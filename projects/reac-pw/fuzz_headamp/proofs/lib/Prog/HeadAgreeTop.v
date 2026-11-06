(** ubsan_agrees of reac-pw/fuzz_headamp, closed: AgreeHead.ubsan_agrees_of_contracts with, per build, the checking evt
    (headamp_check.headamp_check_holds over the parse and check walks), the plain parse's contract and check_plain's
    contract discharged by their walks.
    rule 24: proves no function by itself (kind: statement text: the top's composition). *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib Require AgreeHead.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog Require headamp_check reac_headamp_prop_parse_result
  reac_headamp_prop_parse check_no_overrun check_count check_cells_valid check_object check_cells check_keys
  check_refusal check_plain strtol __intscan __shlim __errno_location memset strncmp strcmp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog Require headamp_check reac_headamp_prop_parse_result
  reac_headamp_prop_parse check_no_overrun check_count check_cells_valid check_object check_cells check_keys
  check_refusal check_plain strtol __intscan __shlim __errno_location memset strncmp strcmp.
From OSSVerify.reac_pw.fuzz_headamp Require Statements.

Theorem ubsan_agrees_holds : Statements.ubsan_agrees.
Proof.
  pose proof (OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.strtol.strtol_holds OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.__shlim.__shlim_holds
                (OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.__intscan.__intscan_holds OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.__errno_location.__errno_location_holds OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.__shlim.__shlim_holds))
    as PTOL.
  pose proof (OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog.strtol.strtol_holds OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog.__shlim.__shlim_holds
                (OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog.__intscan.__intscan_holds OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog.__errno_location.__errno_location_holds OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog.__shlim.__shlim_holds))
    as UTOL.
  exact (AgreeHead.ubsan_agrees_of_contracts
           (OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.headamp_check.headamp_check_holds OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.memset.memset_holds
              (OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.reac_headamp_prop_parse_result.reac_headamp_prop_parse_result_holds PTOL OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.strncmp.strncmp_holds
                 OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.strcmp.strcmp_holds)
              OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.check_no_overrun.check_no_overrun_holds OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.check_count.check_count_holds
              OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.check_cells_valid.check_cells_valid_holds OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.strncmp.strncmp_holds OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.strcmp.strcmp_holds
              OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.check_object.check_object_holds OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.check_cells.check_cells_holds OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.check_keys.check_keys_holds
              OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.check_refusal.check_refusal_holds)
           (OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.reac_headamp_prop_parse.reac_headamp_prop_parse_holds PTOL OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.strncmp.strncmp_holds OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.strcmp.strcmp_holds)
           OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.check_plain.check_plain_holds
           (OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog.headamp_check.headamp_check_holds OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog.memset.memset_holds
              (OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog.reac_headamp_prop_parse_result.reac_headamp_prop_parse_result_holds UTOL OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog.strncmp.strncmp_holds
                 OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog.strcmp.strcmp_holds)
              OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog.check_no_overrun.check_no_overrun_holds OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog.check_count.check_count_holds
              OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog.check_cells_valid.check_cells_valid_holds OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog.strncmp.strncmp_holds OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog.strcmp.strcmp_holds
              OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog.check_object.check_object_holds OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog.check_cells.check_cells_holds OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog.check_keys.check_keys_holds
              OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog.check_refusal.check_refusal_holds)
           (OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog.reac_headamp_prop_parse.reac_headamp_prop_parse_holds UTOL OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog.strncmp.strncmp_holds OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog.strcmp.strcmp_holds)
           OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog.check_plain.check_plain_holds).
Qed.
