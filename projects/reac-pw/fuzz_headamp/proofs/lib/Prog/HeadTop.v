(** plain_halts of reac-pw/fuzz_headamp, closed: HeadMain.plain_halts_of_main_callees (LLVMFuzzerTestOneInput's walk)
    with the walks of the two parse entries (Prog/reac_headamp_prop_parse_result.v, reac_headamp_prop_parse.v), the eight
    checks (Prog/check_*.v) and the libc leaves strtol (with __intscan, __shlim, __errno_location), strncmp and strcmp.
    rule 24: proves no function by itself (kind: statement text: the top's composition). *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog Require HeadMain reac_headamp_prop_parse_result
  reac_headamp_prop_parse check_no_overrun check_count check_cells_valid check_object check_cells check_keys
  check_refusal check_plain strtol __intscan __shlim __errno_location strncmp strcmp.
From OSSVerify.reac_pw.fuzz_headamp Require Statements.

Theorem plain_halts_holds : Statements.plain_halts.
Proof.
  pose proof (strtol.strtol_holds __shlim.__shlim_holds
                (__intscan.__intscan_holds __errno_location.__errno_location_holds __shlim.__shlim_holds)) as TOL.
  exact (HeadMain.plain_halts_of_main_callees
           (reac_headamp_prop_parse_result.reac_headamp_prop_parse_result_holds TOL strncmp.strncmp_holds
              strcmp.strcmp_holds)
           (reac_headamp_prop_parse.reac_headamp_prop_parse_holds TOL strncmp.strncmp_holds strcmp.strcmp_holds)
           check_no_overrun.check_no_overrun_holds check_count.check_count_holds
           check_cells_valid.check_cells_valid_holds check_object.check_object_holds check_cells.check_cells_holds
           check_keys.check_keys_holds check_refusal.check_refusal_holds check_plain.check_plain_holds).
Qed.
