(* reac-pw/fuzz_headamp: the plain build's entry-function slot at the agreement shape, closed.
   HeadampAsanTop.PLAIN_SLOT_AG is lib/AgreeHead.v plain_slot_ag_of_evts at the plain build's five evt contracts of
   LLVMFuzzerTestOneInput, each discharged by its walk exactly as lib/Prog/HeadAgreeTop.v ubsan_agrees_holds does for
   the plain half of the ubsan agreement: the builder (headamp_build_holds over memset, memcpy, strlen), the two
   copies (headamp_dup_pod_holds, headamp_dup_first_holds over memcpy), the checking evt (headamp_check_holds over
   memset, the parse with its result record, the eight check walks, strncmp, strcmp) and the plain evt
   (headamp_plain_holds over memset, the 8-byte parse wrapper and check_plain); strtol's closure over __shlim,
   __intscan and __errno_location as there.
   It is the plain side of both images' agreement statements: lib/A/AD2o.v (image A) and lib/AU/YD2o.v (image B).
   Proves no function (kind: composition of released walks). *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib Require AgreeHead.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog Require headamp_build headamp_dup_pod headamp_dup_first
  headamp_plain headamp_check reac_headamp_prop_parse_result reac_headamp_prop_parse check_no_overrun check_count
  check_cells_valid check_object check_cells check_keys check_refusal check_plain strtol __intscan __shlim
  __errno_location memset memcpy strlen strncmp strcmp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require HeadampAsanTop.

Lemma headamp_plain_slot_ag_closed : HeadampAsanTop.PLAIN_SLOT_AG.
Proof.
  pose proof (OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.strtol.strtol_holds
                OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.__shlim.__shlim_holds
                (OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.__intscan.__intscan_holds
                   OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.__errno_location.__errno_location_holds
                   OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.__shlim.__shlim_holds))
    as PTOL.
  exact (AgreeHead.plain_slot_ag_of_evts
           (OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.headamp_build.headamp_build_holds
              OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.memset.memset_holds
              OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.memcpy.memcpy_holds
              OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.strlen.strlen_holds)
           (OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.headamp_dup_pod.headamp_dup_pod_holds
              OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.memcpy.memcpy_holds)
           (OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.headamp_check.headamp_check_holds
              OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.memset.memset_holds
              (OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.reac_headamp_prop_parse_result.reac_headamp_prop_parse_result_holds
                 PTOL OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.strncmp.strncmp_holds
                 OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.strcmp.strcmp_holds)
              OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.check_no_overrun.check_no_overrun_holds
              OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.check_count.check_count_holds
              OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.check_cells_valid.check_cells_valid_holds
              OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.strncmp.strncmp_holds
              OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.strcmp.strcmp_holds
              OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.check_object.check_object_holds
              OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.check_cells.check_cells_holds
              OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.check_keys.check_keys_holds
              OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.check_refusal.check_refusal_holds)
           (OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.headamp_dup_first.headamp_dup_first_holds
              OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.memcpy.memcpy_holds)
           (OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.headamp_plain.headamp_plain_holds
              OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.memset.memset_holds
              (OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.reac_headamp_prop_parse.reac_headamp_prop_parse_holds
                 PTOL OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.strncmp.strncmp_holds
                 OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.strcmp.strcmp_holds)
              OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.check_plain.check_plain_holds)).
Qed.

About headamp_plain_slot_ag_closed.
Print Assumptions headamp_plain_slot_ag_closed.
