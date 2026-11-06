From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog.CF Require check_round_trip_st8 check_round_trip_stdefs check_round_trip_sd0 check_round_trip_sd1 check_round_trip_sd2 check_round_trip_sd3 check_round_trip_sd4 check_round_trip_sd5 check_round_trip_sd6 check_round_trip_sd7.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog.CF Require Import CFS ContractCF KindBGlueCF FrameCF.

Lemma st_chain : check_round_trip_st8.St8 -> check_round_trip_stdefs.St0.
Proof.
  intros H.
  exact (check_round_trip_sd0.st0 (check_round_trip_sd1.st1 (check_round_trip_sd2.st2 (check_round_trip_sd3.st3
           (check_round_trip_sd4.st4 (check_round_trip_sd5.st5 (check_round_trip_sd6.st6
              (check_round_trip_sd7.st7 H)))))))).
Qed.
