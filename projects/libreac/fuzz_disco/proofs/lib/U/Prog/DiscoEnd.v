From OSSVerify.libreac.fuzz_disco Require Statements.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require FrameAPI FrameProof.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import
  memcpy bcmp strlen snprintf reac_hunt_pin reac_hunt_silence_proven reac_hunt_verdict_name reac_hunt_role
  reac_hunt_heard_anything DiscoLinkU.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput Statement
  uslot_ser_chain.

Definition slot_ok : OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog.LLVMFuzzerTestOneInput_c.LLVMFuzzerTestOneInput_contract :=
  OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog.LLVMFuzzerTestOneInput.LLVMFuzzerTestOneInput_holds
    table_init_ok gate_init_ok peer_lock_init_ok hunt_init_ok
    reac_hunt_pin_holds reac_hunt_silence_proven_holds
    table_age_ok check_table_ok
    (uslot_ser_chain.uslot_ser_chain_closed table_json_ok strlen_holds json_scalar_ok jtok_is_ok box_name_ok
       snprintf_stk_holds)
    hunt_step_ok reac_hunt_verdict_name_holds reac_hunt_role_holds reac_hunt_heard_anything_holds
    memcpy_holds find_entry_ok hunt_observe_ok check_sighting_ok
    classify_ok classify_on_segment_ok gate_should_push_ok bcmp_holds table_observe_ok role_of_ok.

Theorem ubsan_halts_holds : OSSVerify.libreac.fuzz_disco.Statements.ubsan_halts.
Proof.
  exact (OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog.Statement.ubsan_halts_of_frame slot_ok
    OSSVerify.Proofs.libreac.fuzz_disco.lib.U.FrameProof.frame_ubsan_holds).
Qed.
