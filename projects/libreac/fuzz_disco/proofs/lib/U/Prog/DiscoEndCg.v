From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import
  memcpy bcmp strlen snprintf reac_hunt_pin reac_hunt_silence_proven reac_hunt_verdict_name reac_hunt_role
  reac_hunt_heard_anything DiscoLinkU.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require LLVMFuzzerTestOneInput_cg uslot_ser_chain.

Definition slot_cg_ok : LLVMFuzzerTestOneInput_cg.LLVMFuzzerTestOneInput_cg_contract :=
  LLVMFuzzerTestOneInput_cg.LLVMFuzzerTestOneInput_cg_holds
    table_init_ok gate_init_ok peer_lock_init_ok hunt_init_ok
    reac_hunt_pin_holds reac_hunt_silence_proven_holds
    table_age_ok check_table_ok
    (uslot_ser_chain.uslot_ser_chain_closed table_json_ok strlen_holds json_scalar_ok jtok_is_ok box_name_ok
       snprintf_stk_holds)
    hunt_step_ok reac_hunt_verdict_name_holds reac_hunt_role_holds reac_hunt_heard_anything_holds
    memcpy_holds find_entry_ok hunt_observe_ok check_sighting_ok
    classify_ok classify_on_segment_ok gate_should_push_ok bcmp_holds table_observe_ok role_of_ok.
