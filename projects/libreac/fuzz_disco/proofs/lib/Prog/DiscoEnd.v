From OSSVerify.libreac.fuzz_disco Require Statements.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require FrameAPI FrameProof.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import
  memcpy bcmp strlen snprintf reac_hunt_pin reac_hunt_silence_proven reac_hunt_verdict_name reac_hunt_role
  reac_hunt_heard_anything DiscoLink.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput Statement.

Definition slot_ok : LLVMFuzzerTestOneInput_c.LLVMFuzzerTestOneInput_contract :=
  LLVMFuzzerTestOneInput.LLVMFuzzerTestOneInput_holds
    table_init_ok gate_init_ok peer_lock_init_ok hunt_init_ok
    reac_hunt_pin_holds reac_hunt_silence_proven_holds
    table_age_ok check_table_ok
    table_json_ok strlen_holds json_scalar_ok jtok_is_ok box_name_ok snprintf_stk_holds
    hunt_step_ok reac_hunt_verdict_name_holds reac_hunt_role_holds reac_hunt_heard_anything_holds
    memcpy_holds find_entry_ok hunt_observe_ok check_sighting_ok
    classify_ok classify_on_segment_ok gate_should_push_ok bcmp_holds table_observe_ok.

Theorem plain_halts_holds : OSSVerify.libreac.fuzz_disco.Statements.plain_halts.
Proof. exact (Statement.plain_halts_of_frame slot_ok FrameProof.frame_plain_holds). Qed.
