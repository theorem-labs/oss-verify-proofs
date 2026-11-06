From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import
  memset memcpy memcpy_same bcmp memchr strlen snprintf
  memset_c memcpy_c memcpy_same_c bcmp_c memchr_c strlen_c snprintf_c snprintf_stk_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import
  kind_of_link1 reac_ctrl_checksum_verify reac_ports_parse reac_ctrl_parse
  kind_of_link1_c reac_ctrl_checksum_verify_c reac_ports_parse_c reac_ctrl_parse_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import
  reac_disco_gate_init reac_disco_gate_should_push reac_disco_peer_lock_init
  reac_disco_table_init reac_disco_table_observe reac_disco_table_age check_table find_entry check_sighting role_of
  json_scalar jtok_is sb_ch sb_dec reac_box_name reac_frame_clean_len
  reac_hunt_heard_anything reac_hunt_pin reac_hunt_role reac_hunt_silence_proven reac_hunt_verdict_name
  reac_hunt_init reac_rate_snap reac_master_only_cadence_ns reac_rival_kind_of reac_sender_kind reac_arbitrate
  reac_hunt_step classify_core reac_disco_classify reac_disco_classify_on_segment reac_hunt_observe
  reac_disco_table_json.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import
  reac_disco_gate_init_c reac_disco_gate_should_push_c reac_disco_peer_lock_init_c
  reac_disco_table_init_c reac_disco_table_observe_c reac_disco_table_age_c check_table_c find_entry_c check_sighting_c
  role_of_c json_scalar_c jtok_is_c sb_ch_c sb_dec_c reac_box_name_c reac_frame_clean_len_c
  reac_hunt_heard_anything_c reac_hunt_pin_c reac_hunt_role_c reac_hunt_silence_proven_c reac_hunt_verdict_name_c
  reac_hunt_init_c reac_rate_snap_c reac_master_only_cadence_ns_c reac_rival_kind_of_c reac_sender_kind_c
  reac_arbitrate_c reac_hunt_step_c classify_core_c reac_disco_classify_c reac_disco_classify_on_segment_c
  reac_hunt_observe_c reac_disco_table_json_c.

Definition ctrl_parse_ok : reac_ctrl_parse_contract :=
  reac_ctrl_parse_holds memset_holds memcpy_holds bcmp_holds kind_of_link1_holds.
Definition gate_init_ok : reac_disco_gate_init_contract := reac_disco_gate_init_holds memset_holds.
Definition gate_should_push_ok : reac_disco_gate_should_push_contract := reac_disco_gate_should_push_holds bcmp_holds.
Definition peer_lock_init_ok : reac_disco_peer_lock_init_contract := reac_disco_peer_lock_init_holds.
Definition table_init_ok : reac_disco_table_init_contract := reac_disco_table_init_holds memset_holds.
Definition table_observe_ok : reac_disco_table_observe_contract :=
  reac_disco_table_observe_holds bcmp_holds memset_holds.
Definition table_age_ok : reac_disco_table_age_contract := reac_disco_table_age_holds memcpy_holds memcpy_same_holds.
Definition check_table_ok : check_table_contract := check_table_holds bcmp_holds.
Definition find_entry_ok : find_entry_contract := find_entry_holds bcmp_holds.
Definition role_of_ok : role_of_contract := role_of_holds find_entry_ok.
Definition check_sighting_ok : check_sighting_contract := check_sighting_holds bcmp_holds.
Definition json_scalar_ok : json_scalar_contract := json_scalar_holds memchr_holds strlen_holds bcmp_holds.
Definition jtok_is_ok : jtok_is_contract := jtok_is_holds strlen_holds bcmp_holds.
Definition sb_dec_ok : sb_dec_contract := sb_dec_holds sb_ch_holds.
Definition box_name_ok : reac_box_name_contract := reac_box_name_holds sb_dec_ok sb_ch_holds memcpy_holds strlen_holds.
Definition hunt_init_ok : reac_hunt_init_contract :=
  reac_hunt_init_holds memset_holds table_init_ok peer_lock_init_ok memcpy_holds.
Definition cadence_ok : reac_master_only_cadence_ns_contract := reac_master_only_cadence_ns_holds reac_rate_snap_holds.
Definition sender_kind_ok : reac_sender_kind_contract := reac_sender_kind_holds reac_rival_kind_of_holds cadence_ok.
Definition arbitrate_ok : reac_arbitrate_contract :=
  reac_arbitrate_holds memset_holds bcmp_holds memcpy_holds reac_rival_kind_of_holds.
Definition hunt_step_ok : reac_hunt_step_contract :=
  reac_hunt_step_holds table_age_ok arbitrate_ok bcmp_holds sender_kind_ok.
Definition classify_core_ok : classify_core_contract :=
  classify_core_holds ctrl_parse_ok bcmp_holds reac_ctrl_checksum_verify_holds memset_holds reac_ports_parse_holds.
Definition classify_ok : reac_disco_classify_contract := reac_disco_classify_holds classify_core_ok.
Definition classify_on_segment_ok : reac_disco_classify_on_segment_contract :=
  reac_disco_classify_on_segment_holds classify_core_ok.
Definition hunt_observe_ok : reac_hunt_observe_contract :=
  reac_hunt_observe_holds reac_frame_clean_len_holds classify_on_segment_ok table_observe_ok memcpy_holds bcmp_holds.
Definition table_json_ok : reac_disco_table_json_contract :=
  reac_disco_table_json_holds snprintf_holds snprintf_stk_holds box_name_ok.
