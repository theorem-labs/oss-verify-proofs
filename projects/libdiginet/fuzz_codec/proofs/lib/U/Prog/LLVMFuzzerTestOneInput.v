From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U.Prog Require Import LLVMFuzzerTestOneInput_c
  memset_c memcpy_c diginet_personality_of_c check_personality_c check_refusal_c check_range_c
  check_bytes_c check_text_masks_c check_text_scribble_c check_text_seg7_c check_text_counter_c
  owed_counter_text_c text_arg_c owe_sysex_c diginet_fader_encode_c diginet_button_encode_c
  diginet_touch_encode_c diginet_vpot_encode_c diginet_jog_encode_c diginet_ring_encode_c
  diginet_meter_encode_c diginet_strip_leds_encode_c diginet_counter_leds_encode_c
  diginet_scribble_encode_c diginet_counter_encode_c diginet_sysex_encode_c
  codec_main_inv codec_main_compose
  codec_main_exit codec_main_entry codec_main_head
  codec_main_rd0 codec_main_rd1 codec_main_rd3 codec_main_rd5 codec_main_rd6 codec_main_rd8
  codec_main_rd9 codec_main_rd11 codec_main_rd12 codec_main_rd13 codec_main_rd14
  codec_main_run codec_main_owehd
  codec_main_owe0 codec_main_owe5 codec_main_owe6 codec_main_owe7 codec_main_owe9
  codec_main_owe10 codec_main_owe11 codec_main_chk.

(** LLVMFuzzerTestOneInput of fuzz_codec.c:556-658 in the UBSan image (0x132b8, 6404 bytes, frame
    0x1a0) against U/Prog/LLVMFuzzerTestOneInput_c.v, with the contract of each direct callee as a
    premise. The walk is cut into 25 segments, each stated in codec_main_inv.v and proved in its own
    codec_main_<segment>.v; codec_main_compose.v chains them (the loop by induction on 256 - ops,
    then the entry). *)
Theorem codec_main_holds :
  check_personality_contract -> memset_contract -> memcpy_contract ->
  diginet_personality_of_contract -> text_arg_contract -> check_text_scribble_contract ->
  check_text_seg7_contract -> check_text_counter_contract -> owed_counter_text_contract ->
  check_text_masks_contract -> owe_sysex_contract ->
  check_refusal_contract -> check_range_contract -> check_bytes_contract ->
  diginet_fader_encode_contract -> diginet_button_encode_contract ->
  diginet_touch_encode_contract -> diginet_vpot_encode_contract ->
  diginet_jog_encode_contract -> diginet_ring_encode_contract ->
  diginet_meter_encode_contract -> diginet_strip_leds_encode_contract ->
  diginet_counter_leds_encode_contract -> diginet_scribble_encode_contract ->
  diginet_counter_encode_contract -> diginet_sysex_encode_contract ->
  codec_main_contract.
Proof.
  exact (codec_main_of_segments codec_main_exit codec_main_latch codec_main_entry codec_main_head
           codec_main_rd0 codec_main_rd1 codec_main_rd3 codec_main_rd5 codec_main_rd6 codec_main_rd8
           codec_main_rd9 codec_main_rd11 codec_main_rd12 codec_main_rd13 codec_main_rd14
           codec_main_run codec_main_owehd
           codec_main_owe0 codec_main_owe5 codec_main_owe6 codec_main_owe7 codec_main_owe9
           codec_main_owe10 codec_main_owe11 codec_main_chk).
Qed.
