(** The UBSan main contract with no premise left: codec_main_holds applied to the walk of every callee it names,
    and recursively to theirs. Each premise is the <fn>_holds lemma of lib/U/Prog/<fn>.v; no contract is restated. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U.Prog Require
  LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput
  memset memcpy bcmp strcmp
  check_personality diginet_personality_of diginet_personality_from_name
  text_arg check_text_scribble diginet_scribble_text diginet_scribble_encode
  check_text_seg7 diginet_seg7 owed_seg7 check_text_counter owed_counter_text diginet_counter_text
  check_text_masks diginet_meter_mask diginet_meter_segments diginet_ring_dot diginet_ring_fill
  owe_sysex check_refusal check_range check_bytes
  diginet_fader_encode diginet_button_encode diginet_touch_encode diginet_vpot_encode
  diginet_jog_encode diginet_ring_encode diginet_meter_encode leds_encode
  diginet_strip_leds_encode diginet_counter_leds_encode diginet_counter_encode diginet_sysex_encode.

Theorem codec_main_proved :
  OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U.Prog.LLVMFuzzerTestOneInput_c.codec_main_contract.
Proof.
  exact (LLVMFuzzerTestOneInput.codec_main_holds
    (check_personality.check_personality_holds
       diginet_personality_of.diginet_personality_of_holds
       strcmp.strcmp_holds
       (diginet_personality_from_name.diginet_personality_from_name_holds strcmp.strcmp_holds))
    memset.memset_holds
    memcpy.memcpy_holds
    diginet_personality_of.diginet_personality_of_holds
    (text_arg.text_arg_holds memcpy.memcpy_holds)
    (check_text_scribble.check_text_scribble_holds
       memset.memset_holds
       diginet_scribble_text.diginet_scribble_text_holds
       bcmp.bcmp_holds)
    (check_text_seg7.check_text_seg7_holds diginet_seg7.diginet_seg7_holds owed_seg7.owed_seg7_holds)
    (check_text_counter.check_text_counter_holds
       (owed_counter_text.owed_counter_text_holds owed_seg7.owed_seg7_holds)
       memset.memset_holds
       (diginet_counter_text.diginet_counter_text_holds diginet_seg7.diginet_seg7_holds)
       bcmp.bcmp_holds)
    (owed_counter_text.owed_counter_text_holds owed_seg7.owed_seg7_holds)
    (check_text_masks.check_text_masks_holds
       diginet_meter_mask.diginet_meter_mask_holds
       diginet_meter_segments.diginet_meter_segments_holds
       diginet_ring_dot.diginet_ring_dot_holds
       diginet_ring_fill.diginet_ring_fill_holds)
    (owe_sysex.owe_sysex_holds memcpy.memcpy_holds)
    check_refusal.check_refusal_holds
    (check_range.check_range_holds bcmp.bcmp_holds)
    (check_bytes.check_bytes_holds bcmp.bcmp_holds)
    diginet_fader_encode.diginet_fader_encode_holds
    diginet_button_encode.diginet_button_encode_holds
    diginet_touch_encode.diginet_touch_encode_holds
    diginet_vpot_encode.diginet_vpot_encode_holds
    diginet_jog_encode.diginet_jog_encode_holds
    (diginet_ring_encode.diginet_ring_encode_holds
       (diginet_sysex_encode.diginet_sysex_encode_holds memcpy.memcpy_holds))
    (diginet_meter_encode.diginet_meter_encode_holds
       (diginet_sysex_encode.diginet_sysex_encode_holds memcpy.memcpy_holds))
    (diginet_strip_leds_encode.diginet_strip_leds_encode_holds
       (leds_encode.leds_encode_holds
          (diginet_sysex_encode.diginet_sysex_encode_holds memcpy.memcpy_holds)))
    (diginet_counter_leds_encode.diginet_counter_leds_encode_holds
       (leds_encode.leds_encode_holds
          (diginet_sysex_encode.diginet_sysex_encode_holds memcpy.memcpy_holds)))
    (diginet_scribble_encode.diginet_scribble_encode_holds
       memcpy.memcpy_holds
       (diginet_sysex_encode.diginet_sysex_encode_holds memcpy.memcpy_holds))
    (diginet_counter_encode.diginet_counter_encode_holds
       (diginet_sysex_encode.diginet_sysex_encode_holds memcpy.memcpy_holds))
    (diginet_sysex_encode.diginet_sysex_encode_holds memcpy.memcpy_holds)).
Qed.
