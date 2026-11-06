(** The plain main contract with no premise left: codec_main_holds applied to the walk of every callee it names,
    and recursively to theirs. Each premise is the <fn>_holds lemma of lib/Prog/<fn>.v; no contract is restated.
    codec_plain_rz_proved is lib/Prog/CodecPlainRz.v's codec_plain_rz with its main-contract premise discharged. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.libdiginet.fuzz_codec Require Statements Images.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import
  YK11 YK15 YM05 YM02 YM0b YO0i YO0f YO0g YO0x YO0d YO05 YO0j YO0m YO03 YO09 YO06 YO04 YO0o
  YH00 YH02 YI06 YI14 YI16 YI5b YI5c YL01 YL0g YL0i YL0k YL0s YL0j YN03 YN2b YN33 YP09 DriverSlots.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib Require Import
  ZImage ZTraceSpec AllocSlots AllocRoom ZComplete ZAllocator Contract FrameAPI FrameSlotG
  Agree AgreeTop AgreeZlib AgreeShape.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib Require AgreeCodec.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require
  LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput CodecPlainRz
  memset memcpy bcmp strcmp
  check_personality diginet_personality_of diginet_personality_from_name
  text_arg check_text_scribble diginet_scribble_text diginet_scribble_encode
  check_text_seg7 diginet_seg7 owed_seg7 check_text_counter owed_counter_text diginet_counter_text
  diginet_sysex_encode diginet_jog_encode diginet_counter_encode diginet_touch_encode
  diginet_vpot_encode diginet_strip_leds_encode diginet_fader_encode diginet_button_encode
  diginet_ring_encode diginet_meter_encode diginet_counter_leds_encode
  check_refusal check_range check_bytes check_text_masks
  diginet_meter_mask diginet_meter_segments diginet_ring_dot diginet_ring_fill.
Import ListNotations.
Open Scope Z_scope.
#[local] Existing Instance YK11.fx0.

Theorem codec_main_proved :
  OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog.LLVMFuzzerTestOneInput_c.codec_main_contract.
Proof.
  exact (LLVMFuzzerTestOneInput.codec_main_holds
    memset.memset_holds
    memcpy.memcpy_holds
    (check_personality.check_personality_holds
       diginet_personality_of.diginet_personality_of_holds
       strcmp.strcmp_holds
       (diginet_personality_from_name.diginet_personality_from_name_holds strcmp.strcmp_holds))
    diginet_personality_of.diginet_personality_of_holds
    (text_arg.text_arg_holds memcpy.memcpy_holds)
    (check_text_scribble.check_text_scribble_holds
       memset.memset_holds
       (diginet_scribble_text.diginet_scribble_text_holds memset.memset_holds)
       bcmp.bcmp_holds)
    (diginet_scribble_encode.diginet_scribble_encode_holds
       memcpy.memcpy_holds
       (diginet_sysex_encode.diginet_sysex_encode_holds memcpy.memcpy_holds))
    (check_text_seg7.check_text_seg7_holds diginet_seg7.diginet_seg7_holds owed_seg7.owed_seg7_holds)
    (check_text_counter.check_text_counter_holds
       (owed_counter_text.owed_counter_text_holds owed_seg7.owed_seg7_holds)
       memset.memset_holds
       (diginet_counter_text.diginet_counter_text_holds diginet_seg7.diginet_seg7_holds)
       bcmp.bcmp_holds)
    (owed_counter_text.owed_counter_text_holds owed_seg7.owed_seg7_holds)
    (diginet_sysex_encode.diginet_sysex_encode_holds memcpy.memcpy_holds)
    diginet_jog_encode.diginet_jog_encode_holds
    (diginet_counter_encode.diginet_counter_encode_holds memcpy.memcpy_holds)
    diginet_touch_encode.diginet_touch_encode_holds
    diginet_vpot_encode.diginet_vpot_encode_holds
    diginet_strip_leds_encode.diginet_strip_leds_encode_holds
    diginet_fader_encode.diginet_fader_encode_holds
    diginet_button_encode.diginet_button_encode_holds
    diginet_ring_encode.diginet_ring_encode_holds
    diginet_meter_encode.diginet_meter_encode_holds
    diginet_counter_leds_encode.diginet_counter_leds_encode_holds
    check_refusal.check_refusal_holds
    (check_range.check_range_holds bcmp.bcmp_holds)
    (check_bytes.check_bytes_holds bcmp.bcmp_holds)
    (check_text_masks.check_text_masks_holds
       diginet_meter_mask.diginet_meter_mask_holds
       diginet_meter_segments.diginet_meter_segments_holds
       diginet_ring_dot.diginet_ring_dot_holds
       diginet_ring_fill.diginet_ring_fill_holds)).
Qed.

Corollary codec_plain_rz_proved :
  forall en inp, valid_entry Images.plain en inp -> valid_input inp ->
  rz_run Images.plain Budgets.Standard.lim_source en inp (SPECX (LS:=AgreeCodec.ag_sil_shape) inp).
Proof. exact (CodecPlainRz.codec_plain_rz codec_main_proved). Qed.
