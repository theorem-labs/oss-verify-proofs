(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/ct/lib/CtColB/W_set0A.v, with its module paths and module names changed; 44 of its 60 lines of code are new or changed and 129 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_scene/lib/Prog/SceneTac.v, with its module paths changed; 470 of its 484 lines of code are new or changed and 46 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/Prog/codec_main_inv.v; 28 of its 49 lines of code are new or changed and 463 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_cells
  memset_c memcpy_c check_personality_c diginet_personality_of_c text_arg_c check_text_scribble_c
  diginet_scribble_encode_c check_text_seg7_c check_text_counter_c owed_counter_text_c diginet_sysex_encode_c
  diginet_jog_encode_c diginet_counter_encode_c diginet_touch_encode_c diginet_vpot_encode_c
  diginet_strip_leds_encode_c diginet_fader_encode_c diginet_button_encode_c diginet_ring_encode_c
  diginet_meter_encode_c diginet_counter_leds_encode_c check_refusal_c check_range_c check_bytes_c
  check_text_masks_c LLVMFuzzerTestOneInput_c codec_main_inv.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import
  codec_main_entry codec_main_exit codec_main_head
  codec_main_rd0 codec_main_rd1 codec_main_rd2 codec_main_rd3 codec_main_rd4 codec_main_rd5 codec_main_rd6
  codec_main_rd7 codec_main_rd8 codec_main_rd9 codec_main_rd10 codec_main_rd11 codec_main_rd12 codec_main_rd13
  codec_main_rd14 codec_main_enc9 codec_main_enc10 codec_main_oweh
  codec_main_owe0 codec_main_owe1 codec_main_owe2 codec_main_owe3 codec_main_owe4 codec_main_owe5 codec_main_owe6
  codec_main_owe7 codec_main_owe8 codec_main_owe9 codec_main_owe10 codec_main_owe11 codec_main_chk codec_main_latch.
Import ListNotations.
Open Scope Z_scope.

(** LLVMFuzzerTestOneInput (fuzz_codec.c:556-658; 6084 bytes at 0x13228) meets codec_main_contract, given the
    contracts of its direct callees. *)
Theorem codec_main_holds :
  memset_contract -> memcpy_contract -> check_personality_contract -> diginet_personality_of_contract ->
  text_arg_contract -> check_text_scribble_contract -> diginet_scribble_encode_contract ->
  check_text_seg7_contract -> check_text_counter_contract -> owed_counter_text_contract ->
  diginet_sysex_encode_contract -> diginet_jog_encode_contract -> diginet_counter_encode_contract ->
  diginet_touch_encode_contract -> diginet_vpot_encode_contract -> diginet_strip_leds_encode_contract ->
  diginet_fader_encode_contract -> diginet_button_encode_contract -> diginet_ring_encode_contract ->
  diginet_meter_encode_contract -> diginet_counter_leds_encode_contract -> check_refusal_contract ->
  check_range_contract -> check_bytes_contract -> check_text_masks_contract ->
  codec_main_contract.
Proof.
  intros Cmset Cmcpy Cpers Cpof Ctarg Ctscr Cscr Cseg7 Ctcnt Cocnt Csx Cjog Ccnt Ctouch Cvpot Csled
         Cfader Cbutton Cring Cmeter Ccled Cref Crange Cbytes Cmasks.
  unfold codec_main_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m lo data HD HN HMI ST LO SPA DJ HPB HR HDJ.
  set (e := mkEnv ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo a0 data).
  assert (HE : env_ok e) by exact (conj HD (conj HMI (conj ST (conj LO (conj SPA (conj DJ (conj HPB (conj HR HDJ)))))))).
  exact (main_of_segments codec_main_entry codec_main_exit codec_main_head
           codec_main_rd0 codec_main_rd1 codec_main_rd2 codec_main_rd3 codec_main_rd4 codec_main_rd5
           codec_main_rd6 codec_main_rd7 codec_main_rd8 codec_main_rd9 codec_main_rd10 codec_main_rd11
           codec_main_rd12 codec_main_rd13 codec_main_rd14 codec_main_enc9 codec_main_enc10 codec_main_oweh
           codec_main_owe0 codec_main_owe1 codec_main_owe2 codec_main_owe3 codec_main_owe4 codec_main_owe5
           codec_main_owe6 codec_main_owe7 codec_main_owe8 codec_main_owe9 codec_main_owe10 codec_main_owe11
           codec_main_chk codec_main_latch
           Cmset Cmcpy Cpers Cpof Ctarg Ctscr Cscr Cseg7 Ctcnt Cocnt Csx Cjog Ccnt Ctouch Cvpot Csled
           Cfader Cbutton Cring Cmeter Ccled Cref Crange Cbytes Cmasks
           e HE t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 HN).
Qed.
