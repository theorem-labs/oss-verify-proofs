(* The A-level contract of fuzz_codec's entry function at image A: codec_lib_contract_x (lib/A/Prog/CPgMainC.v) at
   the image's segments and constants, from the A-level contracts of its 23 callees and the runtime contracts it
   calls. The walk is the segments of lib/A/Prog/codec_amain_inv.v (one file each, codec_amain_<seg>.v), chained
   by amain_of_segments and turned into the contract by amain_contract_of_walk. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0s YK14 YK15 YK18 YP09 YI00 YI04 YI08 YI09 YI16 YN3v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YO09 YE00 YE01 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw0 ACeh ACfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Rt Require Import SetShadowDef.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import
CodecCJ CPgBase CPgEncC CPgChkC CPgMainC CodecRo CodecGlobs CPgWalk CPgWalkRo codec_amain_inv.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require
codec_amain_entry codec_amain_head codec_amain_exit codec_amain_latch
codec_amain_rd0 codec_amain_rd1 codec_amain_rd2 codec_amain_rd3 codec_amain_rd4 codec_amain_rd5 codec_amain_rd6
codec_amain_rd7 codec_amain_rd8 codec_amain_rd9 codec_amain_rd10 codec_amain_rd11 codec_amain_rd12
codec_amain_rd13 codec_amain_rd14 codec_amain_run
codec_amain_enc0 codec_amain_enc1 codec_amain_enc2 codec_amain_enc3 codec_amain_enc4 codec_amain_enc5
codec_amain_enc6 codec_amain_enc7 codec_amain_enc8 codec_amain_enc9 codec_amain_enc10 codec_amain_enc11
codec_amain_oweh codec_amain_owe0 codec_amain_owe1 codec_amain_owe2 codec_amain_owe3 codec_amain_owe4
codec_amain_owe5 codec_amain_owe6 codec_amain_owe7 codec_amain_owe8 codec_amain_owe9 codec_amain_owe10
codec_amain_owe11 codec_amain_chk.
Import ListNotations.
Local Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {ROB : ACeh.ro_tfa_below_ofl}.
Context {LS : lib_shape}.
Variable B : asyms.
Variable MT : ameter_ops.
Variable K : asink_syms.
Variables XM_LIB XN_LIB : Z -> Z.
(* the kit's laws *)
Hypothesis MTL : ameter_laws MT.
Hypothesis MTF : ameter_fs_laws MT.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AIL : asink_img_laws tfibsegs B K.
Hypothesis HXN : forall n, 0 <= XN_LIB n.
Hypothesis LEAF : forall pl fs (Kl : lleaf -> TSet), LIBK pl fs Kl = Kl (LL 0 fs []).
(* the runtime contracts *)
Hypothesis ASM3 : astack_malloc_realizes tfibsegs B 3.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASF : astack_free_law tfibsegs B.
Hypothesis FFL : frame_flag_lawP tfibsegs B.
Hypothesis AMEMSET : aintrin_realizes tfibsegs B OSet 0x51e34.
Hypothesis AMEMCPY : aintrin_realizes tfibsegs B OCpy 0x51998.
Hypothesis ASSF5 : aset_shadow_realizes tfibsegs B AM_set_shadow_f5 0xf5.
(* the start-up facts *)
Hypothesis GM : globs_marked tfibsegs B CODEC_GLOBS.
Hypothesis IV : img_shadow_vis tfibsegs B.
Hypothesis RF : cpw_rows_free B CA_ROSTRS.
(* the 23 callees, at their image-A entries *)
Hypothesis C_check_pers : cdc_check_pers_specX tfibsegs B MT CA_RLO CA_RHI CA_PERS CA_ROSTRS AM_check_pers.
Hypothesis C_pers_of : cdc_pers_of_specX tfibsegs B MT AM_pers_of CA_PERS.
Hypothesis C_text_arg : cdc_text_arg_specX tfibsegs B MT AM_text_arg.
Hypothesis C_check_seg7 : cdc_check_seg7_specX tfibsegs B MT CA_RLO CA_RHI CA_SEG7 CA_GLYPH CA_ROSTRS AM_check_seg7.
Hypothesis C_check_text_counter :
  cdc_check_text_counter_specX tfibsegs B MT CA_RLO CA_RHI CA_SEG7 CA_GLYPH CA_ROSTRS AM_check_text_counter.
Hypothesis C_owed_counter_text :
  cdc_owed_counter_text_specX tfibsegs B MT CA_RLO CA_RHI CA_GLYPH CA_ROSTRS AM_owed_counter_text.
Hypothesis C_check_text_scribble : cdc_check_text_scribble_specX tfibsegs B MT AM_check_text_scribble.
Hypothesis C_check_masks : cdc_check_masks_specX tfibsegs B MT AM_check_masks.
Hypothesis C_check_refusal : cdc_check_refusal_specX tfibsegs B MT AM_check_refusal.
Hypothesis C_check_range : cdc_check_range_specX tfibsegs B MT AM_check_range.
Hypothesis C_check_bytes : cdc_check_bytes_specX tfibsegs B MT AM_check_bytes.
Hypothesis C_fader : cdc_fader_specX tfibsegs B MT AM_fader.
Hypothesis C_button : cdc_button_specX tfibsegs B MT AM_button.
Hypothesis C_touch : cdc_touch_specX tfibsegs B MT AM_touch.
Hypothesis C_vpot : cdc_vpot_specX tfibsegs B MT AM_vpot.
Hypothesis C_jog : cdc_jog_specX tfibsegs B MT AM_jog.
Hypothesis C_sysex : cdc_sysex_specX tfibsegs B MT AM_sysex.
Hypothesis C_ring : cdc_ring_specX tfibsegs B MT AM_ring.
Hypothesis C_meter : cdc_meter_specX tfibsegs B MT AM_meter.
Hypothesis C_sleds : cdc_sleds_specX tfibsegs B MT AM_sleds.
Hypothesis C_cleds : cdc_cleds_specX tfibsegs B MT AM_cleds.
Hypothesis C_scribble : cdc_scribble_specX tfibsegs B MT AM_scribble.
Hypothesis C_counter : cdc_counter_specX tfibsegs B MT AM_counter.

(* each segment theorem at this Section's instance; its own Section hypotheses are among the ones above *)
Ltac seg_by t := eapply t; eassumption.

Theorem codec_amain_holds :
codec_lib_contract_x tfibsegs B MT K XM_LIB XN_LIB CA_RLO CA_RHI A_LLVMF RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK.
Proof using All.
apply (amain_contract_of_walk B MT K XM_LIB XN_LIB MTL AIL HXN LEAF).
apply (amain_of_segments B MT K XM_LIB).
- seg_by codec_amain_entry.seg_entry_holds.
- seg_by codec_amain_head.seg_head_holds.
- intros kind Hk. assert (E : kind = 0 \/ kind = 1 \/ kind = 2 \/ kind = 3 \/ kind = 4 \/ kind = 5 \/ kind = 6 \/
    kind = 7 \/ kind = 8 \/ kind = 9 \/ kind = 10 \/ kind = 11) by lia.
  destruct E as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]].
  + seg_by codec_amain_rd0.seg_rd0_holds.
  + seg_by codec_amain_rd1.seg_rd1_holds.
  + seg_by codec_amain_rd2.seg_rd2_holds.
  + seg_by codec_amain_rd3.seg_rd3_holds.
  + seg_by codec_amain_rd4.seg_rd4_holds.
  + seg_by codec_amain_rd5.seg_rd5_holds.
  + seg_by codec_amain_rd6.seg_rd6_holds.
  + seg_by codec_amain_rd7.seg_rd7_holds.
  + seg_by codec_amain_rd8.seg_rd8_holds.
  + seg_by codec_amain_rd9.seg_rd9_holds.
  + seg_by codec_amain_rd10.seg_rd10_holds.
  + seg_by codec_amain_rd11.seg_rd11_holds.
- seg_by codec_amain_rd12.seg_rd12_holds.
- seg_by codec_amain_rd13.seg_rd13_holds.
- seg_by codec_amain_rd14.seg_rd14_holds.
- seg_by codec_amain_run.seg_run_holds.
- intros kind Hk. assert (E : kind = 0 \/ kind = 1 \/ kind = 2 \/ kind = 3 \/ kind = 4 \/ kind = 5 \/ kind = 6 \/
    kind = 7 \/ kind = 8 \/ kind = 9 \/ kind = 10 \/ kind = 11) by lia.
  destruct E as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]].
  + seg_by codec_amain_enc0.seg_enc0_holds.
  + seg_by codec_amain_enc1.seg_enc1_holds.
  + seg_by codec_amain_enc2.seg_enc2_holds.
  + seg_by codec_amain_enc3.seg_enc3_holds.
  + seg_by codec_amain_enc4.seg_enc4_holds.
  + seg_by codec_amain_enc5.seg_enc5_holds.
  + seg_by codec_amain_enc6.seg_enc6_holds.
  + seg_by codec_amain_enc7.seg_enc7_holds.
  + seg_by codec_amain_enc8.seg_enc8_holds.
  + seg_by codec_amain_enc9.seg_enc9_holds.
  + seg_by codec_amain_enc10.seg_enc10_holds.
  + seg_by codec_amain_enc11.seg_enc11_holds.
- seg_by codec_amain_oweh.seg_oweh_holds.
- intros kind Hk. assert (E : kind = 0 \/ kind = 1 \/ kind = 2 \/ kind = 3 \/ kind = 4 \/ kind = 5 \/ kind = 6 \/
    kind = 7 \/ kind = 8 \/ kind = 9 \/ kind = 10 \/ kind = 11) by lia.
  destruct E as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]].
  + seg_by codec_amain_owe0.seg_owe0_holds.
  + seg_by codec_amain_owe1.seg_owe1_holds.
  + seg_by codec_amain_owe2.seg_owe2_holds.
  + seg_by codec_amain_owe3.seg_owe3_holds.
  + seg_by codec_amain_owe4.seg_owe4_holds.
  + seg_by codec_amain_owe5.seg_owe5_holds.
  + seg_by codec_amain_owe6.seg_owe6_holds.
  + seg_by codec_amain_owe7.seg_owe7_holds.
  + seg_by codec_amain_owe8.seg_owe8_holds.
  + seg_by codec_amain_owe9.seg_owe9_holds.
  + seg_by codec_amain_owe10.seg_owe10_holds.
  + seg_by codec_amain_owe11.seg_owe11_holds.
- seg_by codec_amain_chk.seg_chk_holds.
- seg_by codec_amain_latch.seg_latch_holds.
- seg_by codec_amain_exit.seg_exit_holds.
Qed.
End a.
