(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset image B' (#102 asan-ubsan pin d663f82d, unstripped twin c90d4fa54d43):
   write_value PROVED against the text twrite_value_specX of the draft's texts of record
   (lib/A/PRH_FnWriter.v, lib/A/PRH_Base.v), for every depth n and every
   float state fx:
   - the induction WriteValueB_Top.wv_text_all, with the container walk's three lemmas bound (WriteValueB_Cont.wv_cont,
     WriteValueB_Iter.wv_loop, WriteValueB_Close.wv_close);
   - write_value_holds_B: AT THE B' INSTANCE (PI_prog_B, B := YD2l.TfibB, ARx := ARcf /\ xs_placed_cf, cp :=
     CfParams_preset, ci := CfImg_B, RL := prh_room_live_a8), every image fact discharged by WriteValueB_Wit (vm_compute
     / citation) and strlen by a Theorem Labs lane's proved row (WriteValueB_Wit.wvw_strlen). Its ONLY premises are the
     callee texts, VERBATIM at every float state: put (tput_specX, put's lane), put_string (tput_string_specX, put_string's
     lane), indent (tindent_specX, the indent lane). The former premise SRC-CEIL (a live block's
     `p + req_size n + 8 <= alloc_ceiling`) is AR_laws_x's 24th field alx_blocks_ceil8 in the draft, so the walk takes it
     from LAWS (WriteValueB_Wit.wvw_laws) and the top no longer states it.
   No numeral of the image is typed here. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YK06 YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomPre.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require WriterSpec WriterApp WriterValue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnWriter.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import WriteValueB_Model WriteValueB_Base WriteValueB_Call
  WriteValueB_Leaf WriteValueB_Defs.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallMxmn.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG0ncf YG0lawscf YGcallcf YD2l.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require CfImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require WriteValueB_Base WriteValueB_Top
  WriteValueB_Cont WriteValueB_Iter WriteValueB_Close WriteValueB_Wit.


Section inst. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg}.
#[local] Existing Instance CfImgB.CfImg_B.
#[local] Existing Instance CfParamsPreset.CfParams_preset.
#[local] Existing Instance prh_img_B.
#[local] Abbreviation CP := CfParamsPreset.CfParams_preset.
#[local] Abbreviation TB := YD2l.TfibB.
#[local] Abbreviation SEGS := (@pa_segs _ B_prog_listing PI_prog_B).
#[local] Abbreviation RL8 := (prh_room_live_a8 (cp := CfParamsPreset.CfParams_preset)).
#[local] Abbreviation ARcfx := (fun ly S Hp (W : world SEGS) mem md =>
  YG0ncf.ARcf (cp := CP) SEGS TB ly S Hp W mem md /\ YG0ncf.xs_placed_cf ly S).

(* write_value at the B' instance, at the entry float state fx, every depth n *)
Theorem write_value_holds_B : forall (SK : YI16.sink_head) (CTX0 : list (list Z)),
  (* callee texts, VERBATIM at every float state: put (put's lane), put_string (put_string's lane), indent (the indent lane) *)
  (forall fx' : YK11.FPState,
     tput_specX (fx := fx') (RL := RL8) (PI := prh_img_B) (PA := PI_prog_B) TB ARcfx SK CTX0) ->
  (forall fx' : YK11.FPState,
     tput_string_specX (fx := fx') (RL := RL8) (PI := prh_img_B) (PA := PI_prog_B) TB ARcfx SK CTX0) ->
  (forall fx' : YK11.FPState,
     tindent_specX (fx := fx') (RL := RL8) (PI := prh_img_B) (PA := PI_prog_B) TB ARcfx SK CTX0) ->
  forall n : nat,
  twrite_value_specX (fx := fx) (RL := RL8) (PI := prh_img_B) (PA := PI_prog_B) TB ARcfx SK CTX0 n.
Proof.
intros SK CTX0 PUT PUTSTR INDENT n.
exact (@WriteValueB_Top.wv_text_all rc CfImgB.CfImg_B CP RL8 SK PI_prog_B TB ARcfx WriteValueB_Wit.wvw_laws WriteValueB_Wit.wvw_tl WriteValueB_Wit.wvw_hent WriteValueB_Wit.wvw_hobj
    WriteValueB_Wit.wvw_hjt WriteValueB_Wit.wvw_hlit WriteValueB_Wit.wvw_hpstro CTX0 PUT PUTSTR INDENT WriteValueB_Wit.wvw_hw
  (fun fx' => @WriteValueB_Wit.wvw_strlen fx' rc)
  (fun fx' => @WriteValueB_Cont.wv_cont fx' rc CfImgB.CfImg_B CP RL8 SK PI_prog_B TB ARcfx WriteValueB_Wit.wvw_laws WriteValueB_Wit.wvw_tl WriteValueB_Wit.wvw_hent WriteValueB_Wit.wvw_hobj
    WriteValueB_Wit.wvw_hjt WriteValueB_Wit.wvw_hlit WriteValueB_Wit.wvw_hpstro CTX0 PUT PUTSTR INDENT WriteValueB_Wit.wvw_hw)
  (@WriteValueB_Iter.wv_loop fx rc CfImgB.CfImg_B CP RL8 SK PI_prog_B TB ARcfx WriteValueB_Wit.wvw_laws WriteValueB_Wit.wvw_tl WriteValueB_Wit.wvw_hent WriteValueB_Wit.wvw_hobj
    WriteValueB_Wit.wvw_hjt WriteValueB_Wit.wvw_hlit WriteValueB_Wit.wvw_hpstro CTX0 PUT PUTSTR INDENT WriteValueB_Wit.wvw_hw)
  (@WriteValueB_Close.wv_close fx rc CfImgB.CfImg_B CP RL8 SK PI_prog_B TB ARcfx WriteValueB_Wit.wvw_laws WriteValueB_Wit.wvw_tl WriteValueB_Wit.wvw_hent WriteValueB_Wit.wvw_hobj
    WriteValueB_Wit.wvw_hjt WriteValueB_Wit.wvw_hlit WriteValueB_Wit.wvw_hpstro CTX0 PUT PUTSTR INDENT WriteValueB_Wit.wvw_hw)
  n fx).
Qed.
End inst.

(* THE STATEMENT, implicit arguments shown (the class position holds the entry fx) *)
Set Printing Implicit. Unset Printing Notations.
About write_value_holds_B.
Check write_value_holds_B.
Unset Printing Implicit. Set Printing Notations.
Locate write_value_holds_B. Print Assumptions write_value_holds_B.
