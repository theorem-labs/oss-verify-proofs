(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset image B' (asan-ubsan #102 pin d663f82d7f48, unstripped twin c90d4fa54d43), THE
   THEOREM of the walk of indent (lane IndentB, a Theorem Labs lane), against the kit's text tindent_specX of the batch kit's cut
   7cdbb61b5fa0 (lib/A/PRH_FnWriter.v d89d3c67b78c :504-564), at the instance of record
   (the one lane PutB's put_holds_B is stated at): PA := PI_prog_B, L := B_prog_listing, PI := prh_img_B,
   B := YD2l.TfibB, ARx := ARcfx (ARcf /\ xs_placed_cf = YGcallcf.ARxs), cp := CfParams_preset, ci := CfImg_B,
   RL := prh_room_live_a8; fx, rc and SK stay generic (no premise fixes them).
   rule 24: proves function indent (fuzz_preset, image B'): the walk is IndentB.v, ported from
   a working branch a8d2be84a39d lib/A/Prog/S7a_indent.v (the A' walk on the same cut; relocation by
   alreloc ced0368250cb, then hand fixes); its instance witnesses are IndentB_Wit.v.
   indent_holds_B IS THE TEXT ITSELF: its statement is tindent_specX at the instance, every implicit argument named.
   SECTION HYPOTHESIS of the instance theorem (a callee text, with its owner):
     H_put : tput_specX at the instance, for every CTX0 (the kit's text at the cut, PRH_FnWriter.v d89d3c67b78c :410-499;
             owner lane PutB, a working branch f7d233bfa70: put_holds_B states exactly this).
   put is indent's only callee (bytecmp: the two `jal put` are its only calls). Every other premise of the walk is
   discharged here: LAWS by YGcallcf.AR_laws_x_xs over YG0lawscf.AR_laws_ok_cf; TL by PALibB.exvi_eh_palib; Hent, HLIT
   and HPSTRO by IndentB_Wit.v's s7w_ent_B, s7w_hlit_B and s7w_pstro_B (vm_compute at PI_prog_B).
   Numerals: none. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YK0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YK06 YImgTop YK1g.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PresetRoomPos PresetRun PresetReqAt.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require WriterSpec WriterApp WriterValue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnWriter.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import IndentB IndentB_Wit.
(* the instance and the cited witnesses: Required, not Imported, and cited by qualified name *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YD2l YG0ncf YG0lawscf YGcallcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require CfImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require PALibB.
Import ListNotations.
Open Scope Z_scope.

(* ---- THE INSTANCE THEOREM ---- *)
Section inst. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
#[local] Existing Instance prh_img_B.
#[local] Existing Instance CfParamsPreset.CfParams_preset.
#[local] Existing Instance CfImgB.CfImg_B.
#[local] Existing Instance PRH_Base.prh_room_live_a8.
#[local] Abbreviation PA := (@PI_prog_B rc).
#[local] Abbreviation SEGS := (@pa_segs rc B_prog_listing PA).
#[local] Abbreviation TB := YD2l.TfibB.
#[local] Abbreviation CP := CfParamsPreset.CfParams_preset.
#[local] Abbreviation ARcfx :=
  (fun ly S Hp (W : world SEGS) mem md => YG0ncf.ARcf (cp := CP) SEGS TB ly S Hp W mem md /\ YG0ncf.xs_placed_cf ly S).

(* CALLEE TEXT, owner lane PutB (a working branch f7d233bfa70, put_holds_B): the kit's tput_specX at the cut
   (PRH_FnWriter.v d89d3c67b78c :410-499) at the instance, for every universe closure CTX0 *)
Hypothesis H_put : forall CTX0 : list (list Z),
  tput_specX (fx := fx) (rc := rc) (ci := CfImgB.CfImg_B) (cp := CP) (PI := prh_img_B)
    (RL := @PRH_Base.prh_room_live_a8 CP) (L := B_prog_listing) (PA := PA) TB ARcfx SK CTX0.

(* the allocator laws and the library premise at the instance (the ones lane PutB's PutB_Wit.v cites) *)
Lemma indb_laws : AR_laws_x SEGS TB ARcfx (@cf_head CP).
Proof. exact (YGcallcf.AR_laws_x_xs (cp := CP) SEGS TB (YG0lawscf.AR_laws_ok_cf (cp := CP) SEGS TB)). Qed.
Lemma indb_tl : PALib (L := B_prog_listing) (PI := PA) TB.
Proof. exact PALibB.exvi_eh_palib. Qed.

(* The kit's text tindent_specX (PRH_FnWriter.v d89d3c67b78c :504-564) at the instance, VERBATIM *)
Theorem indent_holds_B : forall CTX0 : list (list Z),
  tindent_specX (fx := fx) (rc := rc) (ci := CfImgB.CfImg_B) (cp := CP) (PI := prh_img_B)
    (RL := @PRH_Base.prh_room_live_a8 CP) (L := B_prog_listing) (PA := PA) TB ARcfx SK CTX0.
Proof.
intros CTX0.
exact (indent_holds (fx := fx) (rc := rc) (ci := CfImgB.CfImg_B) (cp := CP) (RL := @PRH_Base.prh_room_live_a8 CP)
  (SK := SK) (PA := PA) TB ARcfx (@cf_head CP) indb_laws indb_tl (s7w_ent_B (rc := rc)) CTX0 (H_put CTX0)
  (s7w_hlit_B (rc := rc) ARcfx (@cf_head CP) indb_laws) (s7w_pstro_B (rc := rc))).
Qed.
End inst.

Set Printing Implicit. Unset Printing Notations.
Check indent_holds_B.
Unset Printing Implicit. Set Printing Notations.
Print Assumptions indent_holds_B.
