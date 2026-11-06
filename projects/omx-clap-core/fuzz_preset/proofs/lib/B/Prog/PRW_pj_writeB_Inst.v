(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset image B' (#102 asan-ubsan pin d663f82d7f48, unstripped twin c90d4fa54d43), lane
   PjwBPort of a Theorem Labs lane: pj_write AT THE B' INSTANCE.
   rule 24: proves pj_write (image B'; the walk is PRW_pj_writeB.v's pj_write_holds_B, ported from
   lib/A/Prog/PRW_pj_write.v @ f75b9f6e6fa6 (pjw_holds_lc) by relocation: see that file's header).
   pj_write_holds_B_inst: the kit's tpj_write_specX (lib/A/PRH_FnWriter.v d89d3c67b78c :773-850, the cut 7cdbb61b5fa0),
   VERBATIM, at B := YD2l.TfibB, PI := prh_img_B, L := B_prog_listing, PA := PI_prog_B, ci := CfImgB.CfImg_B,
   cp := CfParams_preset, RL := prh_room_live_a8, ARx := ARcf /\ xs_placed_cf over PI_prog_B's segments (the relation
   of every other B' top of this unit: grow_holds_B_inst, check_bounded_alloc_holds_B_inst_xs, write_value_holds_B),
   with every STATIC premise of the walk discharged: LAWS by YGcallcf.AR_laws_x_xs of YG0lawscf.AR_laws_ok_cf,
   segs_low by the class field pa_segs_low, S9_CF by projection, and the image facts by PRW_pj_writeB_Wit.v (vm_compute
   at the instance; AMS by a Theorem Labs lane's lib/AU/PRowSet.v prow_asan_memset_xm_B).
   What stays a premise, each with its owner:
     - the callee texts, the kit's VERBATIM at the B' instance: twrite_value_specX at the entry float state (every depth;
       lane WriteValueB / a Theorem Labs lane), tput_specX (lane PutB) and tfuzz_free_specX (the B' allocator lane) at EVERY
       float state (they run after write_value's return, at the float state it returns at);
     - pjw_ARGCNT, the one ruled argument of pj_write's single fuzz_free call site (the class-24 bound
       tfuzz_free_specX asks for a non-NULL free; a Theorem Labs lane 08:06Z), owner a Theorem Labs lane (counts_of_room_pos_rl /
       counts_of_room_pos_ok), exactly as at A'.
   NAMES: image B's segments are written FULLY QUALIFIED (SEGS_B); pjw_segs_B checks by reflexivity that the walk's
   segments (pa_segs PI_prog_B) ARE image B's. No numeral. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require WriterSpec WriterApp WriterValue ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnAlloc PRH_FnWriter.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require PRW_pj_writeB PRW_pj_writeB_Wit.
(* the instance: Required, not Imported, and cited by qualified name *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YD2l YG0ncf YGcallcf YG0lawscf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require CfImgB.
(* the PLAIN build's sink instance is loaded transitively; it must never fill an ASan sink argument *)
#[global] Remove Hints OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YI5b.src0_sink_head : typeclass_instances.
Import ListNotations.
Open Scope Z_scope.

(* image B's segments, FULLY QUALIFIED *)
#[local] Abbreviation SEGS_B := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Img0.rsegs.

Section i. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Existing Instance CfImgB.CfImg_B.
#[local] Existing Instance CfParamsPreset.CfParams_preset.
#[local] Existing Instance prh_img_B.
#[local] Abbreviation CP := CfParamsPreset.CfParams_preset.
#[local] Abbreviation TB := YD2l.TfibB.
#[local] Abbreviation SEGS := (@pa_segs _ B_prog_listing PI_prog_B).
#[local] Abbreviation RLI := (prh_room_live_a8 (cp := CP)).
#[local] Abbreviation ARcfx := (fun ly S Hp (W : world SEGS) mem md =>
  YG0ncf.ARcf (cp := CP) SEGS TB ly S Hp W mem md /\ YG0ncf.xs_placed_cf ly S).

(* the guard: the walk's SEGS (pa_segs PI_prog_B) IS image B's segments *)
Lemma pjw_segs_B : SEGS = SEGS_B.
Proof. reflexivity. Qed.

(* THE WALK AT THE B' INSTANCE: the kit's tpj_write_specX, verbatim *)
Theorem pj_write_holds_B_inst : forall (SK : YI16.sink_head) (CTX0 : list (list Z)),
  (* the callee texts, the kit's VERBATIM at the B' instance: write_value at the entry float state, every depth *)
  (forall n : nat, twrite_value_specX (RL := RLI) (PI := prh_img_B) (PA := PI_prog_B) TB ARcfx SK CTX0 n) ->
  (* put and fuzz_free at every float state *)
  (forall fx0 : YK11.FPState,
     tput_specX (fx := fx0) (RL := RLI) (PI := prh_img_B) (PA := PI_prog_B) TB ARcfx SK CTX0) ->
  (forall fx0 : YK11.FPState,
     tfuzz_free_specX (fx := fx0) (RL := RLI) (PI := prh_img_B) (PA := PI_prog_B) TB ARcfx SK) ->
  forall n : nat,
  (* pjw_ARGCNT (owner a Theorem Labs lane): the class-24 bound at pj_write's one fuzz_free call site *)
  (forall rp_sm rp_x rp_os rp_H0 ly S Hp (W : world SEGS) regs mem md,
     PRW_pj_writeB.pjw_ARGCNT (RL := RLI) (SK := SK) (PA := PI_prog_B) TB ARcfx (STK_pj_write n)
       rp_sm rp_x rp_os rp_H0 ly S Hp W regs mem md) ->
  tpj_write_specX (RL := RLI) (PI := prh_img_B) (L := B_prog_listing) (PA := PI_prog_B) TB ARcfx SK CTX0 n.
Proof.
intros SK CTX0 HWV HPUT HFREE n HARG.
pose proof (YGcallcf.AR_laws_x_xs (cp := CP) SEGS TB (YG0lawscf.AR_laws_ok_cf (cp := CP) SEGS TB)) as LAWSx.
pose proof (@pa_segs_low _ _ PI_prog_B) as SEGLOW.
assert (S9 : forall ly S Hp (W : world SEGS) mem md, ARcfx ly S Hp W mem md ->
          YG0ncf.ARcf (cp := CP) SEGS TB ly S Hp W mem md)
  by (intros ly S Hp W mem md H; exact (proj1 H)).
pose proof (PRW_pj_writeB_Wit.pjwbw_ams (fx := fx) (rc := rc) ARcfx _ LAWSx) as AMS.
pose proof (PRW_pj_writeB_Wit.pjwbw_hlit (rc := rc) ARcfx _ LAWSx) as HLIT.
pose proof (PRW_pj_writeB_Wit.pjwbw_ent (rc := rc)) as HENT.
pose proof (PRW_pj_writeB_Wit.pjwbw_ret (rc := rc)) as HRET.
pose proof (PRW_pj_writeB_Wit.pjwbw_pstro (rc := rc)) as HPSTRO.
pose proof (PRW_pj_writeB_Wit.pjwbw_pst_ok (rc := rc)) as PSTOK.
pose proof (PRW_pj_writeB_Wit.pjwbw_nl_img (rc := rc)) as HNL.
eapply (PRW_pj_writeB.pj_write_holds_B (fx := fx) (rc := rc) (RL := RLI) (SK := SK) (PA := PI_prog_B) TB ARcfx);
  first [ exact LAWSx | exact SEGLOW | exact HENT | exact AMS | exact HWV | exact HPUT | exact HFREE | exact HRET
        | exact HPSTRO | exact PSTOK | exact HLIT | exact HNL | exact S9 | exact HARG | exact (conj (Z.le_refl _) (Z.le_refl _)) ].
Qed.
End i.

(* the wrong-image check of the rebind brief (rule 7): every PA / L / PI argument names image B' *)
Set Printing Implicit. Unset Printing Notations.
About pj_write_holds_B_inst.
About PRW_pj_writeB.pj_write_holds_B.
Unset Printing Implicit. Set Printing Notations.
Locate SEGS_B.
Locate PI_prog_B.
Locate B_prog_listing.
Locate prh_img_B.
Print Assumptions PRW_pj_writeB.pj_write_holds_B.
Print Assumptions pj_write_holds_B_inst.
(* the elaborated statement of the instance, every implicit shown *)
Set Printing Implicit.
Unset Printing Notations.
Check @pj_write_holds_B_inst.
Unset Printing Implicit.
Set Printing Notations.
