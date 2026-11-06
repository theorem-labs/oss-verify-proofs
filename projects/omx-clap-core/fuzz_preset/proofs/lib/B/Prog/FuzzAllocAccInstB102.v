(* fuzz_preset image B' (asan-ubsan, #102 pin d663f82d7f48): the INSTANCE corollaries of FuzzAllocAccB102.v's seven
   walks, fuzz_alloc_{live,peak,peak_reset,count,fail,ran_out,ran_out_reset}_holds_B_inst: the texts
   (lib/A/PRH_FnAlloc.v tfuzz_alloc_*_specX, byte-equal at decff67d721f :71-146 and at the kit of record
   tip preset-tree-at-2026-10-29T18-51-23Z.tsv (sha256 c6f0aa3569e3; internal record) :110-185) at the real image-B' record B := YD2l.TfibB, with NO image premise.
   THE RECORD is the one h-rw-man-5's PALib binds at the program listing: lib/B/PALibB.v 5baa19c890f7
   (origin/cold/h-rw-man-5-palib102bj ed438196d17c; on int102), exvi_eh_palib : YC1fP.PALib (PI := PI_prog_B)
   YD2l.TfibB, with exvi_eh_errno (api_env rsegs YD2l.TfibB), exvi_eh_head and exvi_eh_laws. The walks take none of
   these (their laws are AR_laws_ok_cf's, proved inside), and PALib has no field for the walks' one stand-in,
   pal_pst_ok. So pal_pst_ok is DISCHARGED here BY COMPUTATION at that record (acc_pal_pst_ok_B, by
   FuzzAllocAccInst102.v's checker acc_pal_pst_b): every range of prh_pst (prh_img_B) is off every range of
   as_owned_static YD2l.TfibB and off the errno cell [as_errno, as_errno + 4). The four readers (live, peak, count,
   ran_out) had no premise; their corollaries only bind the record.
   No numeral. No ADDRESS literal. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YG00 YG01 YG0f YG0n YI16 YM05 YC4aP YGcfNames YG0ncf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnAlloc CfParamsPreset.
(* the instance: Required, not Imported, and cited by qualified name (PALibB.v's convention) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YD2l.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import FuzzAllocAccInst102.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import FuzzAllocAccB102.
(* stdpp, through the LPS modules, shadows several list lemma names; the lemmas used here are Stdlib's *)
From Stdlib Require Import List.
Import ListNotations.
Local Open Scope Z_scope.

(* pal_pst_ok (FuzzAllocAccB102.v Section T's text) at the real image-B' record *)
Lemma acc_pal_pst_ok_B : forall a, Exists (in_zr a) (@prh_pst prh_img_B) ->
  ~ Exists (in_zr a) (as_owned_static YD2l.TfibB) /\ ~ (as_errno YD2l.TfibB <= a < as_errno YD2l.TfibB + 4).
Proof. apply acc_pal_pst_ok_of_b. vm_compute. reflexivity. Qed.

(* ---- the seven corollaries at B := YD2l.TfibB: the AL rows' instance with the record bound ---- *)
Section I. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg}.
Context {SK : YI16.sink_head}.
#[local] Abbreviation CP := CfParams_preset.
#[local] Abbreviation PA := PI_prog_B.
#[local] Abbreviation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Abbreviation PIB := prh_img_B.
#[local] Abbreviation RLa8 := (prh_room_live_a8 (cp := CP)).
#[local] Abbreviation TB := YD2l.TfibB.
#[local] Abbreviation ARcfx := (fun ly S Hp W mem md => ARcf (cp := CP) SEGS TB ly S Hp W mem md /\ xs_placed_cf ly S).

Corollary fuzz_alloc_live_holds_B_inst :
  tfuzz_alloc_live_specX (cp := CP) (PI := PIB) (RL := RLa8) (L := B_prog_listing) (PA := PA) TB ARcfx SK.
Proof. exact (fuzz_alloc_live_holds_B TB). Qed.

Corollary fuzz_alloc_peak_holds_B_inst :
  tfuzz_alloc_peak_specX (cp := CP) (PI := PIB) (RL := RLa8) (L := B_prog_listing) (PA := PA) TB ARcfx SK.
Proof. exact (fuzz_alloc_peak_holds_B TB). Qed.

Corollary fuzz_alloc_peak_reset_holds_B_inst :
  tfuzz_alloc_peak_reset_specX (cp := CP) (PI := PIB) (RL := RLa8) (L := B_prog_listing) (PA := PA) TB ARcfx SK.
Proof. exact (fuzz_alloc_peak_reset_holds_B TB acc_pal_pst_ok_B). Qed.

Corollary fuzz_alloc_count_holds_B_inst :
  tfuzz_alloc_count_specX (cp := CP) (PI := PIB) (RL := RLa8) (L := B_prog_listing) (PA := PA) TB ARcfx SK.
Proof. exact (fuzz_alloc_count_holds_B TB). Qed.

Corollary fuzz_alloc_fail_holds_B_inst :
  tfuzz_alloc_fail_specX (cp := CP) (PI := PIB) (RL := RLa8) (L := B_prog_listing) (PA := PA) TB ARcfx SK.
Proof. exact (fuzz_alloc_fail_holds_B TB acc_pal_pst_ok_B). Qed.

Corollary fuzz_alloc_ran_out_holds_B_inst :
  tfuzz_alloc_ran_out_specX (cp := CP) (PI := PIB) (RL := RLa8) (L := B_prog_listing) (PA := PA) TB ARcfx SK.
Proof. exact (fuzz_alloc_ran_out_holds_B TB). Qed.

Corollary fuzz_alloc_ran_out_reset_holds_B_inst :
  tfuzz_alloc_ran_out_reset_specX (cp := CP) (PI := PIB) (RL := RLa8) (L := B_prog_listing) (PA := PA) TB ARcfx SK.
Proof. exact (fuzz_alloc_ran_out_reset_holds_B TB acc_pal_pst_ok_B). Qed.
End I.
