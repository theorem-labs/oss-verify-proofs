(* fm's plain side, closed: every run of fm.plain from a valid entry on a valid input, at the 16 GiB budget,
   realizes SPECX at ag_shape checksum_shape (cuts allowed). This is the plain realizes that the released
   ubsan_agrees proof builds inside AgreeFrame.ubsan_agrees_of_slots (AgreeTop.plain_rz_of_contracts_R), at the
   concrete instance that Prog/AgreeFm.v uses: LS := ag_shape checksum_shape, G := manifest_G,
   GI := omx_GI src0_msyms, the library contract Prog/AgreeFm.fm_plain_slot_ag and the room fact
   Prog/AgreeTopFm.fm_room. All inputs are released, proved files, used unchanged. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.omx_clap_core.fuzz_manifest Require Statements Images.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
  YK11 YK15 YM05 YM02 YM0b YO0i YO0f YO0g YO0x YO0d YO05 YO0j YO0m YO03 YO09 YO06 YO04 YO0o
  YH00 YH02 YI06 YI14 YI16 YI5b YI5c YL01 YL0g YL0i YL0k YL0s YL0j YN03 YN2b YN33 YP09 DriverSlots.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest Require Import
  lib.ZImage lib.ZTraceSpec lib.AllocSlots lib.AllocRoom lib.ZComplete lib.ZAllocator lib.Contract lib.FrameAPI
  lib.FrameSlotG lib.Agree lib.AgreeTop lib.AgreeZlib lib.AgreeLim lib.AgreeShape lib.AgreeFrame lib.SlotTopG
  lib.FrameProof.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require Import Ledger StatementPlain StatementPlainAg
  ManifestEndAg.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require AgreeFm AgreeTopFm.
Import ListNotations.
Open Scope Z_scope.
#[local] Existing Instance YK11.fx0.

Theorem fm_plain_rz : forall en inp, valid_entry Images.plain en inp -> valid_input inp ->
  rz_run Images.plain Budgets.Standard.lim_source en inp (SPECX (LS:=ag_shape checksum_shape) inp).
Proof.
  intros en inp Hp Hin.
  assert (HROOMp : forall data, @room_calls (ag_shape checksum_shape) (payload_len data) (calls data) SBD_AG)
    by exact AgreeTopFm.fm_room.
  assert (HC : zlib_runtime_contracts_R (ag_shape checksum_shape) (@RI_G (ag_shape checksum_shape)) manifest_G
    frame_RELRO (fun j T m => T = [] /\ omx_GI src0_msyms j m) (fun _ => [])).
  { intros rc. exists (@zlib_API rc). split; [exact zlib_allocator_extra|].
    apply (lib_contract_x_R_all_of_T src0_msyms (@zlib_API rc) (@RI_G (ag_shape checksum_shape)) manifest_G
      frame_RELRO _ (fun _ => []) LIBPC RA_LIB EMPTY LIB_STACK (@RI_G_step (ag_shape checksum_shape) (omx_GI src0_msyms))).
    intros fx j Hj.
    exact (lib_contract_x_T_of_G src0_msyms (@zlib_API rc) manifest_G frame_RELRO (omx_GI src0_msyms) (fun _ => [])
      j LIBPC RA_LIB EMPTY LIB_STACK
      (lib_contract_x_G_of_g src0_msyms (@zlib_API rc) (zlib_tables rc) manifest_G frame_RELRO (omx_GI src0_msyms)
        j LIBPC RA_LIB EMPTY LIB_STACK (AgreeFm.fm_plain_slot_ag rc fx j Hj))). }
  exact (plain_rz_of_contracts_R (ag_shape checksum_shape) (@RI_G (ag_shape checksum_shape)) manifest_G frame_RELRO
    (fun j T m => T = [] /\ omx_GI src0_msyms j m) (fun _ => [])
    (driver_RI_AG (ag_shape checksum_shape) HROOMp) (fun a h => frame_G_src0 a (manifest_G_sub a h)) frame_RELRO_src0
    (G_local_T_of_G src0segs manifest_G (omx_GI src0_msyms) (omx_GI_local src0_msyms))
    (fun mem H => conj eq_refl (omx_GI_img src0_msyms mem ms_segs_rsegs H)) HC en inp Hp Hin).
Qed.
