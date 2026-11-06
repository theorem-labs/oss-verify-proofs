(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/AGif4cgif.v (a working branch ced28ed2383, file sha256 705f79095d39) onto omx-clap-core/fuzz_state's asan-ubsan image (fuzz_state.asan-ubsan, pinned sha256 5ac5ce0954f8; addresses read from its unstripped build b1566a1ca816); module paths changed; its 2 image addresses moved by code-verified function pairs (1 port_addr_check 16f8a030c869 MAPS predictions, each code one re-derived by funcpair.py; 0 code pcs the tool read as sizes, by funcpair.py; 1 the tool cannot place or places wrongly, read out of image B itself); no other numeral changed. *)
(* The cgif_file instance of the image class ImgBaseAGS.AImgS (the secondary interface AGif4.AIfaceS's image facts
   beyond ImgBase.AImg): cgif's shadow offset (AGjm.SHBv), the image addresses of the secondary walk's const zone
   (the image's end YF0x.TFIB_IMG_END and the end of the shadow window, as AGif0cgif.CZONE has them), the depot's write
   zone (AGjm.DZONE), StackDepotPut's entry pc (YFl0.A_StackDepotPut), the grant zones (YF0x.zone3) and the walk's
   frame at Allocate's entry (AGif0cgif.wframe).  A cgif_file consumer of AGif4 does [Require Import AGif2cgif AGif4cgif]
   and instance search fills IM with AImg_cgif and IMS with AImgS_cgif, so each field unfolds to its cgif value by
   delta.  Consumers relocated to another binary declare their own instance in place of this file. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1v YB1q YF0l YF0m YF0x YFl0.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import AGif2cgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import ImgBaseAGS.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require AGjm AGif0cgif.
Open Scope Z_scope.

#[export] Instance AImgS_cgif {fx : YK11.FPState} {rc : YM05.RunCeil} : AImgS := {|
  ims_shb := AGjm.SHBv;
  ims_img_end := 0x5fd000; ims_csh_end := 0x800b3844;
  ims_dzone := AGjm.DZONE;
  ims_depot := A_StackDepotPut;
  ims_zone3 := zone3;
  ims_wframe := AGif0cgif.wframe
|}.
(* Also a canonical structure, as AGif2cgif.AImg_cgif: a tactic that elaborates its term without instance search
   solves [ims_dzone ?IMS = AGjm.DZONE] (and the like) by unification alone. *)
Canonical Structure AImgS_cgif.
