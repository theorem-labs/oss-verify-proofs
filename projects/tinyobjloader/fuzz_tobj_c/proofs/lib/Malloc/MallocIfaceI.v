(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "and"; "eq"; "iff"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "ma_s"; "ma_L"; "MA"; "MInv"; "@Corelib.Init.Datatypes"; "bool"; "option"; "true"; "false"; "None"; "nil"; "prod"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "byteview_of"; "mconsts"; "auxv_ok"; "mc_ctx"; "statics_ok"; "vm_ok"; "img_reserved"; "ledger_ok"; "maps_wf"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "VmMaps"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI"; "MInvG"; "MInvI"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter"; "reprO"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "ly_ctx"; "Inv"; "U0"; "WF"; "bounded"; "layout"; "layout_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "astate"; "sptr"; "st_init_done"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier"; "reach_ok"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics State.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import
  MallocModel MallocInv MallocLayout MallocFooter NestTier MallocIface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition MInvG (C : mconsts) (I : astate -> Prop) (A : MA) (rd : word -> option byte) (wok : word -> bool) (vm : VmMaps) : Prop := ltac2:(tb__ "0|2|
S4VA;A1S24S5VA;A1S22S0VI;R2A1S0S21R2A1S0S1S1bS1dR1A1S12VC;A1A3S0S1cR1R2SfVrd;Vwok;A2M0A3S0S14R1R2Vvm;A3S0S13VC;SfVrd;S3Q40A1SaL_;A2M1G0A3S0S1S8S26R2A1SbA3S11VC;R2G1A3F_;S0S16VC;Vvm;A2S0S15VC;Vvm;A2S17Vvm;A1A2A2A2A2A2A2A2A2A2TL;Ts;").

Definition MInvI (C : mconsts) (X : list sptr) (R : option (sptr * Z)) (U : Z -> Z) : ltac2:(tb__ "0|1|
S6S3Q40A1M0S9S3Q8A1A1F_;G0S8F_;S18OFvm;Fwok;Frd;FA;") := ltac2:(tb__ "0|0|
S19VC;S1eVX;VR;VU;A3A2").

Lemma MInv_MInvG : ltac2:(tb__ "0|1|
S10S6S3Q40A1M0S9S3Q8A1A1F_;G0S8F_;S18S2S7R5R4R3R2R1A5S0S19R5S20R4R3R2R1A6S27S4R4A1A1A2A2Fvm;Fwok;Frd;FA;FC;").
Proof. intros. unfold MInv, MInvG. tauto. Qed.

Lemma MInv_MInvI : ltac2:(tb__ "0|1|
S10S6S3Q40A1M0S9S3Q8A1A1F_;G0S8F_;S18S2S7R5R4R3R2R1A5S0S1aR5SdS25A1ScSeS25S1bA2A1S1fR4R3R2R1A8S27S4R4A1A1A2A2Fvm;Fwok;Frd;FA;FC;").
Proof. intros. unfold MInv, MInvI, MInvG, WF. tauto. Qed.

Lemma MInvG_weaken : ltac2:(tb__ "0|2|
S10S24OF_;M0G0S6S3Q40A1M1S9S3Q8A1A1F_;G1S8F_;S18R6S4R4A1A1R6S4R5A1A1F_;S19R8R7R5R4R3R2A6S19R9R7R6R5R4R3A6F_;F_;Fvm;Fwok;Frd;FA;FJ;FI;FC;").
Proof. intros C I J A rd wok vm HIJ (HI & Hrest). split; [apply HIJ; exact HI | exact Hrest]. Qed.

Section Proj.
  Context {C : mconsts} {I : astate -> Prop} {A : MA} {rd : word -> option byte} {wok : word -> bool} {vm : VmMaps}
          (H : MInvG C I A rd wok vm).
  Lemma mig_I : I (ma_s A). Proof using H. exact (proj1 H). Qed.
  Lemma mig_bounded : bounded (ma_s A). Proof using H. exact (proj1 (proj2 H)). Qed.
  Lemma mig_ctx : ltac2:(tb__ "0|0|
S1S1bS1dS5VA;A1A1S12VC;A1A3"). Proof using H. exact (proj1 (proj2 (proj2 H))). Qed.
  Lemma mig_reprO : ltac2:(tb__ "0|0|
S1cS5VA;A1S4VA;A1SfVrd;Vwok;A2A3"). Proof using H. exact (proj1 (proj2 (proj2 (proj2 H)))). Qed.
  Lemma mig_vm : ltac2:(tb__ "0|0|
S14S5VA;A1S4VA;A1Vvm;A3"). Proof using H. exact (proj1 (proj2 (proj2 (proj2 (proj2 H))))). Qed.
  Lemma mig_statics : ltac2:(tb__ "0|0|
S13VC;SfVrd;S3Q40A1SaL_;A2SfVrd;Vwok;A2A3"). Proof using H. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 H)))))). Qed.
  Lemma mig_auxv : ltac2:(tb__ "0|0|
S1S8S26S4VA;A1A1SbA3S11VC;S5VA;A1SfVrd;S3Q40A1SaL_;A2A3F_;"). Proof using H. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H))))))). Qed.
  Lemma mig_ledger : ledger_ok C vm. Proof using H. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H)))))))). Qed.
  Lemma mig_img : img_reserved C vm. Proof using H. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H))))))))). Qed.
  Lemma mig_maps : maps_wf vm. Proof using H. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H))))))))). Qed.
  Lemma mig_layout : ltac2:(tb__ "0|0|
S23S5VA;A1S4VA;A1A2"). Proof using H. exact (proj1 (proj1 mig_reprO)). Qed.
End Proj.
