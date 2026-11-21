(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (3 recorded proofs replaced by written proofs (AHI_eq, AHI_laws, AH_laws)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr ITree Nodes Decode.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF ITreeA.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg AProto ABase ARep ALayout AHeapP ARepQ ARepQP ASec ASecFrame
     ADepot_iface F_adepot AFake_iface AFake_arep.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AInstance () := "C47Corelib4Init5Logic6eq_indC59OSSVerify5KrLib4Spec8AsanCtrl4aptrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW8F_adepot<adepot_ifaceC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ASec7ASEC_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW:AFake_arep2AHC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01I59OSSVerify5KrLib5BothW4ARep6aholes00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ5AQUARC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00C59OSSVerify5KrLib5BothW4ARep7ah_quarC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame5munchC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame5wmonoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP>quar_untouchedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP9quar_sameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ASecFrame=asec_hs_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep6ah_secC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP=sec_untouchedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP8sec_sameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW<ADepot_iface9adi_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8ah_depotC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C47Corelib4Init9Datatypes3fstC56Stdlib6ZArith6BinInt1Z2leC47Corelib4Init9Datatypes3sndC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C47Corelib4Init5Logic3notC59OSSVerify5KrLib5BothW5ABase8al_nodesC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC59OSSVerify5KrLib5BothW5ABase8al_storeC1?~~~~~~~~~~~~~~~I47Corelib5Lists7ListDef6Forall00C59OSSVerify5KrLib5BothW;AFake_iface5AFAKEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP>fake_untouchedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW;AFake_iface;afake_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7ah_fakeC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5BothW5ABase6abkind02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5BothW5ABase6ablock01C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC47Corelib4Init5Logic3iffC59OSSVerify5KrLib5BothW;AFake_iface<afake_blocksC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5BothW6AHeapP:ahole_laws01C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW9AInstance3AHIC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6ARepQP;AQUAR_frameC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW5ABase7alayout00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8AsanCtrl6astate00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW4ARep5aconc00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib3Lib5Frame3ivlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4BImg5bsegsC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00I59OSSVerify5KrLib5BothW5ABase6ablock00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW6AHeapP:ahole_laws00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW9AInstance8AHI_lawsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW9AInstance6AHI_eqC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition AHI : aholes := mkAHoles AQUAR ASEC_of (ADEPOT adepot_iface) AFAKE.

Lemma AHI_eq : AHI = AH adepot_iface AQUAR ASEC_of.
Proof. reflexivity. Qed.

Theorem AHI_laws : ahole_laws AHI.
Proof.
  constructor; cbn [AHI ah_quar ah_sec ah_depot ah_fake].
  - exact AQUAR_frame.
  - exact asec_hs_frame.
  - exact (adi_frame adepot_iface).
  - intros L LB m m' W HF MU WM UT. eapply afake_frame; [exact HF| exact MU| exact WM| exact UT].
  - intros L LB LB' m HF EQ. eapply afake_blocks; [exact HF| exact EQ].
Qed.

Corollary AH_laws : ahole_laws (AH adepot_iface AQUAR ASEC_of).
Proof. rewrite <- AHI_eq. exact AHI_laws. Qed.
End CANSEC1.
