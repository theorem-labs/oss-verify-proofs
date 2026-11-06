(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec MState Mem Cells Step CellsX.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import StreamSim StoreOk.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require Import AImg.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import HMLib.
Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Ltac2 gd_tbl_AImgW () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.nat"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.bool"; "OSSVerify.KrLib.BB.StreamSim.wseg_ok"; "OSSVerify.KrLib.A.AImg.asegs"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.true"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Stdlib.ZArith.BinInt.Z.pow"; "OSSVerify.KrLib.Lib.Mem.wr_at"; "Corelib.Init.Datatypes.list"; "OSSVerify.KrLib.Lib.Cells.cell"; "OSSVerify.KrLib.Lib.Step.ro_cells"; "OSSVerify.KrLib.Lib.Cells.cells_size"; "OSSVerify.KrLib.Lib.Step.rw_cells"; "ARUN_1.romw_ok"; "OSSVerify.KrLib.Lib.Mem.wa"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.and"; "Corelib.Init.Datatypes.length"; "OSSVerify.KrLib.Lib.Mem.bytes_at"; "Corelib.Init.Datatypes.cons"; "OSSVerify.KrLib.Lib.Cells.C8"; "Corelib.Init.Datatypes.nil"].
   (* [comment removed for export] *)
Section ARUN_1. Context {hAR : arun}.
#[using="Type"] Lemma wr_at_win : ltac2:(CDefT.buildp (gd_tbl_AImgW ()) "PB,$0.PN,$1.Pm,P,(2.&40.)(3.(2.&8.))Pa,$0.Pn,$0.P,(4.$5.(6.$7.(8.&40.R5.)R4.)$9.)P,(:.=R6.)P,(:.(;.R7.(<.R6.))(=.+2.+40.))P,(:.R8.R5.)P,(:.=R5.)P,(:.(;.R7.R6.)(;.R:.(<.R9.)))(>.$7.R9.R8.R7.)")
(* [comment removed for export] *).
Proof.
  intros B N m a n W B0 BN H1 H2 H3. split; [lia|]. split; [lia|]. intros i Hi.
  pose proof (store_ok_window asegs m (Z_to_bv 64 B) (Z_to_bv 64 (a + i)) N 1%nat B (B + Z.of_nat N)
                ltac:(rewrite unsigned_lit by lia; reflexivity) eq_refl BN W ltac:(rewrite unsigned_lit by lia; lia) ltac:(rewrite unsigned_lit by lia; cbn; lia)) as S.
  pose proof (store_ok_wview asegs m (Z_to_bv 64 (a + i)) 1%nat 0%nat S ltac:(lia)) as X.
  rewrite unsigned_lit in X by lia. rewrite Z.add_0_r in X. exact X.
Qed.

#[using="Type"] Lemma ro_rw_win : ltac2:(CDefT.buildp (gd_tbl_AImgW ()) "PB,$0.PN,$1.Pm,P,(2.&40.)(3.(2.&8.))Pa,$0.Pcs,(?.$10.)P,(4.$5.(6.$7.(8.&40.R5.)R4.)$9.)P,(:.=R6.)P,(:.(;.R7.(<.R6.))(=.+2.+40.))P,(11.$7.R6.R5.R4.)P,(:.R9.R6.)P,(:.(;.R7.(<.(12.R6.)))(;.R:.(<.R9.)))(13.$7.R9.R8.R7.)")
(* [comment removed for export] *).
Proof.
  intros B N m a cs W B0 BN RO H1 H2. split; [exact RO|]. eapply wr_at_win; eauto. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma wseg_102000 : wseg_ok asegs (Z_to_bv 64 0x102320) 4096%nat = true. Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rw_instance : ltac2:(CDefT.buildp (gd_tbl_AImgW ()) "Pm,P,(2.&40.)(3.(2.&8.))Pa,$0.Pcs,(?.$10.)P,(11.$7.R3.R2.R1.)P,(:.+102320.R3.)P,(:.(;.R4.(<.(12.R3.)))+103300.)(13.$7.R6.R5.R4.)")
(* [comment removed for export] *).
Proof. intros m a cs RO H1 H2. eapply (ro_rw_win 0x102320 4096%nat); [exact wseg_102000| lia| cbn; lia| exact RO| lia| cbn; lia]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint romw_ok (a : word) (n : nat) : bool :=
  match n with
  | O => true
  | S n' => match memory_read asegs a 1 with Some (_ :: _) => romw_ok (a + 1) n' | _ => false end
  end.

#[using="Type"] Lemma romw_bytes : ltac2:(CDefT.buildp (gd_tbl_AImgW ()) "Pn,$1.Pm,P,(2.&40.)(3.(2.&8.))Pa,$0.P,(4.$5.(14.(15.R1.)R3.)$9.)P,(:.=R2.)P,(:.(;.R3.(<.R5.))(=.+2.+40.))(16.(?.(2.&8.))Lbs,(?.(2.&8.))(17.(4.$1.(18.(2.&8.)R1.)R7.)(19.$7.R6.R5.R1.)))")
(* [comment removed for export] *).
Proof.
  induction n as [|n IH]; intros m a H A0 AN.
  - exists []. split; [reflexivity|]. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
  - cbn [romw_ok] in H. destruct (memory_read asegs (wa a) 1) as [[|b0 bs0]|] eqn:Hr; try discriminate.
    rewrite wa_succ in H. ddestruct (IH m (a + 1) H ltac:(lia) ltac:(lia)) as (bs & L & B).
    set (c := match m (wa a) with Some b => b | None => b0 end).
    exists (c :: bs). split; [cbn; lia|]. split; [lia|]. split; [cbn; lia|].
    intros i Hi. destruct i as [|j].
    + rewrite Z.add_0_r. cbn. unfold mrd. subst c. destruct (m (wa a)); [reflexivity|]. unfold seg_rom. rewrite Hr. reflexivity.
    + cbn [nth_error]. ddestruct B as (_ & _ & BY). rewrite <- (BY j ltac:(cbn in Hi; lia)). f_equal. f_equal. lia.
Qed.

#[using="Type"] Lemma romw_C8 : ltac2:(CDefT.buildp (gd_tbl_AImgW ()) "Pm,P,(2.&40.)(3.(2.&8.))Pa,$0.P,(4.$5.(14.(15.R1.)#8.)$9.)P,(:.=R2.)P,(:.(;.R3.+8.)(=.+2.+40.))(16.(2.&40.)Lw,(2.&40.)(11.$7.R6.R5.(1:.$10.(1;.R1.)(1<.$10.))))")
(* [comment removed for export] *).
Proof.
  intros m a H A0 A8. ddestruct (romw_bytes 8 m a H A0 ltac:(lia)) as (bs & L & B).
  ddestruct (decode_cells_ok [8%nat] bs ltac:(cbn; lia)) as (WF & BY & _).
  exists (le_bytes_to_word (firstn 8 bs)). change [C8 (le_bytes_to_word (firstn 8 bs))] with (decode_cells [8%nat] bs).
  split; [exact WF|]. rewrite BY. exact B.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma canary_cell : forall m, exists w, ro_cells asegs m 0x6596d0 [C8 w].
Proof. intros m. apply romw_C8; [vm_compute; reflexivity| lia| lia]. Qed.

End ARUN_1.
