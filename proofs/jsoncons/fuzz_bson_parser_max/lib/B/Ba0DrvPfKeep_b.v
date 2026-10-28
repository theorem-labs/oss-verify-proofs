(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import AsanAcct.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SpinAlg Hoare AsanAcctShape SymExec2 SymExec2Sound SymRun SymDrive SymDriveX
  HeapIface HeapIfaceA HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import DrvKitA DrvNodesLazyK As0DrvKitA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0DrvEntry_b Ba0Drv_defs_b Ba0DrvLib_b Ba0DrvRead_b Ba0DrvPiece_b Ba0DrvStdio_b Ba0DrvPrintfK_b
  Ba0DrvG_defs_b Ba0DrvC_defs_b Ba0DrvD_defs_b Ba0DrvLibL_b Ba0DrvE_defs_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Import SX2. Import SX2S.

Section PfKeep.
  Variable sp0 : word.
  Hypothesis Hsp : 0x7fff80000000 <= bv_unsigned sp0 <= 2 ^ 47.
  #[local] Notation usp := (bv_unsigned sp0).

  #[using="Hsp"] Lemma regions_pfA : forall vals ebs so j bls,
    let E := Env (vals_ev vals) ebs in
    vals_ev vals 0 = sp0 -> - 2 ^ 22 <= so <= 0 -> 0 <= j <= 500 ->
    (forall i nb, find_nz i bls = Some nb -> hzA sp0 (bv_unsigned (vals_ev vals i)) nb) ->
    regions_ok ASEGS 0 so 3232 bls [] [] IMG_PF_A IMG_RW_A E (fun a => ~ Wpf (usp + so) j a) (fun a => usp + so - 3232 <= a < usp + so).
  Proof.
    intros vals ebs so j bls E P0 Hso Hj Hbl. pose proof Hsp as Hsp'.
    constructor; cbn [ev E]; rewrite ?P0.
    - lia.
    - lia.
    - intros z Hz Hnot. unfold Wpf, SOBUF. lia.
    - intros z Hz. right. lia.
    - intros i nb Hf. destruct (Hbl i nb Hf) as (Z1 & Z2 & Z3). split; [lia|]. intros z Hz. unfold Wpf, SOBUF. lia.
    - intros v b Hf. discriminate.
    - intros i [].
    - intros lo hi Hin. unfold IMG_PF_A in Hin. cbn [In] in Hin.
      repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; (split; [lia|]; split; [lia|]; intros a Ha; unfold Wpf, SOBUF; lia)|]). destruct Hin.
    - intros lo hi Hin. unfold IMG_RW_A in Hin. destruct Hin as [E1|[]]. injection E1 as <- <-. split; [lia|]. split; [lia|].
      intros Mx d m Hd Hm.
      apply (store_ok_window ASEGS Mx (Z_to_bv 64 0x662290) (Z_to_bv 64 d) 65536%nat m 0x662290 0x672290);
        first [exact (wseg_stage) | reflexivity | lia | (rewrite u_small by lia; lia)].
  Qed.
End PfKeep.
