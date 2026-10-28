From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree HufWalkKit2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXMem KXTac KXGo KXPost KXFoot KXGoF KXChk KXGoM KXCell.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg AF_huf_w4s3b AF_huf_w4s34k AF_huf_w4s34k2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Notation amem := (word -> option byte).

Ltac w4br6 b :=
  lazymatch goal with
  | |- branch_taken BC_EQ (edenot ?E (EAlu ALU_XOR (ELit 1) (EAlu ALU_SLTU
         (EAlu ALU_XOR ?P (EAluw ALU_SRL ?X (ELit 3))) (ELit 1)))) (edenot ?E (ELit 0)) = false =>
      apply (w4_br_nzk E P (EAluw ALU_SRL X (ELit 3)));
      rewrite (w4_srlw3 E X b); [ | w4ez; first [reflexivity | f_equal; lia] | lia ];
      w4uzm
  end.

Lemma w4s34_srlw3e : forall E e x, edenot E e = Z_to_bv 64 x -> 0 <= x < 2^31 ->
  edenot E (EAluw ALU_SRL e (ELit 3)) = Z_to_bv 64 (x / 8).
Proof.
  intros E e x He Hx.
  rewrite <- (Z_to_bv_bv_unsigned (edenot E (EAluw ALU_SRL e (ELit 3)))).
  rewrite (w4_srlw3 E e x He Hx). reflexivity.
Qed.

Ltac w4s34_fix_srlw3 x :=
  repeat match goal with |- context [edenot ?E (EAluw ALU_SRL ?e (ELit 3))] =>
    rewrite (w4s34_srlw3e E e x); [| w4ez; first [reflexivity | f_equal; lia] | lia] end.
