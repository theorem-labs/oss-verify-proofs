From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Reusable Require Import YK11 YM05 YO0d YO09 YP09 YL0g YL0i YI14 YI16.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import Mem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require Import Contract.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require Import Img0 FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import LLVMFuzzerTestOneInput_c.
From OSSVerify.libreac.fuzz_disco Require Statements.
Import ListNotations.
Open Scope Z_scope.

Theorem ubsan_halts_of_frame : LLVMFuzzerTestOneInput_contract -> frame_ubsan -> Statements.ubsan_halts.
Proof.
  intros HS (B & API & LS & SH & SK & ra & empty & H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27 & H28 & H29 & H30 & H31 & H32 & Hlast).
  apply (Hlast [] disco_GI).
  - intros a (lo & len & [] & _).
  - intros j m m' _ _. exact I.
  - intros mem _. exact I.
  - intros rc fx j Hj.
    exact (HS B API LS SH SK ra empty H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31 H32 rc fx j Hj).
Qed.
