(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatExec CatSim SeqExec StoreOk SymExec3 SymExec3Sound SymRun3.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Import SymExecA U1ExitKn.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations. Open Scope bv_scope. Import SX2. Import SXA.
Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition EXIT : Z := 0xd1e54.
Definition EXIT_ECALL : Z := 0xd1b64.
Definition EXIT_STACK : Z := 1024.

Definition sr_exit : list expr :=
  [ELit 0; EVar 4; EVar 0; EVar 6; ELit 0x102418; EVar 8; EVar 9; EVar 10;
   EVar 11; EVar 12; EVar 2; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18;
   EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26;
   EVar 27; EVar 28; EVar 29; EVar 30; EVar 31; EVar 32; EVar 33; EVar 34].

Definition kn_exit_common0 : list kentry :=
  [ KRange (EVar 0) 0x100010000 0x800000000000; KAlign (EVar 0) 16;
    KWr (SA (EVar 0) (- EXIT_STACK)) (ELit EXIT_STACK);
    KWr (SA (ELit 0) 0xef000) (ELit 0x35000);
    KWord (SA (ELit 0) 0x102370) 4 (EVar 1); KRange (EVar 1) 1 4194303;
    KWord (SA (ELit 0) 0x1023e8) 8 (ELit 0x1226e0);

    KImg 0x10000 0xef000; KImg 0xefe40 0xeff08; KImg 0xf0248 0xf0249;
    KImg 0x122460 0x122468; KImg 0x122478 0x122480; KImg 0x122680 0x122684; KImg 0x122be8 0x122bf0;
    KWord (SA (ELit 0) 0x1226ab) 1 (ELit 0)     ].

Definition exit_clear_common : list (Z * Z) :=
  [(0x10000, 0xef000); (0xefe40, 0xeff08); (0xf0248, 0xf0249); (0x122460, 0x122468); (0x122478, 0x122480);
   (0x122680, 0x122684); (0x122be8, 0x122bf0)]%Z.

Definition kn_u_extra : list kentry :=
  [ KWord (SA (ELit 0) 0xeff08) 4 (ELit 5); KWord (SA (ELit 0) 0xeff28) 8 (ELit 0);
    KWord (SA (ELit 0) 0xeff60) 8 (ELit 0x122bf8); KWord (SA (ELit 0) 0xeff68) 8 (ELit 0);
    KWord (SA (ELit 0) 0xeff90) 4 (ELit 0xffffffff);
    KImg 0xeff94 0xf01d8 ].
Definition kn_exit_u : list kentry := kn_exit_common0 ++ kn_cxx_exit ++ kn_u_extra.
Definition exit_clear_u : list (Z * Z) := [(0xeff94, 0xf01d8)]%Z.

Definition cert_u :=
  Eval vm_compute in sym_execA SEGS 3000 true [] (SCR [] [] []) (SS EXIT sr_exit [] kn_exit_u 40) [].
Definition cert_u_pc : Z := Eval vm_compute in s_pc (fst (fst cert_u)).
Definition cert_u_scs : list sidecond := Eval vm_compute in snd (fst cert_u).
Definition cert_u_sr : list expr := Eval vm_compute in s_regs (fst (fst cert_u)).

Lemma cert_u_pc_ok : cert_u_pc = EXIT_ECALL.
Proof. vm_compute. reflexivity. Qed.
Lemma cert_u_scs_nil : cert_u_scs = [].
Proof. vm_compute. reflexivity. Qed.

Lemma cert_u_eq :
  sym_execA SEGS 3000 true [] (SCR [] [] []) (SS EXIT sr_exit [] kn_exit_u 40) [] = cert_u.
Proof. vm_compute. reflexivity. Qed.

Definition kn_u1_extra : list kentry :=
  [ KWord (SA (ELit 0) 0xeff08) 4 (ELit 5); KWord (SA (ELit 0) 0xeff10) 8 (ELit 0); KWord (SA (ELit 0) 0xeff18) 8 (ELit 0);
    KWord (SA (ELit 0) 0xeff28) 8 (ELit 0x122bf8); KWord (SA (ELit 0) 0xeff30) 8 (ELit 0x122bf8); KWord (SA (ELit 0) 0xeff40) 8 (ELit 0x122bf8);
    KWord (SA (ELit 0) 0xeff90) 4 (ELit 0xffffffff);
    KImg 0xeff60 0xeff90; KImg 0xeff94 0xf01d8 ].
Definition kn_exit_u1 : list kentry := kn_exit_common0 ++ kn_cxx_exit ++ kn_u1_extra.
Definition exit_clear_u1 : list (Z * Z) := [(0xeff60, 0xeff90); (0xeff94, 0xf01d8)]%Z.

Definition cert_u1 :=
  Eval vm_compute in sym_execA SEGS 3000 true [] (SCR [] [] []) (SS EXIT sr_exit [] kn_exit_u1 40) [].
Definition cert_u1_pc : Z := Eval vm_compute in s_pc (fst (fst cert_u1)).
Definition cert_u1_scs : list sidecond := Eval vm_compute in snd (fst cert_u1).
Definition cert_u1_sr : list expr := Eval vm_compute in s_regs (fst (fst cert_u1)).

Lemma cert_u1_pc_ok : cert_u1_pc = EXIT_ECALL.
Proof. vm_compute. reflexivity. Qed.
Lemma cert_u1_scs_nil : cert_u1_scs = [].
Proof. vm_compute. reflexivity. Qed.

Lemma cert_u1_eq :
  sym_execA SEGS 3000 true [] (SCR [] [] []) (SS EXIT sr_exit [] kn_exit_u1 40) [] = cert_u1.
Proof. vm_compute. reflexivity. Qed.

Definition kn_t0_extra : list kentry :=
  [ KImg 0xeff08 0xf00e8;
    KWord (SA (ELit 0) 0xf00e8) 4 (ELit 5); KWord (SA (ELit 0) 0xf00f0) 8 (ELit 0); KWord (SA (ELit 0) 0xf00f8) 8 (ELit 0);
    KWord (SA (ELit 0) 0xf0108) 8 (ELit 0x123408); KWord (SA (ELit 0) 0xf0110) 8 (ELit 0x123008);
    KWord (SA (ELit 0) 0xf0120) 8 (ELit 0x123008); KWord (SA (ELit 0) 0xf0130) 8 (ELit 0xd70d4);
    KWord (SA (ELit 0) 0xf0170) 4 (ELit 0xffffffff); KWord (SA (ELit 0) 0xf0178) 4 (ELit 0xffffffff);
    KImg 0xf00ec 0xf00f0; KImg 0xf0100 0xf0108; KImg 0xf0118 0xf0120; KImg 0xf0128 0xf0130;
    KImg 0xf0138 0xf0170; KImg 0xf0174 0xf0178; KImg 0xf017c 0xf01d8 ].
Definition kn_exit_t0 : list kentry := kn_exit_common0 ++ kn_cxx_exit_t ++ kn_t0_extra.
Definition exit_clear_t0 : list (Z * Z) :=
  [(0xeff08, 0xf00e8); (0xf00ec, 0xf00f0); (0xf0100, 0xf0108); (0xf0118, 0xf0120); (0xf0128, 0xf0130);
   (0xf0138, 0xf0170); (0xf0174, 0xf0178); (0xf017c, 0xf01d8)]%Z.

Definition cert_t0 :=
  Eval vm_compute in sym_execA SEGS 3000 true [] (SCR [] [] []) (SS EXIT sr_exit [] kn_exit_t0 40) [].
Definition cert_t0_pc : Z := Eval vm_compute in s_pc (fst (fst cert_t0)).
Definition cert_t0_scs : list sidecond := Eval vm_compute in snd (fst cert_t0).
Definition cert_t0_sr : list expr := Eval vm_compute in s_regs (fst (fst cert_t0)).

Lemma cert_t0_pc_ok : cert_t0_pc = EXIT_ECALL.
Proof. vm_compute. reflexivity. Qed.
Lemma cert_t0_scs_nil : cert_t0_scs = [].
Proof. vm_compute. reflexivity. Qed.

Lemma cert_t0_eq :
  sym_execA SEGS 3000 true [] (SCR [] [] []) (SS EXIT sr_exit [] kn_exit_t0 40) [] = cert_t0.
Proof. vm_compute. reflexivity. Qed.

