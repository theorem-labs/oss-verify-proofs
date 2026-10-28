(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.P Require Import Str_tac Sj_num_kit Sj_num_walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface RT_iface2 D_defs D_kit Sj_akit Sj_acps Sj_hkit Sj_num_akit Sj_num_amem
     Pj_defsA Pj_tocharsA_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Record fmI : Type := mkFI {
  fi_p : Z;
  fi_NB : Z;
  fi_sg : Z;
  fi_n : Z;
  fi_e : Z;
  fi_lo : Z;
  fi_ra : word; fi_gp : word;
  fi_s0 : word; fi_s1 : word; fi_s2 : word; fi_s3 : word; fi_s4 : word; fi_s5 : word;
  fi_s6 : word; fi_s7 : word; fi_s8 : word; fi_s9 : word; fi_s10 : word; fi_s11 : word }.

Record fm_ok (J : fmI) : Prop := mkFOK {
  k_sg : 0 <= fi_sg J <= 1;
  k_n : 1 <= fi_n J <= 20;
  k_e : -324 <= fi_e J <= 308;
  k_lo : 0x6e0000 <= fi_lo J;
  k_room : fi_lo J + 80 + 0x10000 <= fi_p J;
  k_ptop : fi_p J + 48 <= 0x800000000000;
  k_nblo : 0x6e0000 <= fi_NB J;
  k_nbhi : fi_NB J + 48 <= fi_lo J }.

Definition fm_saved (J : fmI) : list cell :=
  [C8 (fi_s5 J); C8 (fi_s4 J); C8 (fi_s3 J); C8 (fi_s2 J); C8 (fi_s1 J); C8 (fi_s0 J); C8 (fi_ra J)].

Definition fm_W (J : fmI) : list (Z * Z) := [(fi_p J - 80, fi_p J); (fi_NB J, fi_NB J + 40)].

Definition FINV (J : fmI) (mb m : mem) : Prop :=
  (exists j7 t17, rw_cells bsegs m (fi_p J + -80) [CB 7 j7; CB 17 t17]) /\
  rw_cells bsegs m (fi_p J + -56) (fm_saved J) /\
  (exists nb, u8arr bsegs m (fi_NB J) nb /\ length nb = 40%nat) /\
  mem_inv bsegs m /\ munch (fm_W J) mb m /\ wmono bsegs mb m /\ stk bsegs m (fi_lo J) (fi_p J + -80).

Ltac fi_open H :=
  let j7 := fresh "j7" in let t17 := fresh "t17" in let nb := fresh "nb" in
  destruct H as ((j7 & t17 & LOC) & SAVED & (nb & NA & NL) & MI & MU & WM & ST).
Ltac fi_close :=
  lazymatch goal with
  | |- FINV _ _ _ =>
      split; [do 2 eexists; eassumption|]; split; [eassumption|];
      split; [eexists; split; [eassumption| first [assumption | congruence]]|];
      split; [eassumption|]; split; [eassumption|]; split; eassumption
  end.
Ltac fi_env OK :=
  pose proof OK as OK'; destruct OK' as [Ksg Kn Ke Klo Kroom Kptop Knblo Knbhi].

Definition nb_shzB (J : fmI) (mb : mem) : Prop := forall m', munch (fm_W J) mb m' -> wmono bsegs mb m' -> shz m' (fi_NB J) 40.
