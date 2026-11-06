(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Run StackLayout.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import LiaTuning InitMem.
Open Scope Z_scope.
Class runConstT : Type := RunConst {
ATOP : Z;
SECRET : Z;
CAN : word;
ATOP_lo : 0x7fff7f800000 <= ATOP;
ATOP_hi : ATOP <= 0x7FFFFF800000;
ATOP_al16 : ATOP mod 16 = 0;
SECRET_rng : 0 <= SECRET < 2^64
}.
Lemma entry_atop_lo : forall en, valid_sp (en_sp en) -> 0x7fff7f800000 <= entry_atop en.
Proof. intros en (L & H & M). unfold entry_atop, sp_window_lo, stack_max_size in *. Local Ltac2 Set LiaHints.tbl := fun () => "0010=55699908819.4000003S1L".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma entry_atop_hi : forall en, valid_sp (en_sp en) -> entry_atop en <= 0x7FFFFF800000.
Proof. intros en (L & H & M). unfold entry_atop, sp_window_hi, stack_max_size in *. Local Ltac2 Set LiaHints.tbl := fun () => "0010=48936885269.4000003S1H".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma entry_atop_al16 : forall en, valid_sp (en_sp en) -> entry_atop en mod 16 = 0.
Proof. intros en (L & H & M). unfold entry_atop, stack_max_size in *. Z.div_mod_to_equations. Local Ltac2 Set LiaHints.tbl := fun () => "0010>66151427713.1800000<S1M2H02H12H5".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition run_consts_of (en : ExecEntry) (c : word) (V : valid_sp (en_sp en)) : runConstT :=
{| ATOP := entry_atop en; SECRET := entry_secret en; CAN := c;
ATOP_lo := entry_atop_lo en V; ATOP_hi := entry_atop_hi en V; ATOP_al16 := entry_atop_al16 en V;
SECRET_rng := draw_secret_range (en_draw en) |}.
