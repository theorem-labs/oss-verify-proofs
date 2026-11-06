(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_ctrl_stamp_headamp on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACam.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACbf.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACf6.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v, with its module paths and module names changed; 481 of its 517 lines of code are new or changed and 1242 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoEntProE.v, with its module paths and module names changed; 57 of its 93 lines of code are new or changed and 481 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/Y/Prog/DiscoArm3Tail.v, with its module names changed; 28 of its 62 lines of code are new or changed and 59 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YE00 YE01 YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0d YP0c YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC1g YXcalls.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
DiscoYEntryInv DiscoArm3 DiscoArm3JsonModel DiscoArm3JsonCut DiscoYEntBodyStmt.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {LS : lib_shape}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.

Definition ms_in (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (buf : Z)
  (ret c : Z) (R : bvmap 5 word -> Prop) (X : world SEGS -> (word -> option byte) -> Prop)
  : world SEGS -> config -> Prop :=
  jcut B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf (SIGMA AS___asan_memset - BASE) dsh_scr
    (fun regs => getr regs 1 = w64 (BASE + ret) /\ getr regs 10 = w64 (jcur cx c) /\ getr regs 11 = w64 0 /\
       getr regs 12 = w64 144 /\ R regs) X.

Definition ms_out (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (buf : Z)
  (ret c : Z) (R : bvmap 5 word -> Prop) (X : world SEGS -> (word -> option byte) -> Prop)
  : world SEGS -> config -> Prop :=
  jcut B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf ret dsh_scr
    (fun regs => getr regs 10 = w64 (jcur cx c) /\ R regs)
    (fun W m => X W m /\ garr8 SEGS (rd W m) (jcur cx c) (repeat 0 144)).

Definition ms_kept (cx : dcx) (c : Z) (W : world SEGS) (m : word -> option byte) (W' : world SEGS)
  (m' : word -> option byte) : Prop :=
  W' = W /\ d_kept (fun a => d_A cx - ESTACK <= a < d_A cx \/ jcur cx c <= a < jcur cx c + 144) W m W' m'.

Definition ms_step_stmt : Prop :=
  forall (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (buf : Z)
    (ret c : Z) (R : bvmap 5 word -> Prop) (X : world SEGS -> (word -> option byte) -> Prop)
    (W : world SEGS) (cf : config),
  0 <= ret < 2 ^ 40 -> ret mod 2 = 0 -> 0 <= c <= 8 ->
  (forall rg rg', aregs_preserved rg rg' -> R rg -> R rg') ->
  (forall W1 m1 W2 m2, X W1 m1 -> ms_kept cx c W1 m1 W2 m2 -> X W2 m2) ->
  ms_in cx h i n now op W0 c0 T0 T1 buf ret c R X W cf ->
  SRr SEGS W cf (ms_out cx h i n now op W0 c0 T0 T1 buf ret c R X).

End h.
End f.
End d.
