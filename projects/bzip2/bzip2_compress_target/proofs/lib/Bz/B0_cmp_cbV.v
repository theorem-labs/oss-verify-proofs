(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0 SegsB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzTac2 BzArr BzCMem BzCStream BzCState BzCBlock BzArrD CmpMem CmpCut CmpFsKit0 AsanKit AsanCut AsanCutB0.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpCut6.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Export B0_b2c_cbV.
Local Open Scope Z_scope.

Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.
(* [comment removed for export] *)
Definition acenv_ok (X : cbenv) (Y : acenv) : Prop :=
  let usp := bv_unsigned (ce_sp X) in
  ce_lo X + 48 <= ac_P Y /\ ac_P Y + 288 <= usp /\ usp <= ac_P Y + 304 /\
  0x62b000 <= ac_FB Y /\ ac_FB Y + 512 <= CEILv /\
  SH_LO <= ac_SHF Y /\ ac_SHF Y + 64 <= SH_HI.
End ACeilS1.

(* [comment removed for export] *)
Record cbslB := CBSLB { q0 : word; q8 : word; q16 : word; q24 : word; q32 : word; q40 : word; q48 : word; q56 : word; q64 : word; q72 : word; q80 : word; q88 : word; q96 : word; q104 : word; q112 : word; q120 : word; q128 : word; q136 : word; q144 : word; q152 : word; q160 : word; q168 : word; q176 : word }.
Definition cbslB_cells (s : cbslB) : list cell :=
  [C8 (q0 s); C8 (q8 s); C8 (q16 s); C8 (q24 s); C8 (q32 s); C8 (q40 s); C8 (q48 s); C8 (q56 s); C8 (q64 s); C8 (q72 s); C8 (q80 s); C8 (q88 s); C8 (q96 s); C8 (q104 s); C8 (q112 s); C8 (q120 s); C8 (q128 s); C8 (q136 s); C8 (q144 s); C8 (q152 s); C8 (q160 s); C8 (q168 s); C8 (q176 s)].
(* [comment removed for export] *)
Definition bset0 (s : cbslB) (v : word) := CBSLB v (q8 s) (q16 s) (q24 s) (q32 s) (q40 s) (q48 s) (q56 s) (q64 s) (q72 s) (q80 s) (q88 s) (q96 s) (q104 s) (q112 s) (q120 s) (q128 s) (q136 s) (q144 s) (q152 s) (q160 s) (q168 s) (q176 s).
Definition bset8 (s : cbslB) (v : word) := CBSLB (q0 s) v (q16 s) (q24 s) (q32 s) (q40 s) (q48 s) (q56 s) (q64 s) (q72 s) (q80 s) (q88 s) (q96 s) (q104 s) (q112 s) (q120 s) (q128 s) (q136 s) (q144 s) (q152 s) (q160 s) (q168 s) (q176 s).
Definition bset16 (s : cbslB) (v : word) := CBSLB (q0 s) (q8 s) v (q24 s) (q32 s) (q40 s) (q48 s) (q56 s) (q64 s) (q72 s) (q80 s) (q88 s) (q96 s) (q104 s) (q112 s) (q120 s) (q128 s) (q136 s) (q144 s) (q152 s) (q160 s) (q168 s) (q176 s).
Definition bset24 (s : cbslB) (v : word) := CBSLB (q0 s) (q8 s) (q16 s) v (q32 s) (q40 s) (q48 s) (q56 s) (q64 s) (q72 s) (q80 s) (q88 s) (q96 s) (q104 s) (q112 s) (q120 s) (q128 s) (q136 s) (q144 s) (q152 s) (q160 s) (q168 s) (q176 s).
Definition bset32 (s : cbslB) (v : word) := CBSLB (q0 s) (q8 s) (q16 s) (q24 s) v (q40 s) (q48 s) (q56 s) (q64 s) (q72 s) (q80 s) (q88 s) (q96 s) (q104 s) (q112 s) (q120 s) (q128 s) (q136 s) (q144 s) (q152 s) (q160 s) (q168 s) (q176 s).
Definition bset40 (s : cbslB) (v : word) := CBSLB (q0 s) (q8 s) (q16 s) (q24 s) (q32 s) v (q48 s) (q56 s) (q64 s) (q72 s) (q80 s) (q88 s) (q96 s) (q104 s) (q112 s) (q120 s) (q128 s) (q136 s) (q144 s) (q152 s) (q160 s) (q168 s) (q176 s).
Definition bset48 (s : cbslB) (v : word) := CBSLB (q0 s) (q8 s) (q16 s) (q24 s) (q32 s) (q40 s) v (q56 s) (q64 s) (q72 s) (q80 s) (q88 s) (q96 s) (q104 s) (q112 s) (q120 s) (q128 s) (q136 s) (q144 s) (q152 s) (q160 s) (q168 s) (q176 s).
Definition bset56 (s : cbslB) (v : word) := CBSLB (q0 s) (q8 s) (q16 s) (q24 s) (q32 s) (q40 s) (q48 s) v (q64 s) (q72 s) (q80 s) (q88 s) (q96 s) (q104 s) (q112 s) (q120 s) (q128 s) (q136 s) (q144 s) (q152 s) (q160 s) (q168 s) (q176 s).
Definition bset64 (s : cbslB) (v : word) := CBSLB (q0 s) (q8 s) (q16 s) (q24 s) (q32 s) (q40 s) (q48 s) (q56 s) v (q72 s) (q80 s) (q88 s) (q96 s) (q104 s) (q112 s) (q120 s) (q128 s) (q136 s) (q144 s) (q152 s) (q160 s) (q168 s) (q176 s).
Definition bset72 (s : cbslB) (v : word) := CBSLB (q0 s) (q8 s) (q16 s) (q24 s) (q32 s) (q40 s) (q48 s) (q56 s) (q64 s) v (q80 s) (q88 s) (q96 s) (q104 s) (q112 s) (q120 s) (q128 s) (q136 s) (q144 s) (q152 s) (q160 s) (q168 s) (q176 s).
Definition bset80 (s : cbslB) (v : word) := CBSLB (q0 s) (q8 s) (q16 s) (q24 s) (q32 s) (q40 s) (q48 s) (q56 s) (q64 s) (q72 s) v (q88 s) (q96 s) (q104 s) (q112 s) (q120 s) (q128 s) (q136 s) (q144 s) (q152 s) (q160 s) (q168 s) (q176 s).
Definition bset88 (s : cbslB) (v : word) := CBSLB (q0 s) (q8 s) (q16 s) (q24 s) (q32 s) (q40 s) (q48 s) (q56 s) (q64 s) (q72 s) (q80 s) v (q96 s) (q104 s) (q112 s) (q120 s) (q128 s) (q136 s) (q144 s) (q152 s) (q160 s) (q168 s) (q176 s).
Definition bset96 (s : cbslB) (v : word) := CBSLB (q0 s) (q8 s) (q16 s) (q24 s) (q32 s) (q40 s) (q48 s) (q56 s) (q64 s) (q72 s) (q80 s) (q88 s) v (q104 s) (q112 s) (q120 s) (q128 s) (q136 s) (q144 s) (q152 s) (q160 s) (q168 s) (q176 s).
Definition bset104 (s : cbslB) (v : word) := CBSLB (q0 s) (q8 s) (q16 s) (q24 s) (q32 s) (q40 s) (q48 s) (q56 s) (q64 s) (q72 s) (q80 s) (q88 s) (q96 s) v (q112 s) (q120 s) (q128 s) (q136 s) (q144 s) (q152 s) (q160 s) (q168 s) (q176 s).
Definition bset112 (s : cbslB) (v : word) := CBSLB (q0 s) (q8 s) (q16 s) (q24 s) (q32 s) (q40 s) (q48 s) (q56 s) (q64 s) (q72 s) (q80 s) (q88 s) (q96 s) (q104 s) v (q120 s) (q128 s) (q136 s) (q144 s) (q152 s) (q160 s) (q168 s) (q176 s).
Definition bset120 (s : cbslB) (v : word) := CBSLB (q0 s) (q8 s) (q16 s) (q24 s) (q32 s) (q40 s) (q48 s) (q56 s) (q64 s) (q72 s) (q80 s) (q88 s) (q96 s) (q104 s) (q112 s) v (q128 s) (q136 s) (q144 s) (q152 s) (q160 s) (q168 s) (q176 s).
Definition bset128 (s : cbslB) (v : word) := CBSLB (q0 s) (q8 s) (q16 s) (q24 s) (q32 s) (q40 s) (q48 s) (q56 s) (q64 s) (q72 s) (q80 s) (q88 s) (q96 s) (q104 s) (q112 s) (q120 s) v (q136 s) (q144 s) (q152 s) (q160 s) (q168 s) (q176 s).
Definition bset136 (s : cbslB) (v : word) := CBSLB (q0 s) (q8 s) (q16 s) (q24 s) (q32 s) (q40 s) (q48 s) (q56 s) (q64 s) (q72 s) (q80 s) (q88 s) (q96 s) (q104 s) (q112 s) (q120 s) (q128 s) v (q144 s) (q152 s) (q160 s) (q168 s) (q176 s).
Definition bset144 (s : cbslB) (v : word) := CBSLB (q0 s) (q8 s) (q16 s) (q24 s) (q32 s) (q40 s) (q48 s) (q56 s) (q64 s) (q72 s) (q80 s) (q88 s) (q96 s) (q104 s) (q112 s) (q120 s) (q128 s) (q136 s) v (q152 s) (q160 s) (q168 s) (q176 s).
Definition bset152 (s : cbslB) (v : word) := CBSLB (q0 s) (q8 s) (q16 s) (q24 s) (q32 s) (q40 s) (q48 s) (q56 s) (q64 s) (q72 s) (q80 s) (q88 s) (q96 s) (q104 s) (q112 s) (q120 s) (q128 s) (q136 s) (q144 s) v (q160 s) (q168 s) (q176 s).
Definition bset160 (s : cbslB) (v : word) := CBSLB (q0 s) (q8 s) (q16 s) (q24 s) (q32 s) (q40 s) (q48 s) (q56 s) (q64 s) (q72 s) (q80 s) (q88 s) (q96 s) (q104 s) (q112 s) (q120 s) (q128 s) (q136 s) (q144 s) (q152 s) v (q168 s) (q176 s).
Definition bset168 (s : cbslB) (v : word) := CBSLB (q0 s) (q8 s) (q16 s) (q24 s) (q32 s) (q40 s) (q48 s) (q56 s) (q64 s) (q72 s) (q80 s) (q88 s) (q96 s) (q104 s) (q112 s) (q120 s) (q128 s) (q136 s) (q144 s) (q152 s) (q160 s) v (q176 s).
Definition bset176 (s : cbslB) (v : word) := CBSLB (q0 s) (q8 s) (q16 s) (q24 s) (q32 s) (q40 s) (q48 s) (q56 s) (q64 s) (q72 s) (q80 s) (q88 s) (q96 s) (q104 s) (q112 s) (q120 s) (q128 s) (q136 s) (q144 s) (q152 s) (q160 s) (q168 s) v.

(* [comment removed for export] *)
Ltac acenv_open YOK :=
  let H := fresh "YL" in
  pose proof YOK as H; unfold acenv_ok, CEILv, SH_LO, SH_HI in H; cbv zeta in H;
  cps_destruct H as (?YPl & ?YPh & ?YPa & ?YFl & ?YFh & ?YSl & ?YSh).
(* [comment removed for export] *)
Ltac slB_cbn := unfold cbslB_cells; cbn [bset0 bset8 bset16 bset24 bset32 bset40 bset48 bset56 bset64 bset72 bset80 bset88 bset96 bset104 bset112 bset120 bset128 bset136 bset144 bset152 bset160 bset168 bset176 q0 q8 q16 q24 q32 q40 q48 q56 q64 q72 q80 q88 q96 q104 q112 q120 q128 q136 q144 q152 q160 q168 q176].
