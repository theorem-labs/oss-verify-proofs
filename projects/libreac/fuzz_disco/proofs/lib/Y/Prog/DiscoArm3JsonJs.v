(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module names changed; 463 of its 496 lines of code are new or changed and 36 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoEntHdrLib.v, with its module paths and module names changed; 62 of its 92 lines of code are new or changed and 466 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/Y/Prog/DiscoArm3TailDefs.v, with its module paths and module names changed; 31 of its 67 lines of code are new or changed and 56 lines of the source are left out. *)
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
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_jscalar_model disco_json_reader_model.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition TJSON_SCALAR_STK : Z := 128 + 2 * ESTACK.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {LS : lib_shape}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.

Definition jsc_in (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (buf : Z)
  (shf : Z -> Z) (ret idx voff : Z) (R : bvmap 5 word -> Prop) (X : world SEGS -> (word -> option byte) -> Prop)
  : world SEGS -> config -> Prop :=
  jcut B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf AF_both3_json_scalar shf
    (fun regs => getr regs 1 = w64 (BASE + ret) /\ getr regs 10 = w64 buf /\ getr regs 11 = w64 idx /\
       getr regs 12 = w64 (a3_r T1 now) /\ getr regs 13 = w64 (d_A cx + voff) /\ R regs)
    X.

Definition jsc_out (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (buf : Z)
  (shf : Z -> Z) (ret voff j kk ks kl : Z) (R : bvmap 5 word -> Prop)
  (X : world SEGS -> (word -> option byte) -> Prop) : world SEGS -> config -> Prop :=
  jcut B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf ret shf
    (fun regs => getr regs 10 = w64 j /\ R regs)
    (fun W m => X W m /\ val_mem SEGS (rd W m) (d_A cx + voff) 8 (buf + ks) /\
       val_mem SEGS (rd W m) (d_A cx + voff + 8) 8 kl /\ val_mem SEGS (rd W m) (d_A cx + voff + 16) 4 kk).

Definition jsc_kept (cx : dcx) (voff : Z) (W : world SEGS) (m : word -> option byte) (W' : world SEGS)
  (m' : word -> option byte) : Prop :=
  4096 <= d_FB cx /\ d_FB cx + 4096 <= d_A cx - TJSON_SCALAR_STK /\ d_A cx + 472 <= d_S cx /\ d_S cx <= 2 ^ 47 /\
  d_kept (fun a => d_A cx - TJSON_SCALAR_STK <= a < d_A cx \/ d_A cx + voff <= a < d_A cx + voff + 20) W m W' m'.

Definition jsc_step_stmt : Prop :=
  forall (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (buf : Z)
    (shf : Z -> Z) (ret idx voff j kk ks kl : Z) (R : bvmap 5 word -> Prop)
    (X : world SEGS -> (word -> option byte) -> Prop) (W : world SEGS) (c : config),
  0 <= ret < 2 ^ 40 -> ret mod 2 = 0 -> voff mod 8 = 0 -> 424 <= voff -> voff + 20 <= 472 -> 0 <= idx ->
  jscalar (a3_text T1 now) idx = Some (j, kk, ks, kl) ->
  (forall rg rg', aregs_preserved rg rg' -> R rg -> R rg') ->
  (forall W1 m1 W2 m2, X W1 m1 -> jsc_kept cx voff W1 m1 W2 m2 -> X W2 m2) ->
  jsc_in cx h i n now op W0 c0 T0 T1 buf shf ret idx voff R X W c ->
  SRr SEGS W c (jsc_out cx h i n now op W0 c0 T0 T1 buf shf ret voff j kk ks kl R X).

End h.
End f.
End d.
