(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/YC8a.v, with its module paths and module names changed; 553 of its 629 lines of code are new or changed and 670 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/Y/Prog/JtokIs.v; 3 of its 78 lines of code are new or changed and 554 lines of the source are left out. *)
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
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YA0o YCbm YA0q YG0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC8i YC1f.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC8g YC85 YC44 YC88.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import ConstsViewDef.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import DiscoYEntryShapes.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import jtok_is_c.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
Section h.
Variable B : asyms.
Definition TJTOK_IS_STK : Z := 48 + 2 * ESTACK.
Definition tjtok_is_post (fq : YK11.FPState) (regs : bvmap 5 word) ly S (W : world SEGS) mem md (kind vk vn : Z) (P T : list byte)
  : world SEGS -> config -> Prop :=
  apost_base (fx := fq) SEGS B TJTOK_IS_STK [] regs ly S W mem md 0
    (fun ly' S' W' regs' mem' _ => Permutation (ablocks B ly' S') (ablocks B ly S) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - TJTOK_IS_STK <= a < spZ regs) ->
         aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a) /\
       ((jtok_match vk kind (Z_to_bv 64 vn) P T /\ getr regs' 10 = w64 1) \/
       (~ jtok_match vk kind (Z_to_bv 64 vn) P T /\ getr regs' 10 = w64 0))).
Definition tjtok_is_spec : Prop :=
  forall (fq : YK11.FPState) ly S W (regs : bvmap 5 word) mem md ch (v x kind vk vp vn : Z) (T slack P : list byte),
  afn_pre SEGS B TJTOK_IS_STK ly S W (regupd regs 8 (Z_to_bv 64 0)) mem md ch ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
  consts_view SEGS MC_CONSTS_LO MC_CONSTS_HI W mem ->
  getr regs 10 = w64 v -> getr regs 11 = Z_to_bv 64 kind -> getr regs 12 = w64 x ->
  -2 ^ 31 <= kind < 2 ^ 31 -> -2 ^ 31 <= vk < 2 ^ 31 ->
  0 < v -> v mod 8 = 0 -> v + 20 <= 2 ^ 63 ->
  val_mem SEGS (mrestrict (w_H W) mem) v 8 vp -> val_mem SEGS (mrestrict (w_H W) mem) (v + 8) 8 vn ->
  val_mem SEGS (mrestrict (w_H W) mem) (v + 16) 4 (vk mod 2 ^ 32) ->
  0 <= vp < 2 ^ 64 -> 0 <= vn < 2 ^ 64 ->
  amem_range v 20 ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF v 20 ->
  shadow_hull_vis (aview SEGS (w_H W) mem) v 20 ->
  (v + 20 <= spZ regs - TJTOK_IS_STK \/ spZ regs <= v) ->
  ~ In (Z_to_bv 8 0) T ->
  garr8 SEGS (mrestrict (w_H W) mem) x (map bv_unsigned (T ++ Z_to_bv 8 0 :: slack)) ->
  (- (x + Z.of_nat (length T) + 1)) mod 8 <= Z.of_nat (length slack) ->
  0 < x -> x + Z.of_nat (length T + 1 + length slack) <= 2 ^ 63 ->
  Z.of_nat (length T) + 1 < 2 ^ 32 ->
  amem_range x (Z.of_nat (length T + 1)) ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF x (Z.of_nat (length T + 1)) ->
  shadow_hull_vis (aview SEGS (w_H W) mem) x (Z.of_nat (length T + 1)) ->
  (x + Z.of_nat (length T + 1 + length slack) <= spZ regs - TJTOK_IS_STK \/ spZ regs <= x) ->
  (vk = kind -> vn = Z.of_nat (length T) ->
     length P = length T /\ garr8 SEGS (mrestrict (w_H W) mem) vp (map bv_unsigned P) /\
     0 <= vp /\ vp + Z.of_nat (length T) <= 2 ^ 63 /\
     amem_range vp (Z.of_nat (length T)) /\
     range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF vp (Z.of_nat (length T)) /\
     (0 < Z.of_nat (length T) -> shadow_hull_vis (aview SEGS (w_H W) mem) vp (Z.of_nat (length T))) /\
     (vp + Z.of_nat (length T) <= spZ regs - TJTOK_IS_STK \/ spZ regs <= vp)) ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_both3_jtok_is) regs mem md) (tjtok_is_post fq regs ly S W mem md kind vk vn P T).
End h.
End f.
End d.
