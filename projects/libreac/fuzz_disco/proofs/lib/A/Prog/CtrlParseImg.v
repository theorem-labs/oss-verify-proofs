(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module paths and module names changed; 1243 of its 1273 lines of code are new or changed and 39 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoEntCls.v, with its module names changed; 29 of its 51 lines of code are new or changed and 1251 lines of the source are left out. *)
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
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoFrame DiscoBase.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import DiscoImg DiscoRo DiscoRoList CtrlParseCut.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require ClassifyCoreRom.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

Lemma cp_bcast_val : disco_val (A_OBJ OBJ_BCAST) = 0x215a0.
Proof. vm_compute. reflexivity. Qed.

Lemma cp_bcast_glob : In (0x215a0, 7) disco_globs.
Proof. unfold disco_globs. repeat (first [left; reflexivity | right]). Qed.

Lemma cp_HG15_disco : In (@pa_val _ disco_listing PB_disco (A_OBJ OBJ_BCAST), 7) disco_globs.
Proof. cbn [pa_val PB_disco]. rewrite cp_bcast_val. exact cp_bcast_glob. Qed.

Lemma cp_HBC_RNG_disco : YImgTop.IMG_LO + 64 <= @pa_val _ disco_listing PB_disco (A_OBJ OBJ_BCAST) /\
  @pa_val _ disco_listing PB_disco (A_OBJ OBJ_BCAST) + 6 + 64 <= YImgTop.IMG_TOP.
Proof. cbn [pa_val PB_disco]. rewrite cp_bcast_val. unfold YImgTop.IMG_LO, YImgTop.IMG_TOP. lia. Qed.

Lemma cp_HBC_VAL_disco : forall B : asyms, disco_ro_unowned B ->
  forall (H : word -> bool) mem,
  arodata_okP (@pa_segs _ disco_listing PB_disco) (@pa_relro_lo _ disco_listing PB_disco)
    (@pa_relro_hi _ disco_listing PB_disco) B (aview (@pa_segs _ disco_listing PB_disco) H mem) ->
  forall i, 0 <= i < 6 ->
  aview (@pa_segs _ disco_listing PB_disco) H mem (@pa_val _ disco_listing PB_disco (A_OBJ OBJ_BCAST) + i) = Some 255.
Proof.
intros B DRO H mem HR i Hi. cbn [pa_segs pa_val pa_relro_lo pa_relro_hi PB_disco] in *. rewrite cp_bcast_val.
assert (U : ro_unowned B 0x215a0 7).
{ apply disco_ro_unowned_at; [exact DRO|]. unfold disco_ro_ranges. apply in_or_app. left. exact cp_bcast_glob. }
assert (RS : ClassifyCoreRom.ro_span 0x215a0 (0x215a0 + 6) = true) by (vm_compute; reflexivity).
destruct (U (0x215a0 + i) ltac:(lia)) as [Ho He].
rewrite (HR (0x215a0 + i) (ClassifyCoreRom.ro_span_in _ _ RS (0x215a0 + i) ltac:(lia)) Ho He).
assert (Hc : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5) by lia.
destruct Hc as [ -> | [ -> | [ -> | [ -> | [ -> | -> ] ] ] ] ]; vm_compute; reflexivity.
Qed.
End d.
