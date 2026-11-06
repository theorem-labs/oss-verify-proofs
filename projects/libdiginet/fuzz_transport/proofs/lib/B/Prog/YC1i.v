(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_grant's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_grant's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-10: taken by path from libreac/fuzz_grant's copy (proofs/libreac/fuzz_grant/lib/A/Prog/YC1i.v, file sha256 fd76710a5bb5; donor not released) for libreac/fuzz_decode's
   program walk: module paths and the listing's names changed. *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YN3v YI04 YI08.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaRun PaShadow PaJournal YC81.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBSyms DgnTransportBList DgnTransportBPa DgnTransportBPaLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg transportb_listing}.
#[local] Notation SEGS := (@pa_segs _ transportb_listing PI).
#[local] Notation VAL := (@pa_val _ transportb_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ transportb_listing PI).
#[local] Notation BASE := (@pa_val _ transportb_listing PI A_TEXT).
Lemma alias_srlw_sll : forall E v, ew E 23 = Z_to_bv 64 (256 * v) -> 0 <= v < 2 ^ 22 ->
sv_denot E (SAlu ALU_SLL (SAluw ALU_SRL (SOff 23 0) (SLit 8)) (SLit 8)) = sv_denot E (SOff 23 0).
Proof.
intros E v H23 Hv. apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_of_S, S_SAluw. cbn [zalu_raw].
rewrite (U_atom E 23 (256 * v) H23) by lia. rewrite !U_SLit.
change (zcanon 8 mod 2 ^ 32) with 8. change (Z.land 8 31) with 8. change (Z.land (zcanon 8) 63) with 8.
rewrite (Z.mod_small (256 * v)) by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
replace (256 * v / 2 ^ 8) with v by (change (2 ^ 8) with 256; rewrite Z.mul_comm, Z.div_mul; lia).
unfold bv_swrap, bv_wrap.
replace (bv_half_modulus 32) with (2 ^ 31) by reflexivity.
replace (bv_modulus 32) with (2 ^ 32) by reflexivity. replace (bv_modulus 64) with (2 ^ 64) by reflexivity.
rewrite (Z.mod_small (v + 2 ^ 31)) by lia. replace (v + 2 ^ 31 - 2 ^ 31) with v by lia.
rewrite (Z.mod_small v) by lia. rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
Lemma req_size_pos' : forall m, 0 <= m -> 0 < req_size m /\ m <= req_size m.
Proof. intros m Hm. unfold req_size. destruct (Z.eqb_spec m 0); cbn; lia. Qed.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Definition PTR (al : Z) : afact := mkAF 4096 140737479966720 al.
Definition Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Lemma region_kept_at1 : forall E STK1 sp1 FP1 lyc Sc W memc mdc mem2 md2 k1 nn c b m cs,
ajournal SEGS B STK1 sp1 FP1 lyc Sc W memc mdc [] lyc Sc W mem2 md2 k1 ->
bv_unsigned (ew E nn) = c -> In (b, m) (ablocks B lyc Sc) -> b <= c -> c + 1 <= b + req_size m -> ~ inFP FP1 c ->
region_kept SEGS E (mrestrict (w_H W) memc) (mrestrict (w_H W) mem2) (YP09.mkRegion (Some nn) 0 1 0 1 cs).
Proof.
intros E STK1 sp1 FP1 lyc Sc W memc mdc mem2 md2 k1 nn c b m cs HJ Hn Hin Hlo Hhi HnF.
pose proof HJ as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & G2 & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR2 Hin) as (_ & _ & _ & _ & Hpres2 & _).
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview SEGS). replace a with (b + (a - b)) by lia. apply (G2 b m (a - b) Hin Hin); [lia|].
replace (b + (a - b)) with c by lia. exact HnF.
- intros _. apply (apresent_writable SEGS). apply (proj1 (Hpres2 a ltac:(lia))).
Qed.
End h.
End f.
End e.
