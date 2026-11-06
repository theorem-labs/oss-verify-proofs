(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YC02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI04 YI1i YI08.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG0a YG01 YG0h YG0u YG0d YCcz.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YCe7 YF9i YCeb YCe8 YCfq YCdy YCe9 YCfx YCi1 YCib YCie YCif YCid.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK0p YI0c YM01 YG0e YCd0.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCph YCjr YCqa YCpj YCqb YClx YCm2 YCqc YCjo YCly YClz YCqd YCqe YCqf YCea YP14 YO3u.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCn4.
Ltac m_rregD HS r v tac H :=
lazymatch type of HS with
| st_ok ?segs ?Ex ?ss (restrict ?Hh ?ms) =>
let e := eval vm_compute in (sr_get (ss_regs ss) r) in
let rg := eval cbn [ms_regs restrict mkst] in (ms_regs ms) in
assert (H : getr rg r = Z_to_bv 64 v)
by (refine (eq_trans (st_ok_restrict_reg segs Hh Ex ss ms r HS) _); change (sv_denot Ex e = Z_to_bv 64 v); tac)
end.
Ltac m_drop_chunk HS n off :=
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (map (fun r0 => if YQ0b.obase_eqb (YQ0b.r_base r0) (Some n)
then YQ0b.mkRegion (YQ0b.r_base r0) (YQ0b.r_lo r0) (YQ0b.r_hi r0) (YQ0b.r_wlo r0) (YQ0b.r_whi r0)
(filter (fun c => negb (Z.eqb (YQ0b.c_off c) off)) (YQ0b.r_chunks r0))
else r0) (ss_mem ssx)) in
let HS3 := fresh "HS3" in
pose proof (st_ok_submem trbsegs Ex ssx msx rs HS ltac:(cbn [ss_mem]; ga_submem_to) ltac:(vm_compute; reflexivity)) as HS3; clear HS; rename HS3 into HS end;
norm_ss HS.
Ltac m_add_chunk HS n off w sv b v tacb tacd tacr Hval :=
lazymatch type of HS with st_ok ?segs ?Ex ?ssx ?msx =>
let c := constr:(YQ0b.mkChunk off (CVal w sv)) in
let res := eval vm_compute in (add_chunk_sem (ss_mem ssx) (Some n) c) in
lazymatch res with
| Some (?rs', ?cs) =>
let HS3 := fresh "HS3" in
assert (HS3 : st_ok segs Ex (mkSST (ss_pc ssx) (ss_regs ssx) (ss_fregs ssx) rs' (ss_resv ssx) (ss_facts ssx)) msx);
[ apply (st_ok_add_chunk_sem segs Ex ssx msx (Some n) c rs' cs HS); [vm_compute; reflexivity|];
intros _; cbn [base_val];
let Hb := fresh "Hb" in assert (Hb : bv_unsigned (ew Ex n) = b) by tacb; rewrite Hb;
apply (chunk_ok_val segs Ex _ b off w sv v); [tacd | tacr | cbn; lia | cbn [ms_mem restrict]; exact Hval]
| clear HS; rename HS3 into HS ]
| None => fail "m_add_chunk: no region of atom" n "contains the chunk"
end end;
norm_ss HS.
