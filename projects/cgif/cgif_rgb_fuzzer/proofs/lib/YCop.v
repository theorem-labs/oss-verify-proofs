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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCph YCjr YCqa YCpj YCqb YClx YCm2 YCqc YCjo YCly YClz YCqd YCqe YCqf YCea YP14.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCn4 YCnf YCol.
Ltac m_keptWc Hfr2 Hpres2 HJ2 HWIN HWSTc HRNG AG Usp RF E67 E10n E11n celo cehi extra :=
lazymatch goal with
| |- m_region_kept_ck _ _ _ _ (YQ0b.mkRegion (Some 2%nat) ?lo ?hi ?wlo ?whi ?cs) =>
lazymatch type of Usp with _ = ?sp =>
eapply (m_region_kept_ck_av _ _ _ _ _ 2%nat sp lo hi wlo whi cs celo cehi);
[ ga_evalE0 AG; first [reflexivity | exact Usp]
| vm_compute; reflexivity
| vm_compute; reflexivity
| let a := fresh "akw" in let Ha := fresh "Hakw" in let Hn := fresh "Hnkw" in
intros a Ha Hn; apply Hfr2; apply (HWSTc a Ha Hn)
| let a := fresh "akw" in let Ha := fresh "Hakw" in
intros a Ha; destruct HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsp & _); apply Hsp; clear - Ha HRNG; lia ] end
| |- m_region_kept_ck _ _ _ _ _ =>
apply m_region_kept_ck_of_kept; [vm_compute; reflexivity|];
m_keptW Hfr2 Hpres2 HWIN HWIN HRNG AG Usp RF E67 E10n E11n extra
end.
Ltac m_env_fold HS AG :=
let AG2 := fresh "AG" in let Ev := fresh "E" in let HEv := fresh "HE" in
lazymatch type of AG with forall n, _ -> _ = ew ?E0 n =>
lazymatch type of HS with st_ok _ ?Enew _ _ =>
remember Enew as Ev eqn:HEv in *;
assert (AG2 : forall n, (n < 33)%nat -> ew Ev n = ew E0 n)
by (let nn := fresh "nn" in let Hnn := fresh "Hnn" in intros nn Hnn; rewrite HEv; repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; apply AG; exact Hnn);
repeat match goal with H : ew ?Eo ?n = ?v |- _ =>
lazymatch Eo with
| Ev => fail
| _ => lazymatch (eval cbv in (Nat.leb 33 n)) with
| true => let H2 := fresh H in
assert (H2 : ew Ev n = v) by (rewrite HEv; repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact H);
clear H; rename H2 into H
end end end;
clear HEv AG; rename AG2 into AG end end.
