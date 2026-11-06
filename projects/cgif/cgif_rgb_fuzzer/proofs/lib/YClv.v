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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCph YCjr YCqa YCpj YCqb YClx YCm2 YCqc YCjo YCly YCpm YClz YCqd YCqe YChh YCn4 YCn6 YCnf YCoi YCoj YCok YCon.
Ltac g_havoc HS N vals :=
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let HS3 := fresh "HS3" in
pose proof (st_ok_havoc trbsegs N Ex ssx msx vals HS ltac:(vm_compute; reflexivity)) as HS3; clear HS; rename HS3 into HS end.
Ltac g_havoc_val HS N i v En :=
lazymatch type of HS with st_ok _ (havoc ?E0v _ ?vals) _ _ =>
let n := eval vm_compute in (N + i)%nat in
assert (En : ew (havoc E0v N vals) n = v)
by (change n with (N + i)%nat; rewrite (ew_havoc_new _ N vals i (Z_to_bv 64 0)) by (cbn [length]; lia); reflexivity) end.
Ltac g_pin HS r sv tac :=
lazymatch type of HS with st_ok ?segs ?Ev ?ssx (restrict ?Hh ?msx) =>
let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
let HS3 := fresh "HS3" in
pose proof (ast_ok_set_reg_fp segs Ev ssx (restrict Hh msx) r sv HS eq_refl
ltac:(cbn [ms_regs restrict]; rewrite (st_ok_restrict_reg segs Hh Ev ssx msx r HS); change (sv_denot Ev sv = sv_denot Ev e); tac)) as HS3;
clear HS; rename HS3 into HS end;
norm_ss HS.
Ltac g_fact HS n af tac :=
lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
let HS3 := fresh "HS3" in
pose proof (st_ok_add_fact trbsegs Ev ssx msx n af HS ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; tac)) as HS3;
clear HS; rename HS3 into HS end;
norm_ss HS.
Ltac g_cond HS c a b tac :=
lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
let HS3 := fresh "HS3" in
pose proof (st_ok_add_cond trbsegs Ev ssx msx c a b HS ltac:(tac)) as HS3;
clear HS; rename HS3 into HS end;
norm_ss HS.
Ltac g_region HS AG reg tacok tacd :=
lazymatch type of HS with st_ok _ ?Ev _ _ =>
let HS3 := fresh "HS3" in
pose proof (ast_ok_add_region trbsegs Ev _ _ reg HS eq_refl
ltac:(unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst]; tacok)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
ga_evalE0 AG; repeat split; tacd)) as HS3;
clear HS; rename HS3 into HS end;
norm_ss HS.
Ltac g_slot_set HS b lo off v' tac :=
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let HS3 := fresh "HS3" in
let l := eval vm_compute in (slot_vals b lo off (ss_mem ssx)) in
pose proof (st_ok_gen_slot trbsegs Ex ssx msx b lo off v' HS
ltac:(change (slot_vals b lo off (ss_mem ssx)) with l; constructor; [tac | constructor])
ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS end;
norm_ss HS.
Ltac g_keptP Hfr HRNG HJ2 AG Usp RF E67 E10n E11n Rtb F HFpres Hrpres Htbpres consts :=
lazymatch goal with
| |- m_region_kept_ck _ _ _ _ (YQ0b.mkRegion (Some ?n) _ _ _ _ _) =>
apply m_region_kept_ck_of_kept; [vm_compute; reflexivity|];
lazymatch n with
| 2%nat =>
lazymatch type of Usp with _ = ?sp =>
eapply (m_region_kept_av _ _ _ _ _ 2%nat sp);
[ ga_evalE0 AG; first [reflexivity | exact Usp]
| let a := fresh "akw" in let Ha := fresh "Hakw" in intros a Ha; cbn [YQ0b.r_lo YQ0b.r_hi] in Ha; apply Hfr; clear - Ha HRNG; lia
| let a := fresh "akw" in let Ha := fresh "Hakw" in intros a Ha; cbn [YQ0b.r_wlo YQ0b.r_whi] in Ha;
destruct HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsp & _); apply Hsp; clear - Ha HRNG; lia ] end
| 54%nat =>
eapply (m_region_kept_av _ _ _ _ _ 54%nat F);
[ ga_evalE0 AG; first [reflexivity | exact RF | rewrite RF; apply unsigned_lit_small; clear - HRNG; lia]
| let a := fresh "akw" in let Ha := fresh "Hakw" in intros a Ha; cbn [YQ0b.r_lo YQ0b.r_hi] in Ha; apply Hfr; clear - Ha HRNG; lia
| let a := fresh "akw" in let Ha := fresh "Hakw" in intros a Ha; cbn [YQ0b.r_wlo YQ0b.r_whi] in Ha; apply (fun Hx => proj1 (HFpres a Hx)); clear - Ha; lia ]
| 67%nat =>
eapply (m_region_kept_av _ _ _ _ _ 67%nat (SB + F / 8));
[ ga_evalE0 AG; first [reflexivity | exact E67 | rewrite E67; apply unsigned_lit_small; unfold SB; clear - HRNG; lia]
| let a := fresh "akw" in let Ha := fresh "Hakw" in intros a Ha; cbn [YQ0b.r_lo YQ0b.r_hi] in Ha; apply Hfr; unfold SB in Ha |- *; clear - Ha HRNG; lia
| let a := fresh "akw" in let Ha := fresh "Hakw" in intros a Ha; cbn [YQ0b.r_wlo YQ0b.r_whi] in Ha; exfalso; clear - Ha; lia ]
| 10%nat =>
lazymatch type of E10n with _ = Z_to_bv 64 ?r =>
eapply (m_region_kept_av _ _ _ _ _ 10%nat r);
[ ga_evalE0 AG; first [reflexivity | exact E10n | rewrite E10n; apply unsigned_lit_small; clear - HRNG; lia]
| let a := fresh "akw" in let Ha := fresh "Hakw" in intros a Ha; cbn [YQ0b.r_lo YQ0b.r_hi] in Ha; apply Hfr; clear - Ha HRNG; lia
| let a := fresh "akw" in let Ha := fresh "Hakw" in intros a Ha; cbn [YQ0b.r_wlo YQ0b.r_whi] in Ha; apply (fun Hx => proj1 (Hrpres a Hx)); clear - Ha; lia ] end
| 11%nat =>
lazymatch type of E11n with _ = Z_to_bv 64 ?cfp =>
eapply (m_region_kept_av _ _ _ _ _ 11%nat cfp);
[ ga_evalE0 AG; first [reflexivity | exact E11n | rewrite E11n; apply unsigned_lit_small; clear - HRNG; lia]
| let a := fresh "akw" in let Ha := fresh "Hakw" in intros a Ha; cbn [YQ0b.r_lo YQ0b.r_hi] in Ha; apply Hfr; clear - Ha HRNG; lia
| let a := fresh "akw" in let Ha := fresh "Hakw" in intros a Ha; cbn [YQ0b.r_wlo YQ0b.r_whi] in Ha; exfalso; clear - Ha; lia ] end
| 305%nat =>
lazymatch type of Rtb with _ = Z_to_bv 64 ?tb =>
eapply (m_region_kept_av _ _ _ _ _ 305%nat tb);
[ ga_evalE0 AG; first [reflexivity | exact Rtb | rewrite Rtb; apply unsigned_lit_small; clear - HRNG; lia]
| let a := fresh "akw" in let Ha := fresh "Hakw" in intros a Ha; cbn [YQ0b.r_lo YQ0b.r_hi] in Ha; apply Hfr; clear - Ha HRNG; lia
| let a := fresh "akw" in let Ha := fresh "Hakw" in intros a Ha; cbn [YQ0b.r_wlo YQ0b.r_whi] in Ha; apply (fun Hx => proj1 (Htbpres a Hx)); clear - Ha; lia ] end
end
| |- m_region_kept_ck _ _ _ _ (YQ0b.mkRegion None _ _ _ _ _) => consts
end.
Ltac g_kept_run HFr AG P Hceil Hslo FFS KP :=
let UNx := fresh "UNx" in
m_run_keptG HFr AG P Hceil Hslo FFS UNx;
let KP2 := fresh "KP" in
lazymatch type of UNx with forall a, _ -> _ -> aview _ ?Hn ?mn a = _ =>
lazymatch type of KP with forall a, _ -> _ -> _ = aview _ ?H0 ?m0 a =>
assert (KP2 : forall a, 0 <= a < 2 ^ 64 -> ~ P a -> aview trbsegs Hn mn a = aview trbsegs H0 m0 a)
by (let a := fresh "a" in let Ha := fresh "Ha" in let Hn := fresh "Hn" in intros a Ha Hn; rewrite (UNx a Ha Hn); exact (KP a Ha Hn)) end end;
clear UNx KP; rename KP2 into KP.
