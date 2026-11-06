(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YC02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI04 YI1i YI08.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YC04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YC19 YF8z YC1d YC1a YC2o YC10 YC1b YC2u
YC4u YC4z YC52 YC53 YC51.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK0p YI0c YM01 YG0e YC05.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCaq YC6j YCbj YCas YCat YCau YCbh YCbk YC7e YC7j YCbl YC6e YCav YC7f YCaw YCax YCay YCaz YC7g YCbm YCb0 YCb1 YCbn YCbi YCbo YC1c YCbe YP14 YC4b YC2r.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YC8i YC9u.
Ltac m_hand_ih IH HS HJx kx :=
lazymatch goal with |- SRr _ ?W3 (mkCfg ?ms3 ?md3) (rga_post ?B ?cxv) =>
lazymatch type of HS with st_ok _ ?Ev _ _ =>
lazymatch type of HJx with ajournal _ _ _ _ _ _ _ _ _ _ _ ?lyx ?Sx _ _ _ _ =>
eapply (IH cxv Ev kx lyx Sx W3 ms3 md3);
[ lazymatch goal with H0 : rga_base _ _ |- _ => exact H0 end
| idtac
| first [eassumption | idtac]
| first [exact HJx | unfold rgc_FP, rgc_FPs; rga_cbn_cx_goal; cbn [ms_mem]; exact HJx | idtac]
| first [eassumption | idtac]
| red; rga_cbn_cx_goal
| exact HS ] end end end.
Ltac m_ewT := match goal with H : ew _ ?n = ?v |- ew _ ?n = ?v => repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; exact H end.
Ltac m_inv_conj :=
first [ lazymatch goal with |- rga_kb _ _ _ _ _ _ _ => split; [first [eassumption | lia] | rga_bud_auto] end
| eassumption
| m_ewT
| split; [m_ewT | split; eassumption]
| match goal with H : ew _ ?n = Z_to_bv 64 ?a |- exists _, ew _ ?n = _ /\ _ => exists a; split; [m_ewT | eassumption] end
| match goal with H : ?P -> ew _ ?n = ?v |- ?P -> ew _ ?n = ?v => let Hp := fresh in intros Hp; specialize (H Hp); m_ewT end
| match goal with Hw : ?P -> ?w = ?v |- ?P -> ew _ ?n = ?v => let Hp := fresh in intros Hp; rewrite <- (Hw Hp); m_ewT end
| match goal with |- _ -> ew _ _ = _ => intros _; m_ewT end ].
Ltac m_inv_auto := repeat (split; [m_inv_conj|]); m_inv_conj.
Ltac m_keptW Hfr2 Hpres2 HWIN HWST HRNG AG Usp RF E67 E10n E11n extra :=
lazymatch goal with
| |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 2%nat) _ _ _ _ _) =>
eapply (region_kept_aview _ _ _ _ 2%nat); [ga_evalE0 AG; first [reflexivity | exact Usp] | | exact Hpres2];
let a := fresh "akw" in let Ha := fresh "Hakw" in
intros a Ha; cbn [YQ0b.r_lo YQ0b.r_hi] in Ha; apply Hfr2; apply (HWST a); clear - Ha; lia
| |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 54%nat) _ _ _ _ _) =>
eapply (region_kept_aview _ _ _ _ 54%nat); [ga_evalE0 AG; first [reflexivity | exact RF | rewrite RF; apply unsigned_lit_small; clear - HRNG; lia] | | exact Hpres2];
let a := fresh "akw" in let Ha := fresh "Hakw" in
intros a Ha; cbn [YQ0b.r_lo YQ0b.r_hi] in Ha; apply Hfr2; apply (HWIN a); clear - Ha HRNG; lia
| |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 67%nat) _ _ _ _ _) =>
eapply (region_kept_aview _ _ _ _ 67%nat); [ga_evalE0 AG; first [reflexivity | exact E67 | rewrite E67; apply unsigned_lit_small; unfold SB; clear - HRNG; lia] | | exact Hpres2];
let a := fresh "akw" in let Ha := fresh "Hakw" in
intros a Ha; cbn [YQ0b.r_lo YQ0b.r_hi] in Ha; apply Hfr2; apply (HWIN a); unfold SB in Ha; clear - Ha HRNG; lia
| |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 10%nat) _ _ _ _ _) =>
eapply (region_kept_aview _ _ _ _ 10%nat); [ga_evalE0 AG; first [reflexivity | exact E10n | rewrite E10n; apply unsigned_lit_small; clear - HRNG; lia] | | exact Hpres2];
let a := fresh "akw" in let Ha := fresh "Hakw" in
intros a Ha; cbn [YQ0b.r_lo YQ0b.r_hi] in Ha; apply Hfr2; apply (HWIN a); clear - Ha HRNG; lia
| |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 11%nat) _ _ _ _ _) =>
eapply (region_kept_aview _ _ _ _ 11%nat); [ga_evalE0 AG; first [reflexivity | exact E11n | rewrite E11n; apply unsigned_lit_small; clear - HRNG; lia] | | exact Hpres2];
let a := fresh "akw" in let Ha := fresh "Hakw" in
intros a Ha; cbn [YQ0b.r_lo YQ0b.r_hi] in Ha; apply Hfr2; apply (HWIN a); clear - Ha HRNG; lia
| _ => extra
end.
Ltac m_keptW_blk Hfr2 Hpres2 HWIN AG n b Rb Hrng :=
lazymatch goal with
| |- region_kept _ _ _ _ (YQ0b.mkRegion (Some n) _ _ _ _ _) =>
eapply (region_kept_aview _ _ _ _ n b); [ga_evalE0 AG; first [reflexivity | exact Rb | rewrite Rb; apply unsigned_lit_small; clear - Hrng; lia] | | exact Hpres2];
let a := fresh "akw" in let Ha := fresh "Hakw" in
intros a Ha; cbn [YQ0b.r_lo YQ0b.r_hi] in Ha; apply Hfr2; apply (HWIN a); clear - Ha Hrng; lia
end.
Ltac m_gen_slots_win HS N Ex vals i slots :=
lazymatch slots with
| [] => idtac
| (?b, ?lo, ?off) :: ?tl =>
lazymatch type of HS with st_ok _ ?Ey ?ssy ?msy =>
let HS4 := fresh "HS4" in
let n := eval vm_compute in (N + i)%nat in
let l := eval vm_compute in (slot_vals b lo off (ss_mem ssy)) in
lazymatch l with
| [?sv0] =>
pose proof (st_ok_gen_slot trasegs Ey ssy msy b lo off (SOff n 0) HS
ltac:(change (slot_vals b lo off (ss_mem ssy)) with l;
constructor; [|constructor];
rewrite (sv_denot_agree_on (win_free N (length vals)) Ex Ey sv0 (env_agree_on_havoc Ex N vals) ltac:(vm_compute; reflexivity));
cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; change n with (N + i)%nat;
rewrite (ew_havoc_new _ N vals i (Z_to_bv 64 0)) by (cbn [length]; lia); cbn [nth]; reflexivity)
ltac:(vm_compute; reflexivity)) as HS4;
clear HS; rename HS4 into HS;
lazymatch type of HS with st_ok _ _ ?ssz _ => let v := eval vm_compute in ssz in change ssz with v in HS end;
m_gen_slots_win HS N Ex vals (S i) tl
end end
end.
Ltac m_join_slots_win HS target N deads slots hook :=
norm_ss HS;
let tg := eval red in target in
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let HS3 := fresh "HS3" in
let dl := eval cbv in deads in
let sw := slot_words Ex ssx slots in
let vals := constr:(map (fun r : bv 5 => getr (ms_regs msx) r) dl ++ sw) in
let vals' := eval cbn [map app ms_regs restrict] in vals in
pose proof (st_ok_havoc_win trasegs N Ex ssx msx vals' HS ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS;
ga_set_regs_rec HS N vals' 0%nat dl;
norm_ss HS;
let i0 := eval vm_compute in (length dl) in
m_gen_slots_win HS N Ex vals' i0 slots end;
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let HS3 := fresh "HS3" in
let rs := eval cbn [ss_mem] in (ss_mem tg) in
pose proof (st_ok_submem trasegs Ex ssx msx rs HS ltac:(cbn [ss_mem]; ga_submem_to) ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS end;
norm_ss HS;
hook;
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let HS3 := fresh "HS3" in
let fa := eval cbn [ss_facts f_atoms] in (f_atoms (ss_facts tg)) in
let cs := eval cbn [ss_facts f_conds] in (f_conds (ss_facts tg)) in
let al := eval cbn [ss_facts f_alias] in (f_alias (ss_facts tg)) in
pose proof (st_ok_facts_incl3 trasegs Ex ssx msx fa cs al HS ltac:(ga_incl_lit_tac) ltac:(ga_incl_lit_tac) ltac:(ga_incl_lit_tac)) as HS3;
clear HS; rename HS3 into HS end;
norm_ss HS;
lazymatch type of HS with st_ok _ _ ?ssx _ => first [change ssx with target in HS | idtac "JOIN-MISMATCH" ssx tg] end.
