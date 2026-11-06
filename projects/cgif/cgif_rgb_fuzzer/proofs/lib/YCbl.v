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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCaq YC6j YCbj YCas YCbh YCbk YC7e YC7j YC7k.
Ltac rga_E_tac HEE0 := repeat first [apply rga_E_havoc; [lia|] | apply rga_E_ewset; [lia|]]; exact HEE0.
Ltac ga_obl_cfp HJx HE11 HE44 HRA HAR Hfin Hcid0 Hflo Hfhi Hfal Hrh Hrapp :=
lazymatch goal with |- range_addressable _ (U ?Ex _) (U _ (SOff 11 ?c)) ?len =>
lazymatch type of HE11 with _ = Z_to_bv 64 ?cfp =>
first [ rewrite (U_atom_off Ex 11 cfp c); [| cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact HE11 | lia | lia]
| rewrite (U_atom Ex 11 cfp); [| cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact HE11 | lia] ];
eapply (obl_of_range trasegs _ _ Ex (SOff 44 0) _ len cfp 24);
[ let L := rnLAWS in eapply (range_addressable_entry_frame trasegs _ L); [exact HJx | exact Hfin | exact Hcid0 | exact Hflo | exact Hfhi | exact Hfal
| let x := fresh "x" in let rg := fresh "rg" in let Hr := fresh "Hr" in
intros x (rg & [<- | []] & Hr); cbn [fst snd] in Hr; change (req_size RGB_SIZE) with 64 in Hr;
unfold gbox in Hrapp; clear - Hr Hrh Hrapp; unfold kLowShadowBeg, kHighShadowEnd, kHighMemBeg in *; lia
| exact HAR | exact HRA]
| rewrite (U_atom Ex 44 SB); [reflexivity | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact HE44 | unfold SB; lia]
| lia | lia ] end end.
Ltac ga_chunk_sv cs od w :=
lazymatch cs with
| YQ0b.mkChunk od (CVal w ?e) :: _ => e
| _ :: ?tl => ga_chunk_sv tl od w
end.
Ltac rga_exit_same RX HS HJx kx Hkx HP3 HEE0 HBASE0 LAWS :=
lazymatch goal with |- SRr _ _ _ (rga_post ?B ?cxv) =>
let r := eval cbn in (c_r cxv) in
let Hobj := fresh "Hobj" in let HEEv := fresh "HEEv" in let HRr := fresh "HRr" in
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict (w_H ?W3x) ?msX) =>
assert (HEEv : rga_E cxv Ex) by (rga_E_tac HEE0);
let rs := eval vm_compute in (ss_mem ssx) in
let idx := ga_idx_of_base rs 10%nat in let idx := eval vm_compute in idx in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3x) msX) idx _ HS eq_refl) as HRr; cbn [ms_mem restrict] in HRr;
lazymatch type of HRr with region_ok _ _ _ (YQ0b.mkRegion _ _ _ _ _ ?cs) =>
let ecur := ga_chunk_sv cs 60 4%N in
let vals := eval cbn in [c_g cxv; c_wfn cxv; c_ctx cxv; c_path cxv; c_attr cxv; c_gen cxv; c_loops cxv; c_Wd cxv; c_Hd cxv; c_bef cxv; c_beffmt cxv] in
assert (Hobj : obj_at trasegs (mrestrict (w_H W3x) (ms_mem msX)) r LAY_Rgb (vals ++ [bv_unsigned (sv_denot Ex ecur) mod 2 ^ 32]));
[ let AGv := fresh "AGv" in let EXv := fresh "EXv" in
destruct HEEv as (AGv & EXv & _); unfold rgc_vals in EXv; rga_cbn_cx EXv; rga_cbn_cx AGv;
let X0 := fresh "X" in let X1 := fresh "X" in let X2 := fresh "X" in let X3 := fresh "X" in let X4 := fresh "X" in let X5 := fresh "X" in
let X6 := fresh "X" in let X7 := fresh "X" in let X8 := fresh "X" in let X9 := fresh "X" in let X10 := fresh "X" in
pose proof (EXv 0%nat ltac:(lia)) as X0; pose proof (EXv 1%nat ltac:(lia)) as X1; pose proof (EXv 2%nat ltac:(lia)) as X2;
pose proof (EXv 3%nat ltac:(lia)) as X3; pose proof (EXv 4%nat ltac:(lia)) as X4; pose proof (EXv 5%nat ltac:(lia)) as X5;
pose proof (EXv 6%nat ltac:(lia)) as X6; pose proof (EXv 7%nat ltac:(lia)) as X7; pose proof (EXv 8%nat ltac:(lia)) as X8;
pose proof (EXv 9%nat ltac:(lia)) as X9; pose proof (EXv 10%nat ltac:(lia)) as X10;
cbn [Nat.add nth rga_vals] in X0, X1, X2, X3, X4, X5, X6, X7, X8, X9, X10;
lazymatch goal with Hrgb0 : obj_at _ _ r LAY_Rgb _ |- _ =>
let Hq := fresh "Hq" in pose proof Hrgb0 as Hq; cbn [obj_at LAY_Rgb] in Hq;
destruct Hq as ([_ ?] & [_ ?] & [_ ?] & [_ ?] & [_ ?] & [_ ?] & [_ ?] & [_ ?] & [_ ?] & [_ ?] & [_ ?] & _);
cbn [fst snd N.to_nat Z.of_N] in * |- end;
eapply (rga_obj_r_of_region_any _ _ r _ _ _ _ _ _ ecur HRr);
[ rewrite (AGv 10%nat) by lia;
match goal with H10 : ew _ 10 = Z_to_bv 64 r |- _ => rewrite H10 end; apply unsigned_lit_small;
lazymatch goal with Hlo : 4096 <= r, Hhi : r + 64 <= alloc_ceiling, Cx : _ <= alloc_ceiling <= _ |- _ => clear - Hlo Hhi Cx; lia end
| reflexivity
| let j := fresh "j" in let v := fresh "v" in let Hj := fresh "Hj" in
intros j v Hj;
do 11 (destruct j as [|j]; [injection Hj as <-; split; [cbn [Nat.add]; assumption|]; split; [cbn [nth LAY_Rgb snd fst Z.of_N]; assumption | cbn; tauto]|]);
destruct j; discriminate Hj
| cbn; tauto ]
| cbn [app] in Hobj; clear HRr ] end;
let HJF := fresh "HJF" in
lazymatch type of HJx with ajournal _ _ _ _ ?FPsm _ _ _ _ _ _ _ _ _ _ _ _ =>
pose proof (ajournal_fp_mono B _ _ FPsm (rgc_FP cxv) _ _ _ _ _ _ _ _ _ _ _ _
ltac:(let a := fresh "a" in let rg := fresh "rg" in let Hr := fresh "Hr" in
intros a (rg & [<- | []] & Hr); exists (r, r + req_size RGB_SIZE); split; [left; reflexivity | exact Hr]) HJx) as HJF end;
ga_join HS ss_EPI 900%nat rga_deads_X ltac:(idtac);
let HX := fresh "HX" in
lazymatch goal with |- SRr _ ?W3y (mkCfg ?msy ?mdy) _ =>
lazymatch type of HS with st_ok _ ?Ev _ _ =>
lazymatch type of HJx with ajournal _ _ _ _ _ _ _ _ _ _ ?ownx ?lyx ?Sx _ _ _ _ =>
assert (HX : INV_X B cxv Ev kx lyx Sx W3y msy mdy);
[ eapply (rga_INV_X_same B LAWS cxv Ev kx lyx Sx W3y msy mdy ownx _ HBASE0);
[ unfold rgc_FPs; rga_cbn_cx_goal; exact HJx | exact Hkx | rga_bud_auto   | rga_cbn_cx_goal; exact HP3 | rga_cbn_cx_goal; exact Hobj ]
| unfold rgc_FP in HJF; rga_cbn_cx HJF; rga_hand RX HS HJF kx; [rga_E_tac HEE0 | exact HX] ] end end end
end end.
Ltac ga_keptK HK HJx AG Usp HrinO HrinN HfinSO HfinO HFPn HFSPn HnR HnC HnF HnS EFA F Kg Kg2 Kc Kc2 Kgu Kgu2 Ku Ku2 Vg Vg2 :=
let L := rnLAWS in
lazymatch goal with
| |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 2%nat) _ _ _ _ _) =>
eapply (region_kept_stack_aj trasegs _); [exact HK | exact HJx | ga_evalE AG
| lia | unfold TRGBADD_STK, TRGBADD_FRAME, FDT_STK, TREE_HMAX, ASTACK; lia | lia | lia | lia]
| |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 11%nat) _ _ _ _ _) =>
eapply (region_kept_frame_aj trasegs _); [exact HK | ga_evalE AG | exact HfinSO | rewrite ?EFA; lia | rewrite ?EFA; lia | lia
| let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; apply HnC; lia]
| |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 10%nat) _ _ _ _ _) =>
eapply (region_kept_block_ajw2 trasegs _ L); [exact HK | exact (proj1 HJx) | exact HrinN | ga_evalE AG | exact HrinO | lia | change (req_size 64) with 64; lia | lia | lia
| let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; apply HnR; lia]
| |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 54%nat) _ _ _ _ _) =>
eapply (region_kept_ownframe_aj trasegs _); [exact HK | ga_evalE AG | exact HfinO | left; change (fs_frame_bytes 7) with 8192; rewrite ?EFA; fold F; lia
| let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; apply HnF; lia
| let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; first [exfalso; clear - Ha; lia | apply (fun H => proj1 (HFPn a H)); lia] ]
| |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 67%nat) _ _ _ _ _) =>
eapply (region_kept_ownframe_aj trasegs _); [exact HK | ga_evalE AG | exact HfinO
| right; unfold shadow_addr; rewrite <- SB_SHADOW_OFF; change (fs_frame_bytes 7 / 8) with 1024; rewrite ?EFA; fold F; unfold SB; lia
| let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; apply HnS; unfold SB in *; lia
| let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; first [exfalso; clear - Ha; lia
| unfold shadow_addr in HFSPn; rewrite <- ?SB_SHADOW_OFF in HFSPn; unfold SB in *;
replace a with (2147450880 + F / 8 + (a - (2147450880 + F / 8))) by lia; apply (fun H => proj1 (HFSPn (a - (2147450880 + F / 8)) H)); lia] ]
| |- region_kept _ _ _ _ (YQ0b.mkRegion None _ _ _ _ _) => ga_kept_consts Kg Kg2 Kc Kc2 Kgu Kgu2 Ku Ku2 Vg Vg2
end.
Ltac ga_relow HS AG E10 E11 E10n E11n :=
try clear E10n; try clear E11n;
lazymatch type of HS with st_ok _ ?Ev _ _ =>
lazymatch type of E10 with _ = ?v => assert (E10n : ew Ev 10 = v) by (rewrite (AG 10%nat) by lia; exact E10) end;
lazymatch type of E11 with _ = ?v => assert (E11n : ew Ev 11 = v) by (rewrite (AG 11%nat) by lia; exact E11) end end.
Ltac rga_E_now cxv HS H :=
lazymatch type of HS with st_ok _ ?Ev _ _ =>
assert (H : rga_E cxv Ev);
[ unfold rga_E, rgc_vals, rga_F, rga_FL; rga_cbn_cx_goal;
split; [assumption|]; split;
[ let j := fresh "j" in let Hj := fresh "Hj" in intros j Hj;
do 18 (destruct j as [|j]; [cbn [Nat.add nth rga_vals]; first [assumption | match goal with AGx : forall n, _ -> ew Ev n = _ |- _ => rewrite AGx by lia end; assumption]|]); lia
| split; [assumption|]; split; assumption ]
| ] end.
Ltac ga_keptI3 Hfr Hpres AG HdF HdC HdR Hz Kg Kg2 Kc Kc2 Kgu Kgu2 Ku Ku2 Vg Vg2 :=
lazymatch goal with
| |- region_kept _ _ _ _ (YQ0b.mkRegion (Some ?n) _ _ _ _ _) =>
eapply region_kept_aview; [ ga_evalE AG | | exact Hpres ];
let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; apply Hfr; unfold ESTACK;
lazymatch n with
| 2%nat => ga_zl1
| 54%nat => (unfold gbox in HdF; ga_zl1)
| 67%nat => (unfold gbox in Hz; ga_zl1)
| 10%nat => (unfold gbox in HdR; ga_zl1)
| 11%nat => (unfold gbox in HdC; ga_zl1)
| _ => ga_zlia
end
| |- region_kept _ _ _ _ (YQ0b.mkRegion None _ _ _ _ _) => ga_kept_consts Kg Kg2 Kc Kc2 Kgu Kgu2 Ku Ku2 Vg Vg2
end.
Ltac ga_obl_F HRAf HRF HE44 :=
lazymatch goal with |- range_addressable _ (U ?Ex _) (U _ (SOff 54 ?c)) ?len =>
lazymatch type of HRF with _ = Z_to_bv 64 ?Fv =>
lazymatch type of HRAf with range_addressable _ _ ?lo ?n =>
first [ rewrite (U_atom_off Ex 54 Fv c); [| cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact HRF | lia | lia]
| rewrite (U_atom Ex 54 Fv); [| cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact HRF | lia] ];
eapply (obl_of_range trasegs _ _ Ex (SOff 44 0) _ len lo n);
[ exact HRAf
| rewrite (U_atom Ex 44 SB); [reflexivity | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact HE44 | unfold SB; lia]
| lia | lia ] end end end.
