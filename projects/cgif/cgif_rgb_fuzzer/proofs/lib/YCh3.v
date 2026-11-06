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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI01 YI04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YCcz.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YCe7 YF9i YCeb YCe8 YCfq YCdy YCfr YCdv YCe9 YCgi YChv YChx YChw YCgl YChb YChm YChi YChj YChk YChn YChf YChe YCho.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section b.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis ML : model_laws (as_universe B).
Let HBcode := tl_code B TL. Let errno_low := tl_env B TL.
Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL. Let HBguar := tl_got_uar B TL. Let HBuar := tl_uar_cell B TL.
Lemma ra_G_aux : ra_from B ss_G3 (INV_T0 B) -> ra_from B ss_G2 (INV_T0 B).
Proof.
intros RG3. ra_prelude.
pose proof HINV as (Hk3 & (K1 & EK & HK1r & HK1s) & (bb & Lbb & M & E600 & E601 & HPerm3 & Hbb4096 & HM & Abb & Tbb)).
assert (Hraw3 : In (raw, RAW_SIZE) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm3|]; right; exact Hraw_in).
assert (Hing3 : In (g, CGIF_SIZE) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm3|]; right; exact Hing).
ra_blocks3 Hraw3 Hing3. fold F in HdFR, HdFG.
relowC HS AG E10 E11 E32 E10n E11n E32n.
pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
reshok_bx HS 40%nat.
aj_run_tok trbtbl_lib_ok HS HJ3 SHOK RABspan.
all: try (obl_blk HJ3 E10n E40 Hraw3).
all: try (obl_blk HJ3 E32n E40 Hing3).
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrRA AG fpos F EFA3.
clear_frames.
srr_branch_tok trbtbl_lib_ok HS SHOK RABspan.
-
aj_run_to_tok trbtbl_lib_ok HS HJ3 SHOK RABspan 0x8a028; [awrRA AG fpos F EFA3|]. clear_frames.
rebaseE HS AG HEv. clear HEv.
ra_join HS ss_G3 750%nat ra_deads_G3 ltac:(idtac).
ra_hand RG3 HS. solve_INV_T0 Hk3 EK HK1r HK1s E600 E601 HPerm3 Hbb4096 HM Abb Tbb.
-
unfold branch_taken in Hc. rewrite bv_eqb_unsigned in Hc. cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in Hc.
rewrite ?ew_ewset_other in Hc by lia.
rewrite E49, Z.add_0_r, Z_to_bv_bv_unsigned, !unsigned_lit_small in Hc by lia. apply Z.eqb_neq in Hc.
destruct (HK1s Hc) as [HK11 HKs1].
assert (Hp2 : 2 <= 2 ^ K1 <= 256) by (clear - HK11 HK1r; split; [change 2 with (2 ^ 1) | change 256 with (2 ^ 8)]; apply Z.pow_le_mono_r; lia).
aj_run_to_tok trbtbl_lib_ok HS HJ3 SHOK RABspan 0x89fb4.
all: try (obl_blk HJ3 E10n E40 Hraw3).
all: try (obl_blk HJ3 E32n E40 Hing3).
all: try (oblFA HJ3 E11n E40 HRA HAR Hfin Hcid0 Hflo Hfhi Hfal).
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrRA AG fpos F EFA3.
clear_frames.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
pose proof (U_ra_ndummy_b Ev 199 49 K1 slct EK ltac:(clear - HK11 HK1r; lia) E49 ltac:(clear - Hc HKs1 Rslct; lia)) as (Dn0 & Dn1 & _) end.
srr_branch_tok trbtbl_lib_ok HS SHOK RABspan.
+
exfalso. rewrite branch_ne_U, Dn1, Dn0, Z.eqb_refl in Hc0. discriminate Hc0.
+ clear Dn0 Dn1.
aj_run_to_tok trbtbl_lib_ok HS HJ3 SHOK RABspan 0x89fdc.
all: try (obl_blk HJ3 E10n E40 Hraw3).
all: try (obl_blk HJ3 E32n E40 Hing3).
all: try (oblFA HJ3 E11n E40 HRA HAR Hfin Hcid0 Hflo Hfhi Hfal).
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrRA AG fpos F EFA3.
clear_frames.
frame_pres HJ3 Hfin3 EFA3 F HFp4 HFSp4.
fs_rwA HS E70 HFSp4.
aj_run_to_sh trbtbl_lib_ok HS HJ3 0x89fe0; [awrRA AG fpos F EFA3|]. clear_frames.
fs_roA HS. rebaseE HS AG HEv. clear HEv. relowC HS AG E10 E11 E32 E10n E11n E32n. reshok_bx HS 40%nat.
aj_run_tok trbtbl_lib_ok HS HJ3 SHOK RABspan; [awrRA AG fpos F EFA3|]. clear_frames.
Local Ltac tailG3 HS HJx AG E70 Hfin3 EFA3 F fpos RG3 Hk3 EK HK1r HK1s E600 E601 HPerm3 Hbb4096 HM Abb Tbb E10 E11 E32 E10n E11n E32n :=
let HFp := fresh "HFp" in let HFSp := fresh "HFSp" in let HEv := fresh "HEv" in
frame_pres HJx Hfin3 EFA3 F HFp HFSp;
fs_rwA HS E70 HFSp;
aj_run_to_sh trbtbl_lib_ok HS HJx 0x8a018; [awrRA AG fpos F EFA3|]; clear_frames;
fs_roA HS; rebaseE HS AG HEv; clear HEv; relowC HS AG E10 E11 E32 E10n E11n E32n; reshok_bx HS 40%nat;
lazymatch goal with SHOK : sh_ok _ _ _ _ _ |- _ =>
aj_run_to_tok trbtbl_lib_ok HS HJx SHOK RABspan 0x8a028; [awrRA AG fpos F EFA3|]; clear_frames end;
rebaseE HS AG HEv; clear HEv;
ra_join HS ss_G3 750%nat ra_deads_G3 ltac:(idtac);
ra_hand RG3 HS; solve_INV_T0 Hk3 EK HK1r HK1s E600 E601 HPerm3 Hbb4096 HM Abb Tbb.
srr_branch_tok trbtbl_lib_ok HS SHOK RABspan.
*
aj_run_to_tok trbtbl_lib_ok HS HJ3 SHOK RABspan 0x8a014; [awrRA AG fpos F EFA3|]. clear_frames.
tailG3 HS HJ3 AG E70 Hfin3 EFA3 F fpos RG3 Hk3 EK HK1r HK1s E600 E601 HPerm3 Hbb4096 HM Abb Tbb E10 E11 E32 E10n E11n E32n.
*
lazymatch type of HS with st_ok _ ?Ev _ _ =>
pose proof (proj2 (proj2 (U_ra_ndummy_b Ev 199 49 K1 slct EK ltac:(clear - HK11 HK1r; lia) E49 ltac:(clear - Hc HKs1 Rslct; lia)))) as Dn3 end.
rewrite branch_eq_U, Dn3, U_SLit in Hc1. change (zcanon 0) with 0 in Hc1. apply Z.eqb_neq in Hc1.
aj_run_to_tok trbtbl_lib_ok HS HJ3 SHOK RABspan 0x89fec; [awrRA AG fpos F EFA3|]. clear_frames.
assert (Hn : 3 <= 3 * (2 ^ K1 - slct) <= 765) by (clear - Hp2 Hc1 Hc HKs1 Rslct; lia).
lazymatch type of HS with st_ok _ ?Ev _ _ =>
assert (Usp3 : bv_unsigned (ew Ev 2) = spZ regs) by (cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 2%nat) by lia; exact Usp) end.
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 32%nat in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_region) in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3) msX) i r HS ltac:(vm_compute; reflexivity)) as HRg; cbn [ms_mem restrict] in HRg;
lazymatch type of HRg with region_ok _ _ _ (YQ0b.mkRegion (Some 32%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 32 g cs lo hi wlo whi 56 8%N (SLit A_writecb) A_writecb HRg ltac:(evalE AG) ltac:(cbn; tauto) eq_refl ltac:(unfold A_writecb; cbn; lia) ltac:(cbn; lia)) as M56;
pose proof (field_of_region Ex _ 32 g cs lo hi wlo whi 80 8%N (SLit 0) 0 HRg ltac:(evalE AG) ltac:(cbn; tauto) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as M80;
pose proof (field_of_region Ex _ 32 g cs lo hi wlo whi 64 8%N (SOff 52 0) ctx HRg ltac:(evalE AG) ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E52, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(clear - Rctx; cbn; lia) ltac:(cbn; lia)) as M64 end;
clear HRg;
let ih := idx_of_base_lo rs 2%nat (-320) in let ih := eval vm_compute in ih in
let rh := eval vm_compute in (nth ih rs got_region) in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3) msX) ih rh HS ltac:(vm_compute; reflexivity)) as HRg; cbn [ms_mem restrict] in HRg;
lazymatch type of HRg with region_ok _ _ _ (YQ0b.mkRegion (Some 2%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-152) 8%N (SOff 57 32) (F + 32) HRg Usp3 ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; evalE AG) ltac:(cbn; lia) ltac:(cbn; lia)) as Mbuf end;
clear HRg end.
replace (spZ regs + -152) with (spZ regs - 320 + 168) in Mbuf by lia.
rreg HS (2%bv : bv 5) Q2. rreg HS (9%bv : bv 5) Q9. rreg HS (19%bv : bv 5) Q18.
rreg HS (27%bv : bv 5) Q20. rreg HS (20%bv : bv 5) Q22.
lazymatch type of HS with st_ok _ ?Ev ?ssx (restrict _ ?msX) =>
let e := eval vm_compute in (sr_get (ss_regs ssx) 26%bv) in
assert (Q19 : getr (ms_regs msX) 26%bv = Z_to_bv 64 (3 * (2 ^ K1 - slct)));
[ rewrite (st_ok_restrict_reg trbsegs _ _ _ _ 26%bv HS); change (sv_denot Ev e = Z_to_bv 64 (3 * (2 ^ K1 - slct)));
rewrite denot_lit_U, Dn3; reflexivity | ] end.
assert (Qal : (spZ regs - 320) mod 16 = 0).
{ pose proof (Z.div_mod (spZ regs) 32 ltac:(lia)) as D. rewrite Hal32, Z.add_0_r in D. rewrite D.
replace (32 * (spZ regs / 32) - 320) with ((2 * (spZ regs / 32) - 20) * 16) by lia. apply Z_mod_mult. }
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (ra_wdb B TL LAWS (Z.to_nat (3 * (2 ^ K1 - slct))) (3 * (2 ^ K1 - slct)) W3 (ms_regs msX) (ms_mem msX) _
TRAWADD_STK (spZ regs) [(raw + 40, raw + 44)] ly S W mem md [(1, fpos)] ly3 S3 k (spZ regs - 320) g ctx (F + 32) ltac:(clear - Hn; lia) HJ3);
[ rewrite Q2; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 2%nat) by lia; rewrite Usp; f_equal; clear; lia
| rewrite Q9; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 2%nat) by lia; rewrite Usp; f_equal; clear; lia
| exact Qal | rewrite FFS; clear; lia | clear; lia | clear - C1 Hceil Hslo FFS; lia | clear - H47 Hshi; lia
| exact Q19 | clear - Hn; lia | exact Q20 | exact Q18
| rewrite Q22; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 32%nat) by lia; exact E32
| exact Hing3 | exact M56 | exact M80 | exact M64 | exact Rctx | exact Mbuf | lia ] end. }
cbv beta. intros W6 c6 _ (-> & regs6 & mem6 & md6 & -> & HJ6 & HK19 & HK20 & Hav6 & Hpr6 & Hrg6).
clear Q2 Q9 Q18 Q19 Q20 Q22 M56 M80 M64 Mbuf.
lazymatch type of HS with st_ok _ ?Ev ?ssx (restrict _ ?msX) =>
let kk := eval vm_compute in (run_K 0 (SOff 32 0) [] ssx) in
let nrs := eval vm_compute in (length (ss_mem ssx)) in
let idxs := eval vm_compute in (List.seq 1 (nrs - 1)) in
jafter_stretch_keep HS kk regs6 (mrestrict (w_H W3) mem6) RWDB_CLOB 0x8a00c idxs HS2;
lazymatch type of HS2 with _ -> Forall _ ?rs -> _ =>
assert (HRK : Forall (fun r => 0 <= base_val Ev (YQ0b.r_base r) + YQ0b.r_lo r /\ base_val Ev (YQ0b.r_base r) + YQ0b.r_hi r <= 2 ^ 64 /\
(base_val Ev (YQ0b.r_base r) + YQ0b.r_hi r <= spZ regs - 320 - 16 \/ spZ regs - 320 <= base_val Ev (YQ0b.r_base r) + YQ0b.r_lo r)) rs);
[ repeat apply Forall_cons; try apply Forall_nil; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
rewrite ?RF, ?E70, ?E600; rewrite ?(AG 2%nat), ?(AG 10%nat), ?(AG 11%nat), ?(AG 32%nat) by lia; rewrite ?Usp, ?E10, ?E11, ?E32;
rewrite ?unsigned_lit_small by (unfold SB; lia);
unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob, A_GOT_rawadd, CGIF_SIZE, SB;
clear - HFceil HFhigh HF8lo HF8hi Hceil Hslo Hshi H47 Hrh Hrceil Hgh Hgceil Hfceil Hfhigh Hflo Hfhi C1 C2 C3 C4 C5 FFS Hbb4096;
zone_lia
| specialize (HS2 Hrg6 (regions_kept_out Ev (w_H W3) (ms_mem msX) mem6 (spZ regs - 320 - 16) (spZ regs - 320) _ Hav6 Hpr6 HRK)) ] end end.
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS. rebaseE HS AG HEv. clear HEv.
pose proof (st_ok_pin_reg' trbsegs _ _ _ 26%bv 0 HS ltac:(cbn [ms_regs restrict mkst]; exact HK19) eq_refl) as HS3. clear HS. rename HS3 into HS.
pose proof (st_ok_pin_reg' trbsegs _ _ _ 27%bv 0 HS ltac:(cbn [ms_regs restrict mkst]; exact HK20) eq_refl) as HS3. clear HS. rename HS3 into HS.
norm_ss HS. relowC HS AG E10 E11 E32 E10n E11n E32n. reshok_bx HS 40%nat.
aj_run_to_tok trbtbl_lib_ok HS HJ6 SHOK RABspan 0x8a014; [awrRA AG fpos F EFA3|]. clear_frames.
tailG3 HS HJ6 AG E70 Hfin3 EFA3 F fpos RG3 Hk3 EK HK1r HK1s E600 E601 HPerm3 Hbb4096 HM Abb Tbb E10 E11 E32 E10n E11n E32n.
Qed.
Lemma ra_G : ra_from B ss_G3 (INV_T0 B) -> ra_from B ss_G2 (INV_T0 B).
Proof. exact ra_G_aux. Qed.
End b.
End a.
