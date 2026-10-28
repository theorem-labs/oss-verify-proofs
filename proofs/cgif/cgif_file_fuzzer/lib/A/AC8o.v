(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI08 YI0t YI0m YI0n YI0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0s YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCbw YCbx.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0y YC4a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC80 YC1f YC1g YC81 YC4b.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC98.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC8a AC93 AC9g AC95 AC91 AC99 AC92 AC9b AC8f AC8c AC96 AC9j AC9h AC9i AC9c AC9d AC9e AC94 AC97.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC88 YC5d YC7y.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC8k.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Context {PI : PAImg lib_asan3_1_listing}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ lib_asan3_1_listing PI) (@pa_relro_lo _ lib_asan3_1_listing PI) (@pa_relro_hi _ lib_asan3_1_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_1_listing PI).
#[local] Notation VAL := (@pa_val _ lib_asan3_1_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_asan3_1_listing PI).
#[local] Notation BASE := (@pa_val _ lib_asan3_1_listing PI A_TEXT).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Section S.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ML : model_laws (as_universe B).
Variable MT : ameter_ops.
Hypothesis MLAW : ameter_laws MT.
Hypothesis AFREE4 : afree04_rule SEGS B MT.
Hypothesis AFREEN4 : afree_null04_rule SEGS B MT.
Variable XN : xnums.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL. Let HBfree := pal_free B TL. Let HBmalloc := pal_malloc B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_asan3_1) (PI := PI).
Hypothesis HUL : forall t, In t (lzw_traces (as_code B) BASE) -> In t (as_universe B).
Let PBASE := @pa_B_ok _ _ PI. Let PBLO := @pa_base_lo _ _ PL_asan3_1 PI.
Lemma tlzw_fail_postX : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs pR nP idl icl ly2 S2 W2 regs2 mem2 md2 k2 res (PIX : list Z) (m : Z),
tlzw_caller B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs pR nP idl icl ->
ajournal SEGS B LZW_TSTK (spZ regs) [] lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 k2 -> k2 <= LZW_EV ->
aregs_preserved regs regs2 -> getr regs2 10 = w64 res -> res = 5 -> frames S2 = frames Sc ->
Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) ->
lzw_vnone idl icl PIX -> mo_le MT Sc S2 m -> m <= xn_lzw XN nP idl ->
tlzw_postX SEGS B MT XN STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs pR nP idl icl PIX W2 (mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs pR nP idl icl ly2 S2 W2 regs2 mem2 md2 k2 res PIX m
(HJc & Hra0 & Hgp & Htp & Hal16 & Hwlo & Hwhi & HpR8 & HpRside & HpR0 & HpR63 & HpRw & HpRok & HnP & Hidl & Hicl & Hev & Hlive)
HJ2 Hk2 HP Ha0 Hres Hfrs HPerm HVN HMLE HMle.
pose proof pa_segs_low as Hsegs. assert (HEV : LZW_EV = 19) by reflexivity.
exists ly2, S2, regs2, mem2, md2, res. split; [reflexivity|].
split.
{ eapply ajournal_mono_k.
{ change own with ([] ++ own). eapply (ajournal_sub SEGS B LAWS Hsegs); [exact HJc | exact HJ2 | exact Hwlo | exact Hwhi |].
intros a (r & Hr & _). destruct Hr. }
rewrite HEV. lia. }
split; [exact HP|]. split; [exact Ha0|]. split; [exact Hfrs|].
split; [exact (mle_weaken MT _ _ _ _ MLAW HMLE HMle)|].
right. split; [exact Hres|]. split; [exact HPerm|]. split; [exact HVN|].
split; [eapply tlzw_kept_of_journal; [exact HJ2 | intros b Hb; eapply Permutation_in; [apply Permutation_sym; exact HPerm | exact Hb]]|].
intros a Ha. eapply tlzw_pR_kept_of_journal; [exact HJ2 | exact HpRok | exact HpRside | exact HpR63 | lia].
Qed.
Lemma teidx_failX : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs cx ly7 S7 W7
(regs' : bvmap 5 word) mem' md' lp dp mp (PIX : list Z) (T acc : Z),
lzw_loop_ctx B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs cx ly7 S7 ->
ajournal SEGS B LZW_TSTK (z_sp cx) [] lyc Sc W memc mdc [] ly7 S7 W7 mem' md' 7 ->
alzw_regs_core regs' cx ->
agen_at (mrestrict (w_H W7) mem') cx lp dp mp -> 0 <= lp <= 2 ^ 27 - 2 -> 4 <= dp <= 4096 -> 1 <= mp <= 2047 ->
alzw_slots (mrestrict (w_H W7) mem') cx -> alzw_sslots (mrestrict (w_H W7) mem') cx -> tlzw_frame (mrestrict (w_H W7) mem') (z_sp cx) regs ->
lzw_vnone (z_idl cx) (z_icl cx) PIX ->
mo_ok MT Sc T -> mo_le MT Sc S7 acc -> 0 <= acc -> acc + 7 * mo_free MT <= T -> acc + 7 * mo_free MT <= xn_lzw XN (z_nP cx) (z_idl cx) ->
SRr SEGS W7 (mkCfg (mkst regs' (Z_to_bv 64 (BASE + PC_EIDX)) mem' (seg_rom SEGS)) md')
(tlzw_postX SEGS B MT XN STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs (z_pR cx) (z_nP cx) (z_idl cx) (z_icl cx) PIX).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs cx ly7 S7 W7 regs' mem' md' lp dp mp PIX T acc
(HC & Hzsp & Hzgp & Hztp & HCX & HRG & HSEP & (HBg & HBi & HBt) & HTOK & HB7 & Hfrs7 & Hnev7) HJ HFC HG Hlp Hdp Hmp HSL HSS HFR
HVN HT MACC Hacc0 HaccT HaccN.
pose proof HC as (HJc & Hra0 & Hgp & Htp & Hal16 & Hwlo & Hwhi & HpR8 & HpRside & HpR0 & HpR63 & HpRw & HpRok & HnP & Hidl & Hicl & Hev & Hlive).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO. pose proof HJ as (HAR & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HTS : LZW_TSTK = 336 + ASTACK) by reflexivity. assert (ASTACK = 16384) as Has by reflexivity.
assert (HEV : LZW_EV = 19) by reflexivity.
pose proof HCX as (Hidl' & HnP' & HMR & HMR0 & Hicl' & Hal16' & Hsplo & Hsphi & HpR0' & HpR47 & HpR8' & Hgp' & Htp' & EMR).
pose proof (acx_tabs_nz cx HRG) as Hnz.
pose proof HRG as (HR & Hbi0 & Hbi1 & Hbi2 & Hbi3). cbn [ranges acx_tabs lzw_tabs app] in HR.
destruct HR as ((Rld1 & Rld2 & Rld3 & Rld4) & (Rti1 & Rti2 & Rti3 & Rti4) & (Rlm1 & Rlm2 & Rlm3 & _) & (Rlc1 & Rlc2 & Rlc3 & _) & (Rli1 & Rli2 & Rli3 & _) &
(Rtm1 & Rtm2 & Rtm3 & Rtm4) & (Rg1 & Rg2 & Rg3 & _) & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ (z_ctx cx) 72 HAR HBg) as (_ & _ & _ & _ & Hcpres & _). change (req_size 72) with 72 in Hcpres.
rewrite ?C1, ?C2, ?C3, ?C4 in *. clear C2 C3 C4.
pose proof HB7 as HB7'. unfold acx_tabs, lzw_tabs in HB7', Hnz. pose proof HTOK as HTOK'. unfold acx_tok, acx_tabs, lzw_tabs in HTOK'.
remember (Eimg (Ereg regs' (acx_extra cx lp dp mp regs ++ []))) as E eqn:HE0. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
pose proof (AE_sp regs' cx lp dp mp regs [] HFC) as HE2. pose proof (AE_ctx regs' cx lp dp mp regs [] HFC) as HE8.
pose proof (AE_SB regs' cx lp dp mp regs [] HFC) as HE20. pose proof (AE_gp regs' cx lp dp mp regs [] HFC) as HE3. pose proof (AE_tp regs' cx lp dp mp regs [] HFC) as HE4.
rewrite <- HE0 in HE2, HE8, HE20, HE3, HE4.
assert (HS : st_ok_pi SEGS VAL E (alzw_ss PC_EIDX sr_atoms false false [] [] [] []) (restrict (w_H W7) (mkst regs' (Z_to_bv 64 (BASE + PC_EIDX)) mem' (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. rewrite HE0. apply (alzw_st_ok cx regs' regs lp dp mp [] (mrestrict (w_H W7) mem') _ sr_atoms false false); rewrite <- ?HE0.
- exact HCX. - exact HRG. - exact HFC. - exact HG. - exact HSL. - exact HSS. - exact HFR.
- intros X0; discriminate X0. - intros X0; discriminate X0.
- lia. - lia. - lia.
- rewrite HE0. apply regs_ok_Eimg_Ereg.
- vm_compute; reflexivity.
- apply Forall_nil. - exact I. - exact I. - exact I. - exact I. - exact I. - exact I. }
assert (AG : forall n, (n < 33)%nat -> ew E n = ew E n) by (intros; reflexivity).
change mem' with (ms_mem (mkst regs' (Z_to_bv 64 (BASE + PC_EIDX)) mem' (seg_rom SEGS))) in HJ.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts alzw_ss] in HS.
shok_auto SHOK (SOff 27 0) E (mrestrict (w_H W7) (ms_mem (mkst regs' (Z_to_bv 64 (BASE + PC_EIDX)) mem' (seg_rom SEGS)))).
paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x2138; [awr_ok_tac|]. mem_eq_ro HF. clear HFr.
try match goal with H : mem_grows _ _ |- _ => clear H end.
prreg HS (2%bv : bv 5) R2; prreg HS (3%bv : bv 5) R3; prreg HS (4%bv : bv 5) R4; prreg HS (8%bv : bv 5) R8; prreg HS (9%bv : bv 5) R9;
prreg HS (18%bv : bv 5) R18; prreg HS (19%bv : bv 5) R19; prreg HS (20%bv : bv 5) R20; prreg HS (21%bv : bv 5) R21;
prreg HS (22%bv : bv 5) R22; prreg HS (1%bv : bv 5) R1; prreg HS (27%bv : bv 5) R27.
rewrite (st_ok_restrict_mkst SEGS _ _ _ _ HS eq_refl); cbn [ss_pc].
pose proof HG as (V0 & V8 & V16 & V24 & V32 & V40 & _).
pose proof HFC as (Gsp & G8 & G9 & G18 & G19 & G20 & G21 & G22 & G25 & G26 & G27 & G1 & G3 & G4).
lazymatch type of HJ with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem ?msX) ?mdX _ =>
eapply SRr_mono;
[ eapply (tlzw_cleanX B TL LAWS MT MLAW AFREE4 AFREEN4 ltac:(pHUL) W7 (ms_regs msX) (ms_mem msX) mdX regs LZW_TSTK (z_sp cx) [] lyc Sc W memc mdc [] ly7 S7 7
(z_ctx cx) (z_ti cx) (2 * z_idl cx * z_idl cx) (z_lm cx) 8192 (z_lc cx) 4096 (z_li cx) 8192 (z_tm cx) (4098 * z_idl cx) (z_ld cx) (2 * (lzw_MR (z_nP cx) (z_idl cx) + z_nP cx + 2)) (ablocks B lyc Sc) 5 T acc Sc HJ);
[ first [ rewrite (tnz_id _ Hnz); exact HB7' | idtac "BR0" ]
| first [ rewrite (tnz_id _ Hnz); intros b Hb; exact (proj1 (proj2 (proj2 (HTOK' b Hb)))) | idtac "BRtok" ]
| first [ intros b Hb; cbv [In] in Hb; repeat (destruct Hb as [<-|Hb]; [cbn [fst]; lia|]); destruct Hb | idtac "BR1" ]
| first [ exact V0 | idtac "BR2" ]
| first [ exact V8 | idtac "BR3" ]
| first [ exact V16 | idtac "BR4" ]
| first [ exact V24 | idtac "BR5" ]
| first [ exact V32 | idtac "BR6" ]
| first [ exact V40 | idtac "BR7" ]
| first [ exact Hra0 | idtac "BR8" ]
| first [ exact Hal16 | idtac "BR9" ]
| first [ rewrite <- Hzsp; lia | idtac "BR10" ]
| first [ rewrite <- Hzsp; lia | idtac "BR11" ]
| first [ exact Hgp | idtac "BR12" ]
| first [ exact Htp | idtac "BR13" ]
| first [ rewrite <- Hzsp; unfold spZ; rewrite R2, HE2, unsigned_lit_small by lia; lia | match goal with |- ?g => idtac "BR14" g end ]
| first [ rewrite R3, HE3, Hzgp; symmetry; exact Hgp | idtac "BR15" ]
| first [ rewrite R4, HE4, Hztp; symmetry; exact Htp | idtac "BR16" ]
| first [ rewrite R8, HE8; reflexivity | idtac "BR17" ]
| first [ rewrite R27, HE20; reflexivity | idtac "BR18" ]
| first [ rewrite R21; reflexivity | idtac "BR19" ]
| first [ lia | idtac "BR20" ]
| first [ rewrite R22, HE0, Eimg_low, (ew_Ereg_nat regs' _ 22 22%bv eq_refl) by (unfold A_TEXT; lia); exact G22 | match goal with |- ?g => idtac "BR21" g end ]
| first [ rewrite R20, HE0, Eimg_low, (ew_Ereg_nat regs' _ 20 20%bv eq_refl) by (unfold A_TEXT; lia); exact G20 | match goal with |- ?g => idtac "BR22" g end ]
| first [ rewrite R19, HE0, Eimg_low, (ew_Ereg_nat regs' _ 19 19%bv eq_refl) by (unfold A_TEXT; lia); exact G19 | match goal with |- ?g => idtac "BR23" g end ]
| first [ rewrite R18, HE0, Eimg_low, (ew_Ereg_nat regs' _ 18 18%bv eq_refl) by (unfold A_TEXT; lia); exact G18 | match goal with |- ?g => idtac "BR24" g end ]
| first [ rewrite R9, HE0, Eimg_low, (ew_Ereg_nat regs' _ 9 9%bv eq_refl) by (unfold A_TEXT; lia); exact G9 | rewrite R9, HE8, unsigned_lit_small by lia; reflexivity | match goal with |- ?g => idtac "BR25" g end ]
| first [ rewrite R1, HE0, Eimg_low, (ew_Ereg_nat regs' _ 1 1%bv eq_refl) by (unfold A_TEXT; lia); exact G1 | rewrite R1, HE8, unsigned_lit_small by lia; reflexivity | match goal with |- ?g => idtac "BR26" g end ]
| first [ rewrite <- Hzsp; exact HFR | idtac "BR27" ]
| first [ clear - Hnev7 Hev HEV; lia | idtac "BR28" ]
|   exact HT | exact MACC | exact Hacc0 | exact HaccT ]
| ] end.
cbv beta; intros W12 c12 _ (ly12 & S12 & regs12 & mem12 & md12 & -> & HJ12 & HP12 & Ha12 & Hfrs12 & HPerm12 & _ & MACC12).
rewrite Hzsp in HJ12.
eapply (tlzw_fail_postX STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs (z_pR cx) (z_nP cx) (z_idl cx) (z_icl cx));
[exact HC | exact HJ12 | rewrite HEV; lia | exact HP12 | exact Ha12 | reflexivity | rewrite Hfrs12; exact Hfrs7 | exact HPerm12
| exact HVN | exact MACC12 | exact HaccN].
Qed.
End S.
End d.
End c.
