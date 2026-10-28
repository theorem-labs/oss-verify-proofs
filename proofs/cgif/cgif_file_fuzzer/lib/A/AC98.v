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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC8a AC93 AC9g AC95 AC91 AC99 AC92 AC9b AC8f AC8c AC96 AC9j AC9h AC9i AC9c AC9d AC9e AC94 AC97.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
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
Hypothesis AFREE : afree_realizes SEGS B.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL. Let HBfree := pal_free B TL. Let HBmalloc := pal_malloc B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_asan3_1) (PI := PI).
Hypothesis HUL : forall t, In t (lzw_traces (as_code B) BASE) -> In t (as_universe B).
Let PBASE := @pa_B_ok _ _ PI. Let PBLO := @pa_base_lo _ _ PL_asan3_1 PI.
Definition lzw_loop_ctx (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world SEGS)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
(lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte) (mdc : Model) (k : Z)
(regs : bvmap 5 word) (cx : lzw_acx) (ly7 : alayout) (S7 : astate) : Prop :=
tlzw_caller B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs (z_pR cx) (z_nP cx) (z_idl cx) (z_icl cx) /\
z_sp cx = spZ regs /\ z_gp cx = as_gp B /\ z_tp cx = as_tp B /\
acx_ok cx /\ acx_ranges cx /\ acx_seps cx /\ acx_blk (ablocks B ly7 S7) cx /\ acx_tok cx (ablocks B lyc Sc) /\
Permutation (ablocks B ly7 S7) (acx_tabs cx ++ (z_ctx cx, 72) :: ablocks B lyc Sc) /\
frames S7 = frames Sc /\ st_nev S7 <= st_nev Sc + 7.
Lemma acx_tabs_nz : forall cx, acx_ranges cx -> Forall (fun b => fst b <> 0) (acx_tabs cx).
Proof.
intros cx (HR & _). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). cbn [ranges acx_tabs lzw_tabs app] in HR.
unfold acx_tabs, lzw_tabs. repeat (apply Forall_cons; [cbn [fst]; lia|]). apply Forall_nil.
Qed.
Lemma teidx_fail : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs cx ly7 S7 W7
(regs' : bvmap 5 word) mem' md' lp dp mp,
lzw_loop_ctx STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs cx ly7 S7 ->
ajournal SEGS B LZW_TSTK (z_sp cx) [] lyc Sc W memc mdc [] ly7 S7 W7 mem' md' 7 ->
alzw_regs_core regs' cx ->
agen_at (mrestrict (w_H W7) mem') cx lp dp mp -> 0 <= lp <= 2 ^ 27 - 2 -> 4 <= dp <= 4096 -> 1 <= mp <= 2047 ->
alzw_slots (mrestrict (w_H W7) mem') cx -> alzw_sslots (mrestrict (w_H W7) mem') cx -> tlzw_frame (mrestrict (w_H W7) mem') (z_sp cx) regs ->
SRr SEGS W7 (mkCfg (mkst regs' (Z_to_bv 64 (BASE + PC_EIDX)) mem' (seg_rom SEGS)) md')
(tlzw_post SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs (z_pR cx)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs cx ly7 S7 W7 regs' mem' md' lp dp mp
(HC & Hzsp & Hzgp & Hztp & HCX & HRG & HSEP & (HBg & HBi & HBt) & HTOK & HB7 & Hfrs7 & Hnev7) HJ HFC HG Hlp Hdp Hmp HSL HSS HFR.
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
[ eapply (tlzw_clean B TL LAWS ML AFREE ltac:(pHUL) W7 (ms_regs msX) (ms_mem msX) mdX regs LZW_TSTK (z_sp cx) [] lyc Sc W memc mdc [] ly7 S7 7
(z_ctx cx) (z_ti cx) (2 * z_idl cx * z_idl cx) (z_lm cx) 8192 (z_lc cx) 4096 (z_li cx) 8192 (z_tm cx) (4098 * z_idl cx) (z_ld cx) (2 * (lzw_MR (z_nP cx) (z_idl cx) + z_nP cx + 2)) (ablocks B lyc Sc) 5 HJ);
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
| first [ clear - Hnev7 Hev HEV; lia | idtac "BR28" ] ]
| ] end.
cbv beta; intros W12 c12 _ (ly12 & S12 & regs12 & mem12 & md12 & -> & HJ12 & HP12 & Ha12 & Hfrs12 & HPerm12 & _).
rewrite Hzsp in HJ12.
eapply (tlzw_fail_post B LAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs (z_pR cx) (z_nP cx) (z_idl cx) (z_icl cx));
[exact HC | exact HJ12 | rewrite HEV; lia | exact HP12 | exact Ha12 | right; reflexivity | rewrite Hfrs12; exact Hfrs7 | exact HPerm12].
Qed.
Lemma aentry_st_ok_any : forall E pc sr (regsM : bvmap 5 word) (rs : smem) (G : facts) mem,
regs_ok E sr regsM -> regions_wf rs = true -> Forall (region_ok SEGS E mem) rs -> pairwise_disjoint E rs -> facts_ok E G ->
st_ok_pi SEGS VAL E (mkSS pc sr rs None G) (mkst regsM (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS)).
Proof. intros E pc sr regsM rs G mem Hsr Hwf Hrs Hpd HG. exact (pa_entry_st_ok_full E pc sr regsM rs G mem Hsr Hwf Hrs Hpd HG). Qed.
Lemma epi_saved_chunks : forall E m spe (regs0 : bvmap 5 word),
(forall j, (j < 13)%nat -> ew E (42 + j) = nth j (tsaved_vals regs0) (Z_to_bv 64 0)) ->
tlzw_frame m spe regs0 -> bv_unsigned (ew E 2) = spe ->
Forall (YP09.chunk_ok SEGS E m spe)
(map (fun jp => YP09.mkChunk (- fst (snd jp)) (CVal 8 (SOff (42 + fst jp)%nat 0))) (combine (seq 0 13) TSAVED)).
Proof.
intros E m spe regs0 HSV HFR HE2. unfold tlzw_frame in HFR. rewrite Forall_forall in HFR.
apply Forall_forall. intros ch Hin. apply in_map_iff in Hin as ([j [od r]] & <- & Hin). cbn [fst snd].
pose proof (in_combine_l _ _ _ _ Hin) as Hj. apply in_seq in Hj. pose proof (in_combine_r _ _ _ _ Hin) as Hodr.
assert (Hnth : nth j TSAVED (0, 0%bv) = (od, r)).
{ clear - Hin. cbv [TSAVED combine seq] in Hin.
repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; reflexivity |]). destruct Hin. }
eapply chunk_ok_val.
- cbn [sv_denot]. rewrite (HSV j ltac:(lia)), Z.add_0_r. unfold tsaved_vals.
rewrite (map_nth (fun p => getr regs0 (snd p)) TSAVED (0, 0%bv) j) , Hnth. cbn [snd]. reflexivity.
- pose proof (bv_unsigned_in_range 64 (getr regs0 r)) as Hr. change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hr. exact Hr.
- cbn; lia.
- replace (spe + - od) with (spe - od) by lia. exact (HFR (od, r) Hodr).
Qed.
Lemma tepi_seed : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs cx ly7 S7 W7 (regs' : bvmap 5 word) mem' md' X',
lzw_loop_ctx STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs cx ly7 S7 ->
ajournal SEGS B LZW_TSTK (z_sp cx) [] lyc Sc W memc mdc [] ly7 S7 W7 mem' md' 7 ->
alzw_regs_head regs' cx -> agen_at (mrestrict (w_H W7) mem') cx (la_lp X') (la_dp X') (la_mp X') ->
lzw_inv (z_idl cx) (z_nP cx) X' -> la_s X' = z_nP cx ->
alzw_slots (mrestrict (w_H W7) mem') cx -> alzw_sslots (mrestrict (w_H W7) mem') cx -> tlzw_frame (mrestrict (w_H W7) mem') (z_sp cx) regs ->
lzw_rodata_ok (w_H W7) mem' ->
exists E, tepi_pre B STK sp0 lyc Sc W memc mdc regs (z_pR cx) (z_nP cx) (z_idl cx) (z_icl cx) W7 ly7 S7 regs' mem' md' E
(z_ctx cx) (z_ti cx) (z_lm cx) (z_lc cx) (z_li cx) (z_tm cx) (z_ld cx) (la_lp X').
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs cx ly7 S7 W7 regs' mem' md' X'
(HC & Hzsp & Hzgp & Hztp & HCX & HRG & HSEP & (HBg & HBi & HBt) & HTOK & HB7 & Hfrs7 & Hnev7) HJ HFH HG HI HsN HSL HSS HFR Hrod.
pose proof HC as (HJc & Hra0 & Hgp & Htp & Hal16 & Hwlo & Hwhi & HpR8 & HpRside & HpR0 & HpR63 & HpRw & HpRok & HnP & Hidl & Hicl & Hev & Hlive).
pose proof HJ as (HAR & _). pose proof HFH as (HFX & H30 & H16).
pose proof HFX as (Gsp & G8 & G9 & G18 & G19 & G20 & G21 & G22 & G25 & G26 & G27 & G1 & G3 & G4).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HTS : LZW_TSTK = 336 + ASTACK) by reflexivity. assert (ASTACK = 16384) as Has by reflexivity.
pose proof HCX as (Hidl' & HnP' & HMR & HMR0 & Hicl' & Hal16' & Hsplo & Hsphi & HpR0' & HpR47 & HpR8' & Hgp' & Htp' & EMR).
pose proof (acx_tabs_nz cx HRG) as Hnz.
assert (HBld : In (z_ld cx, 2 * (lzw_MR (z_nP cx) (z_idl cx) + z_nP cx + 2)) (ablocks B ly7 S7)) by (apply HBt; cbv [acx_tabs lzw_tabs]; left; reflexivity).
pose proof HRG as (HR & Hbi0 & Hbi1 & Hbi2 & Hbi3). cbn [ranges acx_tabs lzw_tabs app] in HR.
destruct HR as ((Rld1 & Rld2 & Rld3 & Rld4) & (Rti1 & Rti2 & Rti3 & Rti4) & (Rlm1 & Rlm2 & Rlm3 & _) & (Rlc1 & Rlc2 & Rlc3 & _) & (Rli1 & Rli2 & Rli3 & _) &
(Rtm1 & Rtm2 & Rtm3 & Rtm4) & (Rg1 & Rg2 & Rg3 & _) & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ (z_ctx cx) 72 HAR HBg) as (_ & _ & _ & _ & Hcpres & _). change (req_size 72) with 72 in Hcpres.
destruct (al_blocks _ _ LAWS _ _ _ _ _ (z_ld cx) _ HAR HBld) as (_ & _ & _ & _ & Hldpres & _).
pose proof (maxres_bounds (z_idl cx) (z_nP cx) Hidl ltac:(lia)) as [HMR1 HMR2].
pose proof (req_size_pos (2 * (lzw_MR (z_nP cx) (z_idl cx) + z_nP cx + 2)) ltac:(unfold lzw_MR; lia)) as Hrqld.
rewrite ?C1, ?C2, ?C3, ?C4 in *.
destruct X' as [TI LM LI TM s lp dp mp Cn R]. cbn [la_TI la_LM la_LI la_TM la_s la_lp la_dp la_mp] in *. subst s.
assert (EMR' : lzw_MR (z_nP cx) (z_idl cx) = z_MR cx) by (symmetry; exact EMR). unfold lzw_MR in EMR'. rewrite EMR' in *.
assert (HMRle : z_MR cx <= 26055).
{ assert (z_MR cx * 3838 <= z_MR cx * (4094 - z_idl cx)) by (apply Z.mul_le_mono_nonneg_l; lia). lia. }
pose proof (lp_exit_bound (z_idl cx) (z_nP cx) (z_MR cx) (mkLA TI LM LI TM (z_nP cx) lp dp mp Cn R) ltac:(unfold lzw_par; lia) HI) as Hlpx.
cbn [la_lp] in Hlpx. unfold cap in Hlpx.
set (m := mrestrict (w_H W7) mem') in *.
set (ext := [w64 (z_ld cx); w64 lp; w64 (z_pR cx); w64 (z_icl cx); w64 (z_ld cx + 2 * lp); w64 (z_ti cx); w64 (z_lm cx); w64 (z_lc cx); w64 (z_li cx); w64 (z_tm cx)]
++ tsaved_vals regs).
set (E := Eimg (Ereg (regupd regs' 2%bv (w64 (z_sp cx))) ext)).
assert (E251 : ew E (A_OBJ 10) = Z_to_bv 64 (VAL (A_OBJ 10))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (pa_obj_img 10 ltac:(lia)) as Hob10.
assert (ER : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> r <> 2%bv -> ew E n = getr regs' r).
{ intros n r Hn Hr. subst E. rewrite (ew_Eimg_Ereg_nat _ ext n r Hn). apply getr_other. exact Hr. }
assert (HE2 : ew E 2 = w64 (z_sp cx)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat _ ext 2%nat 2%bv eq_refl); apply getr_same; intros X0; discriminate X0).
assert (ERn : forall i, (i < 32)%nat -> (i <> 2)%nat -> ew E i = getr regs' (Z_to_bv 5 (Z.of_nat i))).
{ intros i Hi Hne. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite ew_Ereg_lt by exact Hi. apply getr_other. intros Heq. apply Hne.
apply (f_equal (@bv_unsigned 5)) in Heq. rewrite Z_to_bv_unsigned in Heq. unfold bv_wrap in Heq. change (bv_modulus 5) with 32 in Heq.
rewrite Z.mod_small in Heq by lia. replace (bv_unsigned (2%bv : bv 5)) with 2 in Heq by reflexivity. lia. }
assert (EX : forall j, (j < 10)%nat -> ew E (32 + j) = nth j ext (Z_to_bv 64 0)) by (intros j Hj; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as HE32. pose proof (EX 1%nat ltac:(lia)) as HE33. pose proof (EX 2%nat ltac:(lia)) as HE34. pose proof (EX 3%nat ltac:(lia)) as HE35. pose proof (EX 4%nat ltac:(lia)) as HE36.
pose proof (EX 5%nat ltac:(lia)) as HE37. pose proof (EX 6%nat ltac:(lia)) as HE38. pose proof (EX 7%nat ltac:(lia)) as HE39. pose proof (EX 8%nat ltac:(lia)) as HE40.
pose proof (EX 9%nat ltac:(lia)) as HE41. cbn [nth ext app Nat.add] in HE32, HE33, HE34, HE35, HE36, HE37, HE38, HE39, HE40, HE41.
assert (HSV : forall j, (j < 13)%nat -> ew E (42 + j)%nat = nth j (tsaved_vals regs) (Z_to_bv 64 0)).
{ intros j Hj. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). replace (42 + j)%nat with (32 + (10 + j))%nat by lia. rewrite ew_Ereg_extra. subst ext.
change (10 + j)%nat with (length [w64 (z_ld cx); w64 lp; w64 (z_pR cx); w64 (z_icl cx); w64 (z_ld cx + 2 * lp); w64 (z_ti cx); w64 (z_lm cx); w64 (z_lc cx); w64 (z_li cx); w64 (z_tm cx)] + j)%nat.
apply app_nth2_plus. }
pose proof (ER 8%nat 8%bv eq_refl ltac:(intros X0; discriminate X0)) as HE8. rewrite G8 in HE8.
pose proof (ER 27%nat 27%bv eq_refl ltac:(intros X0; discriminate X0)) as HE27. rewrite G27 in HE27.
pose proof (ER 25%nat 25%bv eq_refl ltac:(intros X0; discriminate X0)) as HE25. rewrite G25 in HE25.
pose proof (ER 21%nat 21%bv eq_refl ltac:(intros X0; discriminate X0)) as HE21. rewrite G21 in HE21.
pose proof (ER 3%nat 3%bv eq_refl ltac:(intros X0; discriminate X0)) as HE3. rewrite G3 in HE3.
pose proof (ER 4%nat 4%bv eq_refl ltac:(intros X0; discriminate X0)) as HE4. rewrite G4 in HE4.
unfold w64 in *.
exists E. unfold tepi_pre.
split; [rewrite <- Hzsp; exact HJ|].
split.
{
change (st_ok_pi SEGS VAL E ss_epi (restrict (w_H W7) (mkst regs' (Z_to_bv 64 (BASE + PC_EPI)) mem' (seg_rom SEGS)))).
rewrite restrict_mkst_fx. unfold ss_epi. apply aentry_st_ok_any.
-
apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<-|Hr];
[ match goal with |- _ = sv_denot ?Ex (sr_get ?sr ?r) => let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end;
cbn [sv_denot];
first [ rewrite getr_zero; reflexivity
| rewrite HE2, unsigned_lit_small by lia; unfold spZ in Gsp; apply bv_eq; rewrite Gsp, unsigned_lit_small by lia; lia
| rewrite HE8, unsigned_lit_small by lia; first [exact G1 | exact G9 | exact G18 | exact G19 | exact G20 | exact H30]
| rewrite HE8, HE27, !unsigned_lit_small, !Z.add_0_r by (unfold SB; lia); exact G22
| rewrite Z.add_0_r, ERn by lia;
match goal with |- _ = Z_to_bv 64 (bv_unsigned (getr _ ?x)) => let y := eval vm_compute in x in change x with y end;
rewrite Z_to_bv_bv_unsigned; reflexivity
| match goal with |- ?g => idtac "REGSOK" g end ] | ]).
destruct Hr.
- vm_compute. reflexivity.
-
destruct HG as (V0 & V8 & V16 & V24 & V32 & V40 & V48 & V56 & V60 & V64 & V66).
destruct HSL as (S56 & S72 & S88 & S96 & S120 & S144 & S152 & S168 & S176 & S184 & S208).
destruct HSS as (S64 & S80 & S104 & S112 & S128 & S136 & S160 & S192 & S200).
constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
+ unfold region_ok, ctx_region_epi. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite HE8, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; apply (apresent_writable SEGS); apply (proj1 (Hcpres (z_ctx cx + o) ltac:(lia)))|].
Local Ltac ack S HE := eapply chunk_ok_val; [ cbn [sv_denot]; rewrite HE, ?unsigned_lit_small by lia; rewrite ?Z.add_0_r; reflexivity | cbn; lia | cbn; lia | first [exact S | rewrite Z.add_0_r; exact S] ].
constructor; [ack V0 HE37|]. constructor; [ack V8 HE38|]. constructor; [ack V16 HE39|]. constructor; [ack V24 HE40|].
constructor; [ack V32 HE41|]. constructor; [ack V40 HE32|]. constructor; [ack V60 HE33|]. constructor.
+ unfold region_ok, stk_region_epi. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite HE2, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
Local Ltac sck S HE := eapply chunk_ok_val; [ cbn [sv_denot]; rewrite HE, ?unsigned_lit_small by lia; rewrite ?Z.add_0_r; reflexivity | cbn; lia | cbn; lia
| first [exact S | match type of S with val_mem _ _ ?a _ ?v => match goal with |- val_mem _ _ ?a' _ ?v' => replace a' with a by lia; replace v' with v by lia; exact S end end] ].
Local Ltac shck8 S k HE8 HE27 :=
eapply chunk_ok_val; [ eapply (shx_denot _ _ k HE8 HE27); lia | | cbn; lia
| match type of S with val_mem _ _ ?a _ _ => match goal with |- val_mem _ _ ?a' _ _ => replace a' with a by lia; exact S end end ];
[ unfold shadow_word; match goal with |- 0 <= bv_unsigned ?w < _ => let Hr := fresh in pose proof (bv_unsigned_in_range 64 w) as Hr; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hr; exact Hr end ].
constructor; [shck8 S104 60 HE8 HE27|]. constructor; [shck8 S128 40 HE8 HE27|].
constructor; [sck S152 HE34|]. constructor; [sck S176 HE35|]. constructor; [sck S208 HE8|].
apply (epi_saved_chunks E m (z_sp cx) regs HSV HFR). rewrite HE2. apply unsigned_lit_small. lia.
+ unfold region_ok, end_region_epi. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite HE36, unsigned_lit_small by lia. split; [lia|]. split; [lia|].
split; [intros o Ho; apply (apresent_writable SEGS); apply (proj1 (Hldpres (z_ld cx + 2 * lp + o) ltac:(lia))) | constructor].
+ unfold region_ok, rodata_region_epi. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite E251, unsigned_lit_small by (pose proof (pa_val_range (A_OBJ 10)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. eapply chunk_ok_val; [reflexivity | cbv; split; [discriminate | reflexivity] | cbn; lia | rewrite Z.add_0_r; exact Hrod].
-
cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, ctx_region_epi, stk_region_epi, end_region_epi, rodata_region_epi.
cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite HE8, HE2, HE36, E251, !unsigned_lit_small by (first [lia | pose proof (pa_val_range (A_OBJ 10)); lia]).
pose proof (acx_sep _ HSEP 0 6 ltac:(lia) ltac:(lia)) as Hs06; cbv [nth app acx_objs fst snd zz_disj z_tisz z_tmsz z_cap cap] in Hs06.
repeat split; (clear - Hs06 Hlpx Rg1 Rg2 Rld1 Rld2 Hsplo Hsphi C1 HMRle HnP' Hidl' HTS Has EMR EMR' Hob10; zone_lia).
-
split; [| split; [exact I | cbn [alias_ok]; split; [|exact I]]].
+ cbn [atoms_ok f_atoms facts_epi]. ceil; unfold afact_ok, PTR, ASAN_CEIL, kLowShadowBeg, kHighMemBeg. cbn [af_lo af_hi af_al2]. rewrite ?C1, ?C2, ?C3, ?C4.
rewrite HE2, HE8, HE27, HE25, HE32, HE33, HE34, HE35, HE36, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 0) with 1. change (2 ^ 1) with 2. change (2 ^ 3) with 8. change (2 ^ 4) with 16. rewrite !Z.mod_1_r.
repeat split; try (unfold SB; lia).
* apply Z.mod_divide; [lia|]. apply Z.divide_add_r; [| exists lp; lia].
apply (Z.divide_trans _ 16); [exists 8; reflexivity|]. apply Z.mod_divide; [lia | exact Rld3].
+ apply (alias_b2i' E 32 33 36 (z_ld cx) lp HE32 HE33 HE36); lia. }
split; [subst E; apply Eimg_env|].
split; [rewrite HE2, unsigned_lit_small by lia; exact Hzsp|].
split; [rewrite HE3, Hzgp; symmetry; exact Hgp|]. split; [rewrite HE4, Hztp; symmetry; exact Htp|].
repeat (split; [assumption|]).
split; [lia|]. split; [unfold lzw_MR; lia|].
split; [pose proof HB7 as HB7'; unfold acx_tabs in HB7'; exact HB7'|].
split; [pose proof HTOK as HTOK'; unfold acx_tok, acx_tabs in HTOK'; rewrite <- Hzsp; exact HTOK'|].
split; [exact Hfrs7|].
rewrite (blocks_bytes_bsum B ly7 S7), (blocks_bytes_bsum B lyc Sc), (bsum_perm _ _ HB7), bsum_app, bsum_cons. unfold acx_tabs, lzw_tabs, bsum. cbn [fold_right snd]. unfold lzw_MR. lia.
Qed.
End S.
End d.
End c.
