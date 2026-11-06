(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YC02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI01 YI07 YI03 YI04 YI06.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0y YG0d YCcz.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YCe7 YF9i YCeb YCe8 YCdv YCgl YCg2 YCgi YCg4 YCg0 YCfy YCg8 YCg1 YCfz YCga YCdx YCdw YCg5 YCgm YCgj YCgk YCgc YCgd YCgf YCg3 YCg6.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0h.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0h.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section S.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AFREE : afree_realizes trbsegs B.
Let HBcode := tl_code B TL.
Definition lzw_loop_ctx (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world trbsegs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
(lyc : alayout) (Sc : astate) (W : world trbsegs) (memc : word -> option byte) (mdc : Model) (k : Z)
(regs : bvmap 5 word) (cx : lzw_acx) (ly7 : alayout) (S7 : astate) : Prop :=
tlzw_caller B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs (z_pR cx) (z_nP cx) (z_idl cx) (z_icl cx) /\
z_sp cx = spZ regs /\ z_gp cx = as_gp B /\ z_tp cx = as_tp B /\
acx_ok cx /\ acx_ranges cx /\ acx_seps cx /\ acx_blk (ablocks B ly7 S7) cx /\ acx_tok cx (ablocks B lyc Sc) /\
Permutation (ablocks B ly7 S7) (acx_tabs cx ++ (z_ctx cx, 72) :: ablocks B lyc Sc) /\
frames S7 = frames Sc /\ vev S7 <= vev Sc + 7.
Lemma acx_tabs_nz : forall cx, acx_ranges cx -> Forall (fun b => fst b <> 0) (acx_tabs cx).
Proof.
intros cx (HR & _). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). cbn [ranges acx_tabs lzw_tabs app] in HR.
unfold acx_tabs, lzw_tabs. repeat (apply Forall_cons; [cbn [fst]; lia|]). apply Forall_nil.
Qed.
Lemma teidx_fail : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs cx ly7 S7 W7
(regs' : bvmap 5 word) mem' md' lp dp mp,
lzw_loop_ctx STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs cx ly7 S7 ->
ajournal trbsegs B LZW_TSTK (z_sp cx) [] lyc Sc W memc mdc [] ly7 S7 W7 mem' md' 7 ->
alzw_regs_fix regs' cx ->
agen_at (mrestrict (w_H W7) mem') cx lp dp mp -> 0 <= lp <= 2 ^ 27 - 2 -> 4 <= dp <= 4096 -> 1 <= mp <= 2047 ->
alzw_slots (mrestrict (w_H W7) mem') cx -> alzw_sslots (mrestrict (w_H W7) mem') cx -> tlzw_frame (mrestrict (w_H W7) mem') (z_sp cx) regs ->
SRr trbsegs W7 (mkCfg (mkst regs' (Z_to_bv 64 PC_EIDX) mem' (seg_rom trbsegs)) md')
(tlzw_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs (z_pR cx)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs cx ly7 S7 W7 regs' mem' md' lp dp mp
(HC & Hzsp & Hzgp & Hztp & HCX & HRG & HSEP & (HBg & HBi & HBt) & HTOK & HB7 & Hfrs7 & Hnev7) HJ HFX HG Hlp Hdp Hmp HSL HSS HFR.
pose proof (alzw_regs_core_of_fix _ _ HFX) as HFC.
pose proof HC as (HJc & Hra0 & Hgp & Htp & Hal16 & Hwlo & Hwhi & HpR8 & HpRside & HpR0 & HpR63 & HpRw & HpRok & HnP & Hidl & Hicl & Hev & Hlive).
pose proof Hwx_tfa as Hwx. pose proof trb_segs_low as Hsegs. pose proof HJ as (HAR & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HTS : LZW_TSTK = 304 + ASTACK) by reflexivity. assert (ASTACK = 16384) as Has by reflexivity.
assert (HEV : LZW_EV = 19) by reflexivity.
pose proof HCX as (Hidl' & HnP' & HMR & HMR0 & Hicl' & Hal16' & Hsplo & Hsphi & HpR0' & HpR47 & HpR8' & Hgp' & Htp' & EMR).
pose proof (acx_tabs_nz cx HRG) as Hnz.
pose proof HRG as (HR & Hbi0 & Hbi1 & Hbi2 & Hbi3). cbn [ranges acx_tabs lzw_tabs app] in HR.
destruct HR as ((Rld1 & Rld2 & Rld3 & Rld4) & (Rti1 & Rti2 & Rti3 & Rti4) & (Rlm1 & Rlm2 & Rlm3 & _) & (Rlc1 & Rlc2 & Rlc3 & _) & (Rli1 & Rli2 & Rli3 & _) &
(Rtm1 & Rtm2 & Rtm3 & Rtm4) & (Rg1 & Rg2 & Rg3 & _) & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ (z_ctx cx) 72 HAR HBg) as (_ & _ & _ & _ & Hcpres & _). change (req_size 72) with 72 in Hcpres.
rewrite ?C1, ?C2, ?C3, ?C4 in *. clear C2 C3 C4.
pose proof HB7 as HB7'. unfold acx_tabs, lzw_tabs in HB7', Hnz. pose proof HTOK as HTOK'. unfold acx_tok, acx_tabs, lzw_tabs in HTOK'.
remember (Ereg regs' (acx_extra cx lp dp mp regs ++ [])) as E eqn:HE0.
pose proof (AE_sp regs' cx lp dp mp regs [] HFC) as HE2. pose proof (AE_ctx regs' cx lp dp mp regs [] HFC) as HE8.
pose proof (AE_SB regs' cx lp dp mp regs [] HFC) as HE21. pose proof (AE_gp regs' cx lp dp mp regs [] HFC) as HE3. pose proof (AE_tp regs' cx lp dp mp regs [] HFC) as HE4.
rewrite <- HE0 in HE2, HE8, HE21, HE3, HE4.
assert (HS : st_ok trbsegs E (alzw_ss PC_EIDX sr_atoms false false [] [] [] [])
(restrict (w_H W7) (mkst regs' (Z_to_bv 64 PC_EIDX) mem' (seg_rom trbsegs)))).
{ rewrite restrict_mkst_fx. rewrite HE0. apply (alzw_st_ok cx regs' regs lp dp mp [] (mrestrict (w_H W7) mem') _ sr_atoms false false); rewrite <- ?HE0.
- exact HCX. - exact HRG. - exact HFC. - exact HG. - exact HSL. - exact HSS. - exact HFR.
- intros X0; discriminate X0. - intros X0; discriminate X0.
- lia. - lia. - lia.
- rewrite HE0. apply regs_ok_Ereg.
- vm_compute; reflexivity.
- apply Forall_nil. - exact I. - exact I. - exact I. - exact I. - exact I. - exact I. }
assert (AG : forall n, (n < 33)%nat -> ew E n = ew E n) by (intros; reflexivity).
change mem' with (ms_mem (mkst regs' (Z_to_bv 64 PC_EIDX) mem' (seg_rom trbsegs))) in HJ.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts alzw_ss] in HS.
shok_auto SHOK (SOff 23 0) E (mrestrict (w_H W7) (ms_mem (mkst regs' (Z_to_bv 64 PC_EIDX) mem' (seg_rom trbsegs)))).
aj_run_to_tok trbtbl_lib_ok HS HJ SHOK Bspan 0x8b1f4; [awr_ok_tac|]. mem_eq_ro HF. clear HFr.
try match goal with H : mem_grows _ _ |- _ => clear H end.
rreg HS (2%bv : bv 5) R2; rreg HS (3%bv : bv 5) R3; rreg HS (4%bv : bv 5) R4; rreg HS (8%bv : bv 5) R8; rreg HS (21%bv : bv 5) R9;
rreg HS (18%bv : bv 5) R18; rreg HS (19%bv : bv 5) R19; rreg HS (20%bv : bv 5) R20; rreg HS (23%bv : bv 5) R21;
rreg HS (22%bv : bv 5) R22; rreg HS (11%bv : bv 5) R23; rreg HS (9%bv : bv 5) R26.
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl); cbn [ss_pc].
pose proof HG as (V0 & V8 & V16 & V24 & V32 & V40 & _).
pose proof HFX as (Gsp & G8 & G9 & G18 & G19 & G20 & G21 & G22 & G23 & G25 & G3 & G4).
lazymatch type of HJ with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem ?msX) ?mdX _ =>
eapply SRr_mono;
[ eapply (tlzw_clean B TL LAWS ML AFREE W7 (ms_regs msX) (ms_mem msX) mdX regs LZW_TSTK (z_sp cx) [] lyc Sc W memc mdc [] ly7 S7 7
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
| first [ rewrite R21, HE21; reflexivity | idtac "BR18" ]
| first [ rewrite R22; reflexivity | match goal with |- ?g => idtac "BR19" g end ]
| first [ lia | idtac "BR20" ]
| first [ rewrite R9; first [ rewrite HE0, (ew_Ereg_nat regs' _ 21 21%bv eq_refl); exact G9 | rewrite (ew_Ereg_nat regs' _ 21 21%bv eq_refl); exact G9 ]
| match goal with |- ?g => idtac "BR21" g end ]
| first [ rewrite R20; first [ rewrite HE0, (ew_Ereg_nat regs' _ 20 20%bv eq_refl); exact G20 | rewrite (ew_Ereg_nat regs' _ 20 20%bv eq_refl); exact G20 ] | match goal with |- ?g => idtac "BR22" g end ]
| first [ rewrite R19; first [ rewrite HE0, (ew_Ereg_nat regs' _ 19 19%bv eq_refl); exact G19 | rewrite (ew_Ereg_nat regs' _ 19 19%bv eq_refl); exact G19 ] | match goal with |- ?g => idtac "BR23" g end ]
| first [ rewrite R18; first [ rewrite HE0, (ew_Ereg_nat regs' _ 18 18%bv eq_refl); exact G18 | rewrite (ew_Ereg_nat regs' _ 18 18%bv eq_refl); exact G18 ] | match goal with |- ?g => idtac "BR24" g end ]
| first [ rewrite R26, HE8, unsigned_lit_small by lia; reflexivity | match goal with |- ?g => idtac "BR25" g end ]
| first [ rewrite R23, HE8, unsigned_lit_small by lia; reflexivity | match goal with |- ?g => idtac "BR26" g end ]
| first [ rewrite <- Hzsp; exact HFR | idtac "BR27" ]
| first [ clear - Hnev7 Hev HEV; lia | idtac "BR28" ] ]
| ] end.
cbv beta. intros W12 c12 _ (ly12 & S12 & regs12 & mem12 & md12 & -> & HJ12 & HP12 & Ha12 & Hfrs12 & HPerm12 & _).
rewrite Hzsp in HJ12.
eapply (tlzw_fail_post B LAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs (z_pR cx) (z_nP cx) (z_idl cx) (z_icl cx));
[exact HC | exact HJ12 | rewrite HEV; lia | exact HP12 | exact Ha12 | right; reflexivity | rewrite Hfrs12; exact Hfrs7 | exact HPerm12].
Qed.
Lemma aentry_st_ok_any : forall E pc sr (regsM : bvmap 5 word) (rs : smem) (G : facts) mem,
regs_ok E sr regsM -> regions_wf rs = true -> Forall (region_ok trbsegs E mem) rs -> pairwise_disjoint E rs -> facts_ok E G ->
st_ok trbsegs E (mkSS pc sr rs None G) (mkst regsM (Z_to_bv 64 pc) mem (seg_rom trbsegs)).
Proof.
intros E pc sr regsM rs G mem Hsr Hwf Hrs Hpd HG.
unfold st_ok. cbn [ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem mkst ss_pc ss_regs ss_mem ss_resv ss_facts resv_denot].
repeat (split; [reflexivity|]). split; [exact Hsr|]. split; [| exact HG]. split; [exact Hwf|]. split; [exact Hrs | exact Hpd].
Qed.
Lemma epi_saved_chunks : forall E m spe (regs0 : bvmap 5 word),
(forall j, (j < 13)%nat -> ew E (42 + j) = nth j (tsaved_vals regs0) (Z_to_bv 64 0)) ->
tlzw_frame m spe regs0 -> bv_unsigned (ew E 2) = spe ->
Forall (YQ0b.chunk_ok trbsegs E m spe)
(map (fun jp => YQ0b.mkChunk (- fst (snd jp)) (CVal 8 (SOff (42 + fst jp)%nat 0))) (combine (seq 0 13) TSAVED)).
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
ajournal trbsegs B LZW_TSTK (z_sp cx) [] lyc Sc W memc mdc [] ly7 S7 W7 mem' md' 7 ->
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
pose proof HJ as (HAR & _). pose proof HFH as (HFX & H15).
pose proof HFX as (Gsp & G8 & G9 & G18 & G19 & G20 & G21 & G22 & G23 & G25 & G3 & G4).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HTS : LZW_TSTK = 304 + ASTACK) by reflexivity. assert (ASTACK = 16384) as Has by reflexivity.
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
set (E := Ereg (regupd regs' 2%bv (w64 (z_sp cx))) ext).
assert (ER : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> r <> 2%bv -> ew E n = getr regs' r).
{ intros n r Hn Hr. subst E. rewrite (ew_Ereg_nat _ ext n r Hn). apply getr_other. exact Hr. }
assert (HE2 : ew E 2 = w64 (z_sp cx)) by (subst E; rewrite (ew_Ereg_nat _ ext 2%nat 2%bv eq_refl); apply getr_same; intros X0; discriminate X0).
assert (ERn : forall i, (i < 32)%nat -> (i <> 2)%nat -> ew E i = getr regs' (Z_to_bv 5 (Z.of_nat i))).
{ intros i Hi Hne. subst E. rewrite ew_Ereg_lt by exact Hi. apply getr_other. intros Heq. apply Hne.
apply (f_equal (@bv_unsigned 5)) in Heq. rewrite Z_to_bv_unsigned in Heq. unfold bv_wrap in Heq. change (bv_modulus 5) with 32 in Heq.
rewrite Z.mod_small in Heq by lia. replace (bv_unsigned (2%bv : bv 5)) with 2 in Heq by reflexivity. lia. }
assert (EX : forall j, (j < 10)%nat -> ew E (32 + j) = nth j ext (Z_to_bv 64 0)) by (intros j Hj; subst E; apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as HE32. pose proof (EX 1%nat ltac:(lia)) as HE33. pose proof (EX 2%nat ltac:(lia)) as HE34. pose proof (EX 3%nat ltac:(lia)) as HE35. pose proof (EX 4%nat ltac:(lia)) as HE36.
pose proof (EX 5%nat ltac:(lia)) as HE37. pose proof (EX 6%nat ltac:(lia)) as HE38. pose proof (EX 7%nat ltac:(lia)) as HE39. pose proof (EX 8%nat ltac:(lia)) as HE40.
pose proof (EX 9%nat ltac:(lia)) as HE41. cbn [nth ext app Nat.add] in HE32, HE33, HE34, HE35, HE36, HE37, HE38, HE39, HE40, HE41.
assert (HSV : forall j, (j < 13)%nat -> ew E (42 + j)%nat = nth j (tsaved_vals regs) (Z_to_bv 64 0)).
{ intros j Hj. subst E. replace (42 + j)%nat with (32 + (10 + j))%nat by lia. rewrite ew_Ereg_extra. subst ext.
change (10 + j)%nat with (length [w64 (z_ld cx); w64 lp; w64 (z_pR cx); w64 (z_icl cx); w64 (z_ld cx + 2 * lp); w64 (z_ti cx); w64 (z_lm cx); w64 (z_lc cx); w64 (z_li cx); w64 (z_tm cx)] + j)%nat.
apply app_nth2_plus. }
pose proof (ER 8%nat 8%bv eq_refl ltac:(intros X0; discriminate X0)) as HE8. rewrite G8 in HE8.
pose proof (ER 23%nat 23%bv eq_refl ltac:(intros X0; discriminate X0)) as HE21. rewrite G21 in HE21.
pose proof (ER 25%nat 25%bv eq_refl ltac:(intros X0; discriminate X0)) as HE25. rewrite G25 in HE25.
pose proof (ER 22%nat 22%bv eq_refl ltac:(intros X0; discriminate X0)) as HE22. rewrite G22 in HE22.
pose proof (ER 3%nat 3%bv eq_refl ltac:(intros X0; discriminate X0)) as HE3. rewrite G3 in HE3.
pose proof (ER 4%nat 4%bv eq_refl ltac:(intros X0; discriminate X0)) as HE4. rewrite G4 in HE4.
unfold w64 in *.
exists E. unfold tepi_pre.
split; [rewrite <- Hzsp; exact HJ|].
split.
{
change (st_ok trbsegs E ss_epi (restrict (w_H W7) (mkst regs' (Z_to_bv 64 PC_EPI) mem' (seg_rom trbsegs)))).
rewrite restrict_mkst_fx. unfold ss_epi. apply aentry_st_ok_any.
-
apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<-|Hr];
[ match goal with |- _ = sv_denot ?Ex (sr_get ?sr ?r) => let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end;
cbn [sv_denot];
first [ rewrite getr_zero; reflexivity
| rewrite HE2, unsigned_lit_small by lia; unfold spZ in Gsp; apply bv_eq; rewrite Gsp, unsigned_lit_small by lia; lia
| rewrite HE8, HE21, !unsigned_lit_small, !Z.add_0_r by (unfold SB; lia); exact G9
| rewrite HE8, unsigned_lit_small by lia; first [exact G18 | exact G19 | exact G20]
| rewrite Z.add_0_r, ERn by lia;
match goal with |- _ = Z_to_bv 64 (bv_unsigned (getr _ ?x)) => let y := eval vm_compute in x in change x with y end;
rewrite Z_to_bv_bv_unsigned; reflexivity
| match goal with |- ?g => idtac "REGSOK" g end ] | ]).
destruct Hr.
- vm_compute. reflexivity.
-
destruct HG as (V0 & V8 & V16 & V24 & V32 & V40 & V48 & V56 & V60 & V64 & V66).
destruct HSL as (S40 & S48 & S56 & S72 & S88 & S112 & S128 & S136 & S144 & S152 & S184 & S192).
destruct HSS as (S64 & S80 & S96 & S104 & S120 & S160 & S168 & S176).
constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
+ unfold region_ok, ctx_region_epi. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
rewrite HE8, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; apply (apresent_writable trbsegs); apply (proj1 (Hcpres (z_ctx cx + o) ltac:(lia)))|].
Local Ltac ack S HE := eapply chunk_ok_val; [ cbn [sv_denot]; rewrite HE, ?unsigned_lit_small by lia; rewrite ?Z.add_0_r; reflexivity | cbn; lia | cbn; lia | first [exact S | rewrite Z.add_0_r; exact S] ].
constructor; [ack V0 HE37|]. constructor; [ack V8 HE38|]. constructor; [ack V16 HE39|]. constructor; [ack V24 HE40|].
constructor; [ack V32 HE41|]. constructor; [ack V40 HE32|]. constructor; [ack V60 HE33|]. constructor.
+ unfold region_ok, stk_region_epi. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
rewrite HE2, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
Local Ltac sck S HE := eapply chunk_ok_val; [ cbn [sv_denot]; rewrite HE, ?unsigned_lit_small by lia; rewrite ?Z.add_0_r; reflexivity | cbn; lia | cbn; lia
| first [exact S | match type of S with val_mem _ _ ?a _ ?v => match goal with |- val_mem _ _ ?a' _ ?v' => replace a' with a by lia; replace v' with v by lia; exact S end end] ].
Local Ltac shck S k Ev ctxv HE8 HE21 := eapply chunk_ok_val; [ eapply (shx_denot Ev ctxv k HE8 HE21); lia | | cbn; lia
| first [exact S | match type of S with val_mem _ _ ?a _ ?v => match goal with |- val_mem _ _ ?a' _ ?v' => replace a' with a by lia; exact S end end] ];
[ unfold shadow_word; match goal with |- 0 <= bv_unsigned ?w < _ => pose proof (bv_unsigned_in_range 64 w) as Hr; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hr; exact Hr end ].
constructor; [shck S96 40 E (z_ctx cx) HE8 HE21|]. constructor; [shck S120 60 E (z_ctx cx) HE8 HE21|].
constructor; [sck S128 HE8|]. constructor; [sck S144 HE35|]. constructor; [sck S152 HE34|]. constructor; [sck S184 HE8|]. constructor; [sck S192 HE8|].
apply (epi_saved_chunks E m (z_sp cx) regs HSV HFR). rewrite HE2. apply unsigned_lit_small. lia.
+ unfold region_ok, end_region_epi. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
rewrite HE36, unsigned_lit_small by lia. split; [lia|]. split; [lia|].
split; [intros o Ho; apply (apresent_writable trbsegs); apply (proj1 (Hldpres (z_ld cx + 2 * lp + o) ltac:(lia))) | constructor].
+ unfold region_ok, rodata_region_epi. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
unfold A_rodata_magic. split; [cbn; lia|]. split; [cbn; lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. eapply chunk_ok_val; [reflexivity | cbv; split; [discriminate | reflexivity] | cbn; lia | cbn [base_val]; rewrite Z.add_0_l; exact Hrod].
-
cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, ctx_region_epi, stk_region_epi, end_region_epi, rodata_region_epi.
cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]. rewrite HE8, HE2, HE36, !unsigned_lit_small by lia.
pose proof (acx_sep _ HSEP 0 6 ltac:(lia) ltac:(lia)) as Hs06; cbv [nth app acx_objs fst snd zz_disj z_tisz z_tmsz z_cap cap] in Hs06.
unfold A_rodata_magic.
repeat split; (clear - Hs06 Hlpx Rg1 Rg2 Rld1 Rld2 Hsplo Hsphi C1 HMRle HnP' Hidl' HTS Has EMR EMR'; zone_lia).
-
split; [| split; [| cbn [alias_ok f_alias facts_epi facts_epiA]; split; [|exact I]]].
+ cbn [atoms_ok f_atoms facts_epi facts_epiA]. ceil; unfold afact_ok, PTR, ASAN_CEIL, kLowShadowBeg, kHighMemBeg. cbn [af_lo af_hi af_al2]. rewrite ?C1, ?C2, ?C3, ?C4.
rewrite HE2, HE8, HE21, HE25, HE32, HE33, HE34, HE35, HE36, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 0) with 1. change (2 ^ 1) with 2. change (2 ^ 3) with 8. change (2 ^ 4) with 16. rewrite !Z.mod_1_r.
repeat split; try (unfold SB; lia).
* apply Z.mod_divide; [lia|]. apply Z.divide_add_r; [| exists lp; lia].
apply (Z.divide_trans _ 16); [exists 8; reflexivity|]. apply Z.mod_divide; [lia | exact Rld3].
+
cbn [conds_ok f_conds facts_epiA]. split; [apply (cond_geu E 36 0 32 0 (z_ld cx + 2 * lp) (z_ld cx) HE36 HE32); lia | exact I].
+ apply (alias_b2i' E 32 33 36 (z_ld cx) lp HE32 HE33 HE36); lia. }
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
End c.
