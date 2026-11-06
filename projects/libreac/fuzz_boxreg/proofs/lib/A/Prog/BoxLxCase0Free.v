(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a phase of the entry function LLVMFuzzerTestOneInput on fuzz_grant.asan (GrantEntryUnset), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/GrantEntryUnset.v, with its module paths, module names and numbers changed; 438 of its 509 lines of code are new or changed and 734 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/A/Prog/BoxLxCase0Defs.v; 161 of its 203 lines of code are new or changed and 467 lines of the source are left out. *)
(* The end of LLVMFuzzerTestOneInput's case 0 (fuzz_boxreg.c:284-285) on the ASan build: from the cut F (0x80aa4,
   BoxLxCase0Defs.v) `ld a0, 0x58(s1)` loads the name and `jal 0x523e8` (__interceptor_trampoline_free, return address
   BASE + 0xb60, a site of gb_base's GB_FSITES) frees it under afree04_rule; then `li a0, -1; srli s5, a0, 32` sets
   s5 = 2^32 - 1 (ren = -1) and the run is at the join 0x80ab4, where GI_K holds: the name's block is gone, so the
   blocks are the caller's and r again (gblk1), one more event, and the spending acc + mo_free MT stays under
   GB_A (i + 1). *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YI16 YC5d YM05 YG0s YImgTop.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal BoxSyms BoxList BoxPa BoxPaLib BoxBase.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import YC4b YC1g YC1h YC85 BoxFrame BoxCJ BoxRo.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import ReacBoxregInit BoxLxDefs ReadName.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Boxreg BoxregUpd LLVMFuzzerTestOneInput_inv.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require LLVMFuzzerTestOneInput_case0 LLVMFuzzerTestOneInput_rn.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require read_name_c reac_boxreg_declare_c.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import BoxLxCase0Defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* The slot 0x58 (the name), the one window the walk to the free call reads; the shadow base for the runner. *)
Definition C0F_SB : Z := 0x7fff8000.
Definition C0F_R58 : YP09.region := YP09.mkRegion (Some 9%nat) 0x58 0x60 0 0 [YP09.mkChunk 0x58 (CVal 8 (SOff 32 0))].

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg box_listing}.
#[local] Notation SEGS := (@pa_segs _ box_listing PI).
#[local] Notation VAL := (@pa_val _ box_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ box_listing PI).
#[local] Notation BASE := (@pa_val _ box_listing PI A_TEXT).
Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis MTL : ameter_laws MT.
Hypothesis AFREE4 : afree04_rule SEGS B MT.

Theorem c0_free : forall i POST, gb_from B MT POST (GI_K B MT i) -> gb_from B MT POST (C0_F B MT i).
Proof.
intros i POST HK cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO HI.
destruct HI as (r & bs & bs' & pos & nm & nn & HMS & HMF & Hi & Hk & Hnn & Hacc & HBL & Hnm & HREG & HINV & HINV' & HFAB & HKEPT & HCUR & H58 & R20 & R25).
pose proof HMS as (_ & _ & _ & _ & _ & _ & (G2 & G8 & G9 & G3 & G4 & G18 & G24)).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBok.
pose proof (pa_base_lo (PL := PL_box) (PI := PI)) as HBLO.
pose proof (c0_sp cx HB) as (Hsp & Hsp1 & Hsp32 & Hsp16). unfold GB_STK in Hsp.
pose proof asan_consts as (C1 & _).
assert (Hnm64 : 0 <= nm < 2 ^ 64).
{ pose proof HJ as (HAR & _). assert (Hin : In (nm, nn) (ablocks B ly3 S3)) by (rewrite HBL; apply in_or_app; right; right; left; reflexivity).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & _ & Hc & _). pose proof (req_size_pos nn ltac:(lia)). lia. }
set (E := Eimg (Ereg (ms_regs ms3) [Z_to_bv 64 nm])).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall q (r : bv 5), Z.of_nat q = bv_unsigned r -> ew E q = getr (ms_regs ms3) r)
  by (intros q r0 Hq; subst E; apply ew_Eimg_Ereg_nat; exact Hq).
assert (F32 : ew E 32 = Z_to_bv 64 nm) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 0)).
assert (U9 : bv_unsigned (ew E 9) = c_sp1 cx) by (rewrite (EE 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; lia).
assert (HS : st_ok_pi SEGS VAL E (mkSS GC_F sr_atoms [C0F_R58] None (mkFacts [] [] [])) (restrict (w_H W3) ms3)).
{ rewrite (c0_mkst cx fp GC_F ms3 (w_H W3) HMS). apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold region_ok, C0F_R58. cbv zeta.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS _ _ _ 0x58 8%N (SOff 32 0) nm); [rewrite c0_denot_off0; exact F32 | cbn; lia | cbn; lia |].
    apply (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3)). exact H58.
  - cbn. repeat split.
  - split; [exact I | split; exact I]. }

assert (SHOK : sh_ok SEGS (SLit C0F_SB) [] E (mrestrict (w_H W3) (ms_mem ms3))) by constructor.
paj_run_tok (paj_run B LAWS) HS HJ SHOK (C0F_SB, C0F_SB + 2 ^ 44 - 1); [awr_ok_tac|].
assert (M1 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W3) (ms_mem ms) a = aview SEGS (w_H W3) (ms_mem ms3) a).
{ intros a Ha. apply (c0_keep_outside E _ _ _ (w_H W3) a HF Ha). cbn. intros (rr & [<- | []] & Hb). cbn in Hb. lia. }
clear HF HFr HG.
assert (HAE : env_agree 32 (Ereg (ms_regs ms3) [Z_to_bv 64 nm]) E) by (split; [intros q Hq; subst E; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (KP1 : forall r0 : bv 5, acallee_saved (bv_unsigned r0) -> getr (ms_regs ms) r0 = getr (ms_regs ms3) r0)
  by (intros r0 Hr; exact (regs_kept_of_st_ok SEGS E _ (restrict (w_H W3) ms) (ms_regs ms3) _ c0_csl HS HAE ltac:(vm_compute; reflexivity) r0 (c0_cs_in r0 Hr))).
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10.
rewrite (pal_free B TL).

assert (Usp : spZ (ms_regs ms) = c_sp1 cx) by (unfold spZ; rewrite Q2, (EE 2%nat 2%bv eq_refl), G2; unfold w64; apply unsigned_lit_small; lia).
pose proof HB as (HPRE0 & _ & _ & _ & _ & _ & Hev & Hlive & _ & _ & _ & _ & _ & HMOK & HTR & HNEED).
pose proof HPRE0 as (_ & _ & _ & Hgp & Htp & _).
pose proof HJ as (HAR3 & _).
pose proof (c0_geo LAWS cx fp k ly3 S3 W3 _ _ HB HJ HFR) as (Hinp & EgF & HF0 & HF1 & HF64 & HSH).
assert (ZR : forall a, c0_zone cx fp a -> 0 <= a < 2 ^ 64) by (intros a; apply c0_zone_range; first [exact Hinp | lia | exact HSH]).
assert (Hnmin : In (nm, nn) (ablocks B ly3 S3)) by (rewrite HBL; apply in_or_app; right; right; left; reflexivity).
assert (HMF1 : c0_mf i cx fp W3 ms r bs) by (apply (c0_mf_keep i cx fp W3 ms3 ms r bs HB); [intros a Ha; apply M1; exact (ZR a Ha) | exact HMF]).
assert (HCH : achain ly3 (aview SEGS (w_H W3) (ms_mem ms)) (c_sp1 cx) (spZ (c_regs cx)) (gch cx)).
{ apply (c0_achain cx fp k ly3 S3 W3 _ _ _ HB HJ); [| lia]. exact (proj1 HMF1). }
eapply SRr_bind.
{ eapply (afree04_sub SEGS B LAWS pa_segs_low MT AFREE4 W3 (ms_regs ms) (ms_mem ms) GB_STK (spZ (c_regs cx)) []
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(GB_CID, fp)] ly3 S3 _ k nm nn (c_sp1 cx - spZ (c_regs cx))
    (Z_to_bv 64 (BASE + 2912)) (gch cx) HJ Hnmin).
  - rewrite Q10, F32. reflexivity.
  - rewrite Usp. lia.
  - apply c0_sub_mod16; [exact Hsp32 | exact Hsp16].
  - lia.
  - change ASTACK with 16384. unfold GB_STK. lia.
  - rewrite Q3, (EE 3%nat 3%bv eq_refl), G3. exact Hgp.
  - rewrite Q4, (EE 4%nat 4%bv eq_refl), G4. exact Htp.
  - exact Q1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - pose proof (c0_nev cx fp k ly3 S3 W3 _ _ HB ltac:(lia) HJ). lia.
  - apply (achain_chain_pre ly3 _ (c_sp1 cx) (spZ (c_regs cx)) (gch cx) (ms_regs ms) HCH).
    + rewrite Usp. lia.
    + unfold s0Z. rewrite Q8, (EE 8%nat 8%bv eq_refl), G8. unfold w64. apply unsigned_lit_small. lia.
    + unfold raZ. rewrite Q1, unsigned_lit_small by lia. lia.
  - apply HTR. right. split; [reflexivity|]. unfold raZ. rewrite Q1, unsigned_lit_small by lia.
    replace (BASE + 2912 - BASE) with 2912 by lia. unfold GB_FSITES. cbn [In]. auto.
  - intros Hc. exfalso. apply in_split in Hc as (l1 & l2 & El).
    apply (c0_blk_twice LAWS ly3 S3 W3 _ _ l1 (l2 ++ [(r, REG_SIZE)]) [] (nm, nn) HAR3); [|cbn [snd]; lia].
    rewrite HBL, El. rewrite <- !app_assoc. reflexivity.
  - destruct (c0_budget i nn acc MTL Hi Hnn Hacc) as (Hb1 & Hb2). pose proof (mo_free_nonneg MT MTL).
    apply (mok_station MT (c_S cx) S3 (c_T cx) acc (mo_free MT) MTL HMOK HMO); [apply (mo_free_nonneg MT MTL) | lia]. }
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & (l1 & l2 & Eab & Eab2) & Hfrs2 & HK2 & MLE2 & HJ1).

assert (Hnot : ~ In (nm, nn) (ablocks B (c_ly cx) (c_S cx) ++ [(r, REG_SIZE)])).
{ intros Hc. apply in_split in Hc as (q1 & q2 & Eq).
  apply (c0_blk_twice LAWS ly3 S3 W3 _ _ q1 q2 [] (nm, nn) HAR3); [|cbn [snd]; lia].
  rewrite HBL. change [(r, REG_SIZE); (nm, nn)] with ([(r, REG_SIZE)] ++ [(nm, nn)]). rewrite app_assoc, Eq.
  rewrite <- app_assoc. reflexivity. }
assert (Ebl : (ablocks B (c_ly cx) (c_S cx) ++ [(r, REG_SIZE)]) ++ [(nm, nn)] = l1 ++ (nm, nn) :: l2)
  by (rewrite <- app_assoc; rewrite <- Eab, HBL; reflexivity).
destruct (c0_last_split _ _ _ _ Ebl Hnot) as (El1 & El2). subst l1 l2. rewrite app_nil_r in Eab2.
assert (Hsub3 : forall p n, In (p, n) (ablocks B (c_ly cx) (c_S cx)) -> In (p, n) (ablocks B ly3 S3))
  by (intros p n Hp; rewrite HBL; apply in_or_app; left; exact Hp).
assert (HNB : c0_newblk B cx ly3 S3 (fun a => nm <= a < nm + req_size nn)).
{ intros a Ha. exists nm, nn. split; [exact Hnmin|]. split; [|exact Ha].
  intros Hc. apply Hnot. apply in_or_app. left. exact Hc. }
replace (spZ (c_regs cx) + (c_sp1 cx - spZ (c_regs cx))) with (c_sp1 cx) in HK2 by lia.
pose proof (c0_zone_acall LAWS cx fp k ly3 S3 W3 (ms_mem ms) _ W2 mem2 _ _ HB HJ HFR Hsub3 HNB HK2) as KZ.

set (E2 := Eimg (Ereg regs2 [])).
assert (HEI2 : img_env VAL A_LIM E2) by (subst E2; apply Eimg_env).
assert (EE2 : forall q (r : bv 5), Z.of_nat q = bv_unsigned r -> ew E2 q = getr regs2 r)
  by (intros q r0 Hq; subst E2; apply ew_Eimg_Ereg_nat; exact Hq).
assert (HS2 : st_ok_pi SEGS VAL E2 (mkSS 0xb60 sr_atoms [] None (mkFacts [] [] []))
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + 2912)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor.
  - exact I.
  - split; [exact I | split; exact I]. }
assert (SHOK2 : sh_ok SEGS (SLit C0F_SB) [] E2 (mrestrict (w_H W2) mem2)) by constructor.
clear HS SHOK.
paj_run_to_tok (paj_run_to B LAWS) HS2 HJ2 SHOK2 (C0F_SB, C0F_SB + 2 ^ 44 - 1) GP_K; [awr_ok_tac|].

assert (M2 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W2) (ms_mem ms0) a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha. apply (c0_keep_outside E2 _ _ _ (w_H W2) a HF Ha). cbn. intros (rr & [] & _). }
clear HF HFr HG.
assert (KP2 : forall r0 : bv 5, acallee_saved (bv_unsigned r0) -> getr regs2 r0 = getr (ms_regs ms) r0)
  by (intros r0 Hr; pose proof (HP2 (bv_unsigned r0) Hr) as X; rewrite Z_to_bv_bv_unsigned in X; exact X).
assert (HAE2 : env_agree 32 (Ereg regs2 []) E2) by (split; [intros q Hq; subst E2; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (KP3 : forall r0 : bv 5, acallee_saved (bv_unsigned r0) -> bv_unsigned r0 <> 21 -> getr (ms_regs ms0) r0 = getr (ms_regs ms3) r0).
{ intros r0 Hr H21. rewrite <- (KP1 r0 Hr), <- (KP2 r0 Hr).
  exact (regs_kept_of_st_ok_pi E2 _ (restrict (w_H W2) ms0) regs2 _ c0_csl21 HS2 HAE2 ltac:(vm_compute; reflexivity) r0 (c0_cs_in21 r0 Hr H21)). }
prreg HS2 (21%bv : bv 5) T21.
pmkst HS2.

assert (KZall : forall a, c0_zone cx fp a -> aview SEGS (w_H W2) (ms_mem ms0) a = aview SEGS (w_H W3) (ms_mem ms3) a).
{ intros a Ha. rewrite M2 by exact (ZR a Ha). rewrite KZ by exact Ha. apply M1. exact (ZR a Ha). }
assert (HMF2 : c0_mf i cx fp W2 (mkst (ms_regs ms0) (Z_to_bv 64 (BASE + GP_K)) (ms_mem ms0) (seg_rom SEGS)) r bs)
  by exact (c0_mf_keep2 i cx fp W3 W2 ms3 _ r bs HB KZall HMF).
destruct HK2 as (K1 & K2 & _).
assert (Hrin3 : In (r, REG_SIZE) (ablocks B ly3 S3)) by (rewrite HBL; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ r REG_SIZE HAR3 Hrin3) as (_ & Hr4096 & Hrceil & _). change (req_size REG_SIZE) with 288 in Hrceil.
assert (Hrnm : (r, REG_SIZE) <> (nm, nn)) by (intros Ec; apply Hnot; rewrite <- Ec; apply in_or_app; right; left; reflexivity).
pose proof (sep_blocks SEGS B LAWS ly3 S3 W3 _ _ r REG_SIZE nm nn HAR3 Hrin3 Hnmin Hrnm) as Drn.
unfold zdisjoint in Drn. cbn [fst snd] in Drn. change (req_size REG_SIZE) with 288 in Drn.
assert (KR : forall j, 0 <= j < REG_SIZE -> aview SEGS (w_H W2) (ms_mem ms0) (r + j) = aview SEGS (w_H W3) (ms_mem ms3) (r + j)).
{ intros j Hj. unfold REG_SIZE in Hj. rewrite M2 by lia. rewrite (K2 r REG_SIZE j Hrin3) by (change (req_size REG_SIZE) with 288; lia).
  apply M1. lia. }
assert (KS : forall off v, 0 <= off < 0x98 -> gslot cx W3 ms3 off v ->
  gslot cx W2 (mkst (ms_regs ms0) (Z_to_bv 64 (BASE + GP_K)) (ms_mem ms0) (seg_rom SEGS)) off v).
{ intros off v Hoff Hv. unfold gslot in *. cbn [ms_mem mkst]. rewrite <- Hv. apply rdword_ext. intros j Hj.
  rewrite M2 by lia. rewrite K1 by (change ASTACK with 16384; lia). apply M1. lia. }
eapply (HK cx fp (k + 1) (acc + mo_free MT) ly2 S2 W2 (mkst (ms_regs ms0) (Z_to_bv 64 (BASE + 2920)) (ms_mem ms0) (seg_rom SEGS)) _ HB HJ2).
- rewrite Hfrs2. exact HFR.
- exact (mle_station MT (c_S cx) S3 S2 acc (mo_free MT) MTL HMO MLE2).
- unfold GI_K. exists r, bs, bs', (-1), pos.
  pose proof HINV as ((_ & HB1 & _) & _). unfold Boxreg.boxreg_B1 in HB1.
  destruct (c0_budget i nn acc MTL Hi Hnn Hacc) as (Hb1 & _).
  destruct HREG as (_ & HL' & HR').
  destruct HCUR as (Hpos & C88 & C90).
  pose proof HMF2 as (_ & _ & _ & _ & _ & GP2 & GS2 & S682 & _).
  split; [apply (c0_body i cx fp GP_K W2 _ r bs); [apply (c0_ms_mkst21 cx fp GP_K (ms_regs ms0) (ms_regs ms3) (ms_mem ms0) (Z_to_bv 64 0)); [exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HMS)))))) | exact KP3] | exact HMF2]|].
  split; [exact Hi|]. split; [lia|]. split; [exact Hb1|]. split; [unfold gblk1; exact Eab2|].
  split; [split; [rewrite Eab2; apply in_or_app; right; left; reflexivity|]; split; [exact HL'|]; intros j Hj; cbn [ms_mem mkst]; rewrite KR by exact Hj; exact (HR' j Hj)|].
  split; [exact GP2|]. split; [exact HINV|]. split; [exact HINV'|]. split; [exact HFAB|]. split; [exact HKEPT|].
  split; [lia|].
  split; [cbn [ms_regs mkst]; rewrite KP3 by c0_cs; exact R20|].
  split; [cbn [ms_regs mkst]; rewrite T21; reflexivity|].
  split; [cbn [ms_regs mkst]; rewrite KP3 by c0_cs; exact R25|].
  split; [exact GS2|].
  split; [split; [exact Hpos|]; split; [apply KS; [lia | exact C88] | apply KS; [lia | exact C90]]|].
  exact S682.
Qed.

End c.
End b.
End a.
