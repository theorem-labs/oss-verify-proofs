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
YG00 YG0a YG01 YG0h YG0u YG0d YC04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YC19 YF8z YC1d YC1a YC2o YC10 YC2p YC0x YC1b YC3g YC2u YC39 YC4o YC4q YC46 YC4g YC4c YC4d YC4e YC4f YC4h YC45 YC3t YC3u YC3v YC3w YC3x YC43 YC44 YC3y YC3z YC40 YC41 YC42.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section d.
Variable B : asyms.
Hypothesis TL : TraLib B.
Hypothesis LAWS : AR_laws trasegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AMALLOC : amalloc_realizes trasegs B.
Hypothesis AMEMSET : aintrin_realizes trasegs B OSet A_asan_memset.
Hypothesis AMEMCPY : aintrin_realizes trasegs B OCpy A_asan_memcpy.
Hypothesis AFREE : afree_realizes trasegs B.
Hypothesis ASM1 : astack_malloc_realizes trasegs B 1.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASF : astack_free_law trasegs B.
Hypothesis FFL : frame_flag_lawP trasegs B.
Let HBcode := tl_code B TL. Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL.
Let HBguar := tl_got_uar B TL. Let HBuar := tl_uar_cell B TL. Let errno_low := tl_env B TL.
Local Notation code := (as_code B).
Theorem tra_cgif_raw_addframe : trawadd_spec B.
Proof.
assert (TLZW : tlzw_spec B) by (eapply tra_lzw; eassumption).
assert (RX : ra_from B ss_X (INV_X B)) by (eapply ra_X; eassumption).
assert (RX1 : ra_from B ss_X1 (INV_X B)) by (eapply ra_X1; eassumption).
assert (RH : ra_from B ss_G3 (INV_T0 B)) by (eapply ra_H; eassumption).
assert (RG : ra_from B ss_G2 (INV_T0 B)) by (eapply ra_G; eassumption).
assert (RT0 : ra_from B ss_T0 (INV_T0 B)) by (eapply ra_T0; eassumption).
assert (RTF : ra_from B ss_Tf (INV_Tf B)) by (eapply ra_Tf; eassumption).
assert (RM : ra_from B ss_M (INV_M B)) by (eapply ra_M; eassumption).
assert (RL : ra_from B ss_L (INV_L B)) by (eapply ra_L; eassumption).
assert (RI : ra_from B ss_I (INV_D B)) by (eapply ra_I; eassumption).
assert (RP : ra_from B ss_P (INV_D B)) by (eapply ra_P; eassumption).
assert (RF : ra_from B ss_F (INV_D B)) by (eapply ra_F; eassumption).
assert (RE : ra_from B ss_E (INV_D B)) by (eapply ra_E; eassumption).
assert (RD : ra_from B ss_D (INV_D B)) by (eapply ra_D; eassumption).
assert (RC : ra_from B ss_C (INV_0 B 1)) by (eapply ra_C; eassumption).
assert (RB8 : ra_from B ss_B8 (INV_0 B 1)) by (eapply ra_B8; eassumption).
assert (RA2 : ra_from B ss_A2 (INV_0 B 1)) by (eapply ra_A2; eassumption).
clear RX RX1 RH RG RT0 RTF RM RL RI RP RF RE RD RC RB8 TLZW.
unfold trawadd_spec.
intros ly S W regs mem md ch raw g cfp gct rattr Wd Hd sgct loops rcur ctx lct img fattr w h top left delay slct disp tidx Nimg rest
HPRE Hal32 Hctx Hroom HROD H10 H11 HFO Hcfg Hraw Hsg Mgw Mgf Rctx Mg80 Hw Hh HnP HnPN HPerm Hlct Hev Hlive.
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs.
pose proof (ra_entry B TL LAWS W ly S regs mem md ch raw g cfp gct rattr Wd Hd sgct loops rcur ctx lct img fattr w h top left delay slct disp tidx Nimg rest
HPRE Hal32 HROD H10 H11 HFO Hcfg Hraw Hsg Mgw Mgf Rctx Mg80 Hw Hh HnP HnPN HPerm) as HS.
pose proof (ajournal_init trasegs B TRAWADD_STK [(raw + 40, raw + 44)] ly S W regs mem md ch HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5). assert (FFS : TRAWADD_STK = 17040) by reflexivity.
assert (HEV : EV_RAWADD = 27) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
destruct HFO as ((cid & pos & Hfin & Hcid0 & Hfal & Hflo & Hfhi) & Hcal & HRA).
destruct (frames_bounds trasegs B LAWS ly S W mem md cid pos HAR Hfin) as (Hf4096 & Hfceil & Hfhigh).
pose proof (frm_off_img _ _ _ _ _ _ _ _ HAR Hfin) as Hfhigh_img.
assert (EFA0 : forall c p, frame_addr ly c p = frame_addr ly c p) by reflexivity. assert (EFL0 : forall c p, flag_addr ly c p = flag_addr ly c p) by reflexivity.
assert (Hing : In (g, CGIF_SIZE) (ablocks B ly S)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm|]; right; left; reflexivity).
assert (Hraw_in : In (raw, RAW_SIZE) (ablocks B ly S)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm|]; left; reflexivity).
destruct (al_blocks _ _ LAWS ly S W mem md raw RAW_SIZE HAR Hraw_in) as (Hr16 & Hr4096 & Hrceil & Hrh_ia & Hrpres & _). pose proof (proj1 Hrh_ia) as Hrh.
pose proof (blk_off_img _ _ _ _ _ _ raw RAW_SIZE HAR Hraw_in) as Hrh_img.
change (req_size RAW_SIZE) with 48 in Hrceil, Hrpres, Hrh_img.
destruct (al_blocks _ _ LAWS ly S W mem md g CGIF_SIZE HAR Hing) as (Hg16 & Hg4096 & Hgceil & Hgh_ia & _ & _). pose proof (proj1 Hgh_ia) as Hgh.
pose proof (blk_off_img _ _ _ _ _ _ g CGIF_SIZE HAR Hing) as Hgh_img.
change (req_size CGIF_SIZE) with 96 in Hgceil, Hgh, Hgh_img.
remember (Ereg regs (ra_extra g gct rattr Wd Hd sgct loops rcur lct img fattr w h top left delay slct disp tidx ctx)) as E eqn:HE.
assert (E1 : ew E 1 = getr regs 1) by (subst E; exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (subst E; exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (subst E; exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E8 : ew E 8 = getr regs 8) by (subst E; exact (ew_Ereg_nat regs _ 8 8%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 raw) by (subst E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 cfp) by (subst E; rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (EX : forall j, ew E (32 + j) = nth j (ra_extra g gct rattr Wd Hd sgct loops rcur lct img fattr w h top left delay slct disp tidx ctx) (Z_to_bv 64 0)) by (intros j; subst E; apply ew_Ereg_extra).
pose proof (EX 0%nat) as E32. pose proof (EX 1%nat) as E33. pose proof (EX 2%nat) as E34. pose proof (EX 3%nat) as E35.
pose proof (EX 4%nat) as E36. pose proof (EX 5%nat) as E37. pose proof (EX 6%nat) as E38. pose proof (EX 7%nat) as E39. pose proof (EX 8%nat) as E40.
pose proof (EX 9%nat) as E41. pose proof (EX 10%nat) as E42. pose proof (EX 11%nat) as E43. pose proof (EX 12%nat) as E44. pose proof (EX 13%nat) as E45.
pose proof (EX 14%nat) as E46. pose proof (EX 15%nat) as E47. pose proof (EX 16%nat) as E48. pose proof (EX 17%nat) as E49. pose proof (EX 18%nat) as E50.
pose proof (EX 19%nat) as E51. pose proof (EX 20%nat) as E52.
cbn [Nat.add nth ra_extra map] in E32, E33, E34, E35, E36, E37, E38, E39, E40, E41, E42, E43, E44, E45, E46, E47, E48, E49, E50, E51, E52.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs (ra_extra g gct rattr Wd Hd sgct loops rcur lct img fattr w h top left delay slct disp tidx ctx)) E) by (rewrite HE; split; [intros n Hn; reflexivity | reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r) by (intros n r Hn; rewrite HE; apply ew_Ereg_nat; exact Hn).
clear HE.
unfold cfg_at. change (w64 A_cgif_raw_addframe) with (Z_to_bv 64 A_cgif_raw_addframe).
shok_auto SHOK RABx E (mrestrict (w_H W) mem).
aj_run_tok tratbl_lib_ok HS HJ SHOK RABspan.
{ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0 ?fp ?b0 ?bc ?lyx ?own => let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0 fp b0 bc lyx own) end.
eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat 0); [reflexivity | cbn [ew]; rewrite Usp; lia | cbn; lia | cbn; lia |].
repeat (apply awr_ok_cons_ro; [cbn; lia|]).
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 10%nat); [reflexivity | cbn [ew]; rewrite E10; apply unsigned_lit_small; lia | | ];
[ cbn [YQ0b.r_wlo YQ0b.r_whi]; intros a Ha; right; left; split; [exists (raw + 40, raw + 44); split; [left; reflexivity | cbn [fst snd]; clear - Ha; lia] | exists raw, RAW_SIZE; split; [exact Hraw_in | change (req_size RAW_SIZE) with 48; lia]]
| repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil ]. }
lazymatch type of HFr with frame_of ?Ef ?rs (mrestrict _ _) (mrestrict _ (ms_mem ?msX)) =>
assert (HUP : forall a, spZ regs <= a < 2 ^ 64 -> aview trasegs (w_H W) (ms_mem msX) a = aview trasegs (w_H W) mem a);
[ eapply (aview_kept_frame Ef rs _ _ _ (spZ regs) HFr); [lia|];
intros a Ha (rg & Hin & Hrg);
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In rg rs1) in Hin end; cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin]; [cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val] in Hrg; rewrite ?Usp, ?E10 in Hrg; rewrite ?unsigned_lit_small in Hrg by lia; lia|]);
destruct Hin | ] end.
clear HF HFr HG.
Local Ltac aconstsA HROD HJx Kgot Kcell Kguar Kuar Vgr :=
let Kc := fresh "Kc" in let Ku := fresh "Ku" in let Kg := fresh "Kg" in let Kgu := fresh "Kgu" in
destruct (al_const _ _ LAWS _ _ _ _ _ (proj1 HJx)) as (Kc & Ku & Kg & Kgu);
rewrite HBgot, HBcell in Kg; rewrite HBcell in Kc; rewrite HBguar, HBuar in Kgu; rewrite HBuar in Ku;
pose proof (val_mem_of_rdword trasegs _ _ _ _ Kg) as Kgot; pose proof (val_mem_of_rdword trasegs _ _ _ _ Kc) as Kcell;
pose proof (val_mem_of_rdword trasegs _ _ _ _ Kgu) as Kguar; pose proof (val_mem_of_rd32 trasegs _ _ _ _ Ku) as Kuar;
clear Kc Ku Kg Kgu;
pose proof (arodata_val8 B _ _ A_GOT_rawadd A_cgif_raw_addframe TL
(arodata_ok_journal B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJx HROD)
ltac:(unfold A_GOT_rawadd; lia) ltac:(unfold A_GOT_rawadd; lia)
ltac:(intros x Hx; unfold lib_const_addr, A_GOT_rawadd in *; lia)
ltac:(intros kk Hkk; do 8 (destruct kk as [|kk]; [vm_compute; reflexivity|]); lia)) as Vgr.
aconstsA HROD HJ Kgot0 Kcell0 Kguar0 Kuar0 Vgr0.
rreg HS (2%bv : bv 5) R2. rreg HS (3%bv : bv 5) R3. rreg HS (4%bv : bv 5) R4. rreg HS (1%bv : bv 5) R1.
rewrite (st_ok_restrict_mkst trasegs _ _ _ _ HS eq_refl). cbn [ss_pc].
replace 249516 with (pc_stack_malloc code 1) by (rewrite HBcode; reflexivity).
pose proof (count_cid_le_length 1 (frames S)) as Hcnt.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_stack_malloc_at trasegs B LAWS Hsegs errno_low ML SMP 1 ASM1 ltac:(lia) W (ms_regs msX) (ms_mem msX) TRAWADD_STK (spZ regs) [(raw + 40, raw + 44)] ly S W mem md [] ly S _ 0 (-320) _ HJ) end.
- unfold spZ. rewrite R2, E2. fold (spZ regs). rewrite unsigned_lit_small by lia. lia.
- reflexivity. - lia. - rewrite FFS, Hes; lia.
- rewrite R3, E3. exact Hgp. - rewrite R4, E4. exact Htp.
- exact R1. - vm_compute. reflexivity.
- change (fs_frames 1) with 8192. lia. }
cbv beta. clear R2 R3 R4 R1 HJ SHOK.
intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & fpos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2 & Hbb2 & Hz & Hflag & HK).
rewrite Hes in HK. replace (spZ regs + -320 - 4096) with (spZ regs - 4416) in HK by lia. replace (spZ regs + -320) with (spZ regs - 320) in HK by lia.
assert (HUP2 : forall a, spZ regs <= a < 2 ^ 64 -> aview trasegs (w_H W) mem2 a = aview trasegs (w_H W) mem a).
{ intros a Ha. rewrite <- (HUP a Ha). pose proof HK as (K1 & _). apply K1; lia. }
clear HUP.
aconstsA HROD HJ2 Kgot2 Kcell2 Kguar2 Kuar2 Vgr2.
pose proof (proj1 HJ2) as HAR2.
assert (Hfin2 : In (1, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
assert (HfinS2 : In (cid, pos) (frames S2)) by (rewrite Hfrs2; right; exact Hfin).
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR2 Hfin2) as (HFal & [HFhi _] & HFpres & HFSpres).
pose proof (frm_off_img _ _ _ _ _ _ _ _ HAR2 Hfin2) as HFapp_img.
destruct (frames_bounds trasegs B LAWS _ _ _ _ _ 1 fpos HAR2 Hfin2) as (HF4096 & HFceil & HFhigh).
pose proof (frm_off_img _ _ _ _ _ _ _ _ HAR2 Hfin2) as HFhigh_img.
change (fs_frame_bytes 1) with 128 in *.
set (F := frame_addr ly 1 fpos) in *. set (FL := flag_addr ly 1 fpos) in *.
destruct (in_split _ _ Hfin) as (fl1 & fl2 & Efl).
pose proof (sep_frames_pos trasegs B LAWS ly S2 W mem2 md2 (1, fpos) (cid, pos) [] fl1 fl2 HAR2 ltac:(rewrite Hfrs2, Efl; reflexivity)) as HdFC.
unfold zdisjoint, frame_rng in HdFC. cbn [fst snd] in HdFC. change (fs_frame_bytes 1) with 128 in HdFC. fold F in HdFC.
pose proof (sep_block_frame trasegs B LAWS ly S2 W mem2 md2 g CGIF_SIZE 1 fpos HAR2 ltac:(rewrite Eab; exact Hing) Hfin2) as HdFG.
unfold zdisjoint in HdFG. cbn [fst snd] in HdFG. change (req_size CGIF_SIZE) with 96 in HdFG. change (fs_frame_bytes 1) with 128 in HdFG. fold F in HdFG.
pose proof (sep_block_frame trasegs B LAWS ly S2 W mem2 md2 raw RAW_SIZE 1 fpos HAR2 ltac:(rewrite Eab; exact Hraw_in) Hfin2) as HdFR.
unfold zdisjoint in HdFR. cbn [fst snd] in HdFR. change (req_size RAW_SIZE) with 48 in HdFR. change (fs_frame_bytes 1) with 128 in HdFR. fold F in HdFR.
Local Ltac keptRA HK HJx AG Usp E10 E11 E32 Hfin Hraw Hraw2 Hing Kg Kg2 Kc Kc2 Kgu Kgu2 Ku Ku2 Vg Vg2 :=
lazymatch goal with
| |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 2%nat) _ _ _ _ _) =>
eapply (region_kept_stack_aj trasegs B); [exact HK | exact HJx | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?(AG 2%nat) by lia; exact Usp
| lia | unfold TRAWADD_STK, LZW_TSTK, ASTACK; lia | lia | lia | lia]
| |- region_kept _ _ _ _ (YQ0b.mkRegion None A_GOT_shadow _ _ _ _) => apply (region_kept_val trasegs _ _ _ A_GOT_shadow 8 A_shadow_glob); [exact Kg | exact Kg2 | lia]
| |- region_kept _ _ _ _ (YQ0b.mkRegion None A_shadow_glob _ _ _ _) => apply (region_kept_val trasegs _ _ _ A_shadow_glob 8 SHADOW_OFF); [exact Kc | exact Kc2 | lia]
| |- region_kept _ _ _ _ (YQ0b.mkRegion None A_GOT_uar _ _ _ _) => apply (region_kept_val trasegs _ _ _ A_GOT_uar 8 A_uar_glob); [exact Kgu | exact Kgu2 | lia]
| |- region_kept _ _ _ _ (YQ0b.mkRegion None A_uar_glob _ _ _ _) => apply (region_kept_val trasegs _ _ _ A_uar_glob 4 1); [exact Ku | exact Ku2 | lia]
| |- region_kept _ _ _ _ (YQ0b.mkRegion None A_GOT_rawadd _ _ _ _) => apply (region_kept_val trasegs _ _ _ A_GOT_rawadd 8 A_cgif_raw_addframe); [exact Vg | exact Vg2 | lia]
| |- region_kept _ _ _ _ (YQ0b.mkRegion None ?a _ _ _ _) =>
first [ change a with A_GOT_shadow | change a with A_shadow_glob | change a with A_GOT_uar | change a with A_uar_glob | change a with A_GOT_rawadd ];
keptRA HK HJx AG Usp E10 E11 E32 Hfin Hraw Hraw2 Hing Kg Kg2 Kc Kc2 Kgu Kgu2 Ku Ku2 Vg Vg2
| |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 11%nat) _ _ _ _ _) =>
eapply (region_kept_frame_aj trasegs B); [exact HK | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?(AG 11%nat) by lia; rewrite E11; apply unsigned_lit_small; lia
| exact Hfin | lia | lia | lia | intros a Ha Hn; first [exact Hn | rqs Hn; zone_lia]]
| |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 10%nat) _ _ _ _ _) =>
eapply (region_kept_block_ajw2 trasegs B LAWS); [exact HK | exact (proj1 HJx) | exact Hraw2 | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?(AG 10%nat) by lia; rewrite E10; apply unsigned_lit_small; lia
| exact Hraw | lia | change (req_size RAW_SIZE) with 48; lia | lia | lia | intros a Ha Hn; first [exact Hn | rqs Hn; zone_lia]]
| |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 32%nat) _ _ _ _ _) =>
eapply (region_kept_block_aj trasegs B); [exact HK | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?(AG 32%nat) by lia; rewrite E32; apply unsigned_lit_small; lia
| exact Hing | lia | change (req_size CGIF_SIZE) with 96; unfold CGIF_SIZE; lia | lia | intros a Ha Hn; first [exact Hn | rqs Hn; zone_lia]]
end.
assert (AG : forall n, (n < 33)%nat -> ew E n = ew E n) by (intros; reflexivity).
assert (Hraw2 : In (raw, RAW_SIZE) (ablocks B ly S2)) by (rewrite Eab; exact Hraw_in).
reseat HS HJ2 HP2 [0; 1; 2; 3; 4; 5; 6; 7; 8]%nat AG
ltac:(idtac; first [keptRA HK HJ2 AG Usp E10 E11 E32 Hfin Hraw_in Hraw2 Hing Kgot0 Kgot2 Kcell0 Kcell2 Kguar0 Kguar2 Kuar0 Kuar2 Vgr0 Vgr2 | match goal with |- ?g => idtac "KEPTFAIL" g end]).
rreg HS (10%bv : bv 5) RF. cbn [ms_regs] in RF. rewrite Ha0 in RF. symmetry in RF. unfold w64 in RF. fold F in RF.
lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
pose proof (st_ok_agree trasegs 69 Ev (havoc Ev 69 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)]) ssv msv HS
(env_agree_havoc_ge 69 69 Ev Ev _ ltac:(lia) (env_agree_refl 69 Ev)) ltac:(vm_compute; reflexivity)) as HS3 end.
clear HS. rename HS3 into HS. rebaseE HS AG HEv.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
assert (E69 : ew Ev 69 = Z_to_bv 64 FL) by (rewrite HEv; exact (ew_havoc_new _ 69 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 0 (Z_to_bv 64 0) ltac:(cbn; lia)));
assert (E70 : ew Ev 70 = Z_to_bv 64 (SB + F / 8)) by (rewrite HEv; exact (ew_havoc_new _ 69 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 1 (Z_to_bv 64 0) ltac:(cbn; lia))) end.
clear HEv.
assert (HFq : F = 32 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(lia)); lia).
assert (HF8 : F / 8 = 4 * (F / 32)) by (rewrite HFq at 1; replace (32 * (F / 32)) with (4 * (F / 32) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
assert (HF8lo : 512 <= F / 8) by (apply Z.div_le_lower_bound; lia)    .
assert (HF8hi : F / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia).
destruct (FFL ly S2 W mem2 md2 1 fpos HAR2 Hfin2) as (HFLpres & HFLown & HFLrng). fold FL in HFLpres, HFLown, HFLrng.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
pose proof (st_ok_add_fact trasegs Ev _ _ 57 (HPTR 5) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite RF, unsigned_lit_small by lia; change (2 ^ 5) with 32; lia)) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_add_fact trasegs Ev _ _ 69 (HPTR 0) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite E69, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_add_fact trasegs Ev _ _ 70 (mkAF (SB + 512) (SB + 17592186044416) 2) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E70, unsigned_lit_small by (unfold SB; lia); change (2 ^ 2) with 4; unfold SB;
split; [lia|]; split; [rewrite HF8; replace (2147450880 + 4 * (F / 32)) with ((536862720 + F / 32) * 4) by lia; apply Z_mod_mult | lia])) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_add_alias trasegs Ev _ _ _ _ HS (shadow_decl_ok Ev 57 40 70 F SB RF ltac:(lia) E40 E70)) as HS3;
clear HS; rename HS3 into HS;
let addF lo hi cs cks :=
let HS3 := fresh "HS3" in
lazymatch goal with |- _ =>
pose proof (ast_ok_add_region trasegs Ev _ _ (YQ0b.mkRegion (Some 57%nat) lo hi lo hi cs) HS eq_refl
ltac:(unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst app];
rewrite RF, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split;
[ intros o Ho; apply (apresent_writable trasegs); apply (proj1 (HFpres (F + o) ltac:(lia))) | cks ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
rewrite RF, ?(AG 2%nat), ?(AG 10%nat), ?(AG 11%nat), ?(AG 32%nat), ?Usp, ?E10, ?E11, ?E32, !unsigned_lit_small by lia; unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob, A_GOT_rawadd, CGIF_SIZE;
repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS end in
addF 58 128 [YQ0b.mkChunk 120 (CVal 8 (SOff 69 0))]
ltac:(apply Forall_cons; [|apply Forall_nil]; apply (chunk_ok_val trasegs Ev _ F 120 8 _ FL);
[cbn [sv_denot]; rewrite E69, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | change (fs_frame_bytes 1) with 128 in Hflag; replace (F + 120) with (F + 128 - 8) by lia; exact (val_mem_of_rdword trasegs _ _ _ _ Hflag)]);
addF 49 58 (@nil YQ0b.chunk) ltac:(apply Forall_nil);
addF 0 49 (@nil YQ0b.chunk) ltac:(apply Forall_nil) end.
assert (ZS : forall j, 0 <= j < 2 -> val_mem trasegs (mrestrict (w_H W) mem2) (SB + F / 8 + 8 * j) 8 0).
{ intros j Hj. apply val_mem_zero8. intros i Hi. unfold zero_shadow, shadow_of_addr in Hz. rewrite <- SB_SHADOW_OFF in Hz.
replace (SB + F / 8 + 8 * j + i) with (SB + F / 8 + (8 * j + i)) by lia. apply Hz. change (128 / 8) with 16. lia. }
lazymatch type of HS with st_ok _ ?Ev _ _ =>
pose proof (ast_ok_add_region trasegs Ev _ _
(fshadow_region 70 1 0 16 [YQ0b.mkChunk 0 (CVal 8 (SLit 0)); YQ0b.mkChunk 8 (CVal 8 (SLit 0))]) HS eq_refl
ltac:(unfold region_ok, fshadow_region; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst app];
change (fs_frame_bytes 1 / 8) with 16; rewrite E70, unsigned_lit_small by (unfold SB; lia); split; [unfold SB; lia|]; split; [unfold SB; lia|]; split;
[ intros o Ho; apply (apresent_writable trasegs); unfold shadow_addr in HFSpres; rewrite <- SB_SHADOW_OFF in HFSpres;
replace (SB + F / 8 + o) with (SB + F / 8 + o) by lia; apply (proj1 (HFSpres o ltac:(change (128 / 8) with 16; lia)))
| apply Forall_cons; [apply (chunk_ok_val trasegs Ev _ (SB + F / 8) 0 8 _ 0); [reflexivity | zside | zside | rewrite Z.add_0_r; replace (SB + F / 8) with (SB + F / 8 + 8 * 0) by lia; apply ZS; lia]|];
apply Forall_cons; [apply (chunk_ok_val trasegs Ev _ (SB + F / 8) 8 8 _ 0); [reflexivity | zside | zside | replace (SB + F / 8 + 8) with (SB + F / 8 + 8 * 1) by lia; apply ZS; lia]|];
apply Forall_nil ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint, fshadow_region; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
change (fs_frame_bytes 1 / 8) with 16;
rewrite E70, RF, ?(AG 2%nat), ?(AG 10%nat), ?(AG 11%nat), ?(AG 32%nat), ?Usp, ?E10, ?E11, ?E32, !unsigned_lit_small by (unfold SB; lia);
unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob, A_GOT_rawadd, CGIF_SIZE, SB; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
aj_run_to_sh tratbl_lib_ok HS HJ2 0x88bc0. { awrRA AG fpos F EFA0. }
upd_aboveW HUP2 HFr AG. rename HUP2 into HUP. clear HF HFr HG.
lazymatch type of AG with forall n, _ -> ew ?Ev n = _ =>
assert (E11' : ew Ev 11 = Z_to_bv 64 cfp) by (rewrite (AG 11%nat) by lia; exact E11);
assert (E10' : ew Ev 10 = Z_to_bv 64 raw) by (rewrite (AG 10%nat) by lia; exact E10) end.
fs_roA HS. reshok_bx HS 40%nat.
aj_run_tok tratbl_lib_ok HS HJ2 SHOK RABspan.
all: try (oblFA HJ2 E11' E40 HRA HAR Hfin Hcid0 Hflo Hfhi Hfal).
all: try (obl_blk HJ2 E10' E40 Hraw2).
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrRA AG fpos F EFA0.
clear_frames.
rebaseE HS AG HEv. clear HEv.
lazymatch goal with |- SRr _ ?Wg (mkCfg ?msF ?mdF) _ =>
lazymatch type of HS with st_ok _ ?Ev _ _ =>
eapply (RA2 (mkRACX ly S W regs mem md ch raw g cfp gct rattr Wd Hd sgct loops rcur ctx lct img fattr w h top left delay slct disp tidx Nimg rest cid pos fpos E)
Ev 0 _ _ Wg msF mdF) end end.
- unfold ra_base, ra_vals. cbn [c_ly c_S c_W c_regs c_mem c_md c_ch c_raw c_g c_cfp c_gct c_rattr c_Wd c_Hd c_sgct c_loops c_rcur c_ctx c_lct c_img c_fattr
c_w c_h c_top c_left c_delay c_slct c_disp c_tidx c_Nimg c_rest c_cid c_pos c_fpos c_E0].
repeat match goal with |- _ /\ _ => split end; try assumption; try (clear - Rctx; lia).
intros j Hj. rewrite (EX j). change (Z_to_bv 64 0) with ((Z_to_bv 64) 0). unfold ra_extra. rewrite map_nth. reflexivity.
- unfold YC4c.ra_E, YC4c.ra_F, YC4c.ra_FL, YC4c.ra_vals. cbn [c_ly c_fpos c_E0 c_g c_gct c_rattr c_Wd c_Hd c_sgct c_loops c_rcur c_ctx c_lct c_img c_fattr
c_w c_h c_top c_left c_delay c_slct c_disp c_tidx]. fold F FL.
split; [exact AG|]. split; [|split; [exact RF | split; [exact E69 | exact E70]]].
intros j Hj. do 21 (try (destruct j as [|j]; [first [assumption | lia] |])). lia.
- cbn [c_regs c_raw c_ly c_S c_W c_mem c_md c_fpos]. exact HJ2.
- cbn [c_S c_fpos]. exact Hfrs2.
- split; [lia | cbn [c_ly c_S]; exact Eab].
- exact HS.
Qed.
End d.
End b.
