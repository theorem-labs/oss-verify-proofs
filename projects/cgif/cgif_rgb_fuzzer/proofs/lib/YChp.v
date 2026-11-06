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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YCe7 YF9i YCeb YCe8 YCfq YCdy YCfr YCfu YCe9 YChv YChx YChq YChr YChs YCht YChu.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section RN.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AMALLOC : amalloc_realizes trbsegs B.
Hypothesis AMEMSET : aintrin_realizes trbsegs B OSet A_asan_memset.
Hypothesis AMEMCPY : aintrin_realizes trbsegs B OCpy A_asan_memcpy.
Hypothesis ASM2 : astack_malloc_realizes trbsegs B 2.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASF : astack_free_law trbsegs B.
Hypothesis FFL : frame_flag_lawP trbsegs B.
Let HBcode := tl_code B TL. Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL.
Let HBguar := tl_got_uar B TL. Let HBuar := tl_uar_cell B TL. Let errno_low := tl_env B TL.
Local Notation code := (as_code B).
Theorem trb_cgif_raw_newgif : trawnew_spec B.
Proof.
unfold trawnew_spec.
intros ly S W regs mem md ch cfgp g pgct rattr Wd Hd sgct loops ctx rest HPRE Hal32 Hctx Hroom HROD H10 HFO Hcfg HPerm Mgw Mgf Rctx Mg80 Hev Hlive.
pose proof Hwx_tfa as Hwx. pose proof trb_segs_low as Hsegs.
pose proof (rn_entry B TL LAWS W ly S regs mem md ch cfgp g pgct rattr Wd Hd sgct loops ctx rest HPRE Hal32 HROD H10 HFO Hcfg HPerm Mgw Mgf Rctx Mg80) as HS.
pose proof (ajournal_init trbsegs B TRAWNEW_STK [] ly S W regs mem md ch HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5). assert (FFS : TRAWNEW_STK = 16576) by reflexivity.
assert (HEV : EV_RAWNEW = 4) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
destruct HFO as ((cid & pos & Hfin & Hcid0 & Hfal & Hflo & Hfhi) & Hcal & HRA).
destruct (frames_bounds trbsegs B LAWS ly S W mem md cid pos HAR Hfin) as (Hf4096 & Hfceil & Hfhigh).
pose proof (frm_off_img _ _ _ _ _ _ _ _ HAR Hfin) as Hfhigh_img.
assert (EFA0 : forall c p, frame_addr ly c p = frame_addr ly c p) by reflexivity. assert (EFL0 : forall c p, flag_addr ly c p = flag_addr ly c p) by reflexivity.
assert (Hing : In (g, CGIF_SIZE) (ablocks B ly S)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. left. reflexivity. }
destruct (al_blocks _ _ LAWS ly S W mem md g CGIF_SIZE HAR Hing) as (Hg16 & Hg4096 & Hgceil & Hgh_ia & _ & _). pose proof (proj1 Hgh_ia) as Hgh.
pose proof (blk_off_img _ _ _ _ _ _ g CGIF_SIZE HAR Hing) as Hgh_img.
change (req_size CGIF_SIZE) with 96 in Hgceil, Hgh, Hgh_img.
remember (Ereg regs (rn_extra g pgct rattr Wd Hd sgct loops ctx)) as E eqn:HE.
assert (E1 : ew E 1 = getr regs 1) by (subst E; exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (subst E; exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (subst E; exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E8 : ew E 8 = getr regs 8) by (subst E; exact (ew_Ereg_nat regs _ 8 8%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 cfgp) by (subst E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (EX : forall j, ew E (32 + j) = nth j (rn_extra g pgct rattr Wd Hd sgct loops ctx) (Z_to_bv 64 0)) by (intros j; subst E; apply ew_Ereg_extra).
pose proof (EX 0%nat) as E32. pose proof (EX 1%nat) as E33. pose proof (EX 2%nat) as E34. pose proof (EX 3%nat) as E35.
pose proof (EX 4%nat) as E36. pose proof (EX 5%nat) as E37. pose proof (EX 6%nat) as E38. pose proof (EX 7%nat) as E39. pose proof (EX 8%nat) as E40.
cbn [Nat.add nth rn_extra map] in E32, E33, E34, E35, E36, E37, E38, E39, E40. clear EX.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs (rn_extra g pgct rattr Wd Hd sgct loops ctx)) E) by (rewrite HE; split; [intros n Hn; reflexivity | reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r) by (intros n r Hn; rewrite HE; apply ew_Ereg_nat; exact Hn).
clear HE.
cbn [CTX_cgif_raw_newgif In] in Hctx.
assert (Hra68 : 0x86040 = raZ regs) by (destruct Hctx as [H | [H | []]]; injection H as Hr Hs; exact Hr).
assert (Hspine : spine ch = [0x81c9c; 0x81498] \/ spine ch = [0x81c9c; 0x81498; 0x8116c])
by (destruct Hctx as [H | [H | []]]; injection H as Hr Hs; rewrite <- Hs; [left | right]; reflexivity).
assert (Hchne : ch <> []) by (intros ->; destruct Hspine as [H|H]; discriminate H).
assert (Htop32 : spZ regs + 16 <= s0Z regs /\ s0Z regs < ly_top ly - 16).
{ destruct Hch as [[_ Hnil] | (H1 & H2 & _)]; [exfalso; exact (Hchne Hnil) | lia]. }
unfold cfg_at. change (w64 A_cgif_raw_newgif) with (Z_to_bv 64 A_cgif_raw_newgif).
shok_auto SHOK RBx E (mrestrict (w_H W) mem).
aj_run_tok trbtbl_lib_ok HS HJ SHOK RBspan. { awr_ok_tac. exact Usp. }
lazymatch type of HFr with frame_of ?Ef ?rs (mrestrict _ _) (mrestrict _ (ms_mem ?msX)) =>
assert (HUP : forall a, spZ regs <= a < 2 ^ 64 -> aview trbsegs (w_H W) (ms_mem msX) a = aview trbsegs (w_H W) mem a);
[ eapply (aview_kept_frame Ef rs _ _ _ (spZ regs) HFr); [lia|];
intros a Ha (rg & Hin & Hrg);
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In rg rs1) in Hin end; cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin]; [cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val] in Hrg; rewrite ?Usp in Hrg; lia|]);
match goal with |- ?g => match type of Hin with ?t => idtac "HUPLEFT" t end end; destruct Hin | ] end.
clear HF HFr HG.
aconsts HROD HJ Kgot0 Kcell0 Kguar0 Kuar0 Vgr0.
rreg HS (2%bv : bv 5) R2. rreg HS (3%bv : bv 5) R3. rreg HS (4%bv : bv 5) R4. rreg HS (1%bv : bv 5) R1.
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
replace 250624 with (pc_stack_malloc code 2) by (rewrite HBcode; reflexivity).
pose proof (count_cid_le_length 2 (frames S)) as Hcnt.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_stack_malloc_at trbsegs B LAWS Hsegs errno_low ML SMP 2 ASM2 ltac:(lia) W (ms_regs msX) (ms_mem msX) TRAWNEW_STK (spZ regs) [] ly S W mem md [] ly S _ 0 (-192) _ HJ) end.
- unfold spZ. rewrite R2, E2. fold (spZ regs). rewrite unsigned_lit_small by lia. lia.
- reflexivity. - lia. - rewrite FFS, Hes; lia.
- rewrite R3, E3. exact Hgp. - rewrite R4, E4. exact Htp.
- exact R1. - vm_compute. reflexivity.
- change (fs_frames 2) with 4096. lia. }
cbv beta. clear R2 R3 R4 R1 HJ SHOK.
intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & fpos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2 & Hbb2 & Hz & Hflag & HK).
rewrite Hes in HK. replace (spZ regs + -192 - 4096) with (spZ regs - 4288) in HK by lia. replace (spZ regs + -192) with (spZ regs - 192) in HK by lia.
assert (HUP2 : forall a, spZ regs <= a < 2 ^ 64 -> aview trbsegs (w_H W) mem2 a = aview trbsegs (w_H W) mem a).
{ intros a Ha. rewrite <- (HUP a Ha). pose proof HK as (K1 & _). apply K1; lia. }
clear HUP.
aconsts HROD HJ2 Kgot2 Kcell2 Kguar2 Kuar2 Vgr2.
pose proof (proj1 HJ2) as HAR2.
assert (Hfin2 : In (2, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
assert (HfinS2 : In (cid, pos) (frames S2)) by (rewrite Hfrs2; right; exact Hfin).
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos HAR2 Hfin2) as (HFal & [HFhi _] & HFpres & HFSpres).
pose proof (frm_off_img _ _ _ _ _ _ _ _ HAR2 Hfin2) as HFapp_img.
destruct (frames_bounds trbsegs B LAWS _ _ _ _ _ 2 fpos HAR2 Hfin2) as (HF4096 & HFceil & HFhigh).
pose proof (frm_off_img _ _ _ _ _ _ _ _ HAR2 Hfin2) as HFhigh_img.
change (fs_frame_bytes 2) with 256 in *.
set (F := frame_addr ly 2 fpos) in *. set (FL := flag_addr ly 2 fpos) in *.
destruct (in_split _ _ Hfin) as (fl1 & fl2 & Efl).
pose proof (sep_frames_pos trbsegs B LAWS ly S2 W mem2 md2 (2, fpos) (cid, pos) [] fl1 fl2 HAR2 ltac:(rewrite Hfrs2, Efl; reflexivity)) as HdFC.
unfold zdisjoint, frame_rng in HdFC. cbn [fst snd] in HdFC. change (fs_frame_bytes 2) with 256 in HdFC. fold F in HdFC.
pose proof (sep_block_frame trbsegs B LAWS ly S2 W mem2 md2 g CGIF_SIZE 2 fpos HAR2 ltac:(rewrite Eab; exact Hing) Hfin2) as HdFG.
unfold zdisjoint in HdFG. cbn [fst snd] in HdFG. change (req_size CGIF_SIZE) with 96 in HdFG. change (fs_frame_bytes 2) with 256 in HdFG. fold F in HdFG.
assert (AG : forall n, (n < 33)%nat -> ew E n = ew E n) by (intros; reflexivity).
reseat HS HJ2 HP2 [0; 1; 2; 3; 4; 5; 6; 7]%nat AG
ltac:(idtac; keptR HK HJ2 AG Usp E10 E32 Hfin Hing Kgot0 Kgot2 Kcell0 Kcell2 Kguar0 Kguar2 Kuar0 Kuar2 Vgr0 Vgr2).
rreg HS (10%bv : bv 5) RF. cbn [ms_regs] in RF. rewrite Ha0 in RF. symmetry in RF. unfold w64 in RF. fold F in RF.
lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
pose proof (st_ok_agree trbsegs 57 Ev (havoc Ev 57 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)]) ssv msv HS
(env_agree_havoc_ge 57 57 Ev Ev _ ltac:(lia) (env_agree_refl 57 Ev)) ltac:(vm_compute; reflexivity)) as HS3 end.
clear HS. rename HS3 into HS. rebaseE HS AG HEv.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
assert (E57 : ew Ev 57 = Z_to_bv 64 FL) by (rewrite HEv; exact (ew_havoc_new _ 57 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 0 (Z_to_bv 64 0) ltac:(cbn; lia)));
assert (E58 : ew Ev 58 = Z_to_bv 64 (SB + F / 8)) by (rewrite HEv; exact (ew_havoc_new _ 57 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 1 (Z_to_bv 64 0) ltac:(cbn; lia))) end.
clear HEv.
assert (HFq : F = 32 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(lia)); lia).
assert (HF8 : F / 8 = 4 * (F / 32)) by (rewrite HFq at 1; replace (32 * (F / 32)) with (4 * (F / 32) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
assert (HF8lo : 512 <= F / 8) by (apply Z.div_le_lower_bound; lia)    .
assert (HF8hi : F / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia).
destruct (FFL ly S2 W mem2 md2 2 fpos HAR2 Hfin2) as (HFLpres & HFLown & HFLrng). fold FL in HFLpres, HFLown, HFLrng.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
pose proof (st_ok_add_fact trbsegs Ev _ _ 45 (HPTR 5) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite RF, unsigned_lit_small by lia; change (2 ^ 5) with 32; lia)) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_add_fact trbsegs Ev _ _ 57 (HPTR 0) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite E57, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_add_fact trbsegs Ev _ _ 58 (mkAF (SB + 512) (SB + 17592186044416) 2) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E58, unsigned_lit_small by (unfold SB; lia); change (2 ^ 2) with 4; unfold SB;
split; [lia|]; split; [rewrite HF8; replace (2147450880 + 4 * (F / 32)) with ((536862720 + F / 32) * 4) by lia; apply Z_mod_mult | lia])) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_add_alias trbsegs Ev _ _ _ _ HS (shadow_decl_ok Ev 45 35 58 F SB RF ltac:(lia) E35 E58)) as HS3;
clear HS; rename HS3 into HS;
pose proof (ast_ok_add_region trbsegs Ev _ _ (fframe_region 45 57 2 []) HS eq_refl
ltac:(unfold region_ok, fframe_region; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst app];
change (fs_frame_bytes 2) with 256; rewrite RF, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split;
[ intros o Ho; apply (apresent_writable trbsegs); apply (proj1 (HFpres (F + o) ltac:(lia)))
| apply Forall_cons; [|apply Forall_nil]; apply (chunk_ok_val trbsegs Ev _ F (256 - 8) 8 _ FL);
[cbn [sv_denot]; rewrite E57, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | replace (F + (256 - 8)) with (F + 256 - 8) by lia; exact (val_mem_of_rdword trbsegs _ _ _ _ Hflag)] ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint, fframe_region; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
change (fs_frame_bytes 2) with 256;
rewrite RF, ?(AG 2%nat), ?(AG 10%nat), ?(AG 32%nat), ?Usp, ?E10, ?E32, !unsigned_lit_small by lia; unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob, A_GOT_rawnew;
repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS end.
assert (ZS : forall j, 0 <= j < 4 -> val_mem trbsegs (mrestrict (w_H W) mem2) (SB + F / 8 + 8 * j) 8 0).
{ intros j Hj. apply val_mem_zero8. intros i Hi. unfold zero_shadow, shadow_of_addr in Hz. rewrite <- SB_SHADOW_OFF in Hz.
replace (SB + F / 8 + 8 * j + i) with (SB + F / 8 + (8 * j + i)) by lia. apply Hz. change (256 / 8) with 32. lia. }
lazymatch type of HS with st_ok _ ?Ev _ _ =>
pose proof (ast_ok_add_region trbsegs Ev _ _
(fshadow_region 58 2 0 32 [YQ0b.mkChunk 0 (CVal 8 (SLit 0)); YQ0b.mkChunk 8 (CVal 8 (SLit 0)); YQ0b.mkChunk 16 (CVal 8 (SLit 0)); YQ0b.mkChunk 24 (CVal 8 (SLit 0))]) HS eq_refl
ltac:(unfold region_ok, fshadow_region; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst app];
change (fs_frame_bytes 2 / 8) with 32; rewrite E58, unsigned_lit_small by (unfold SB; lia); split; [unfold SB; lia|]; split; [unfold SB; lia|]; split;
[ intros o Ho; apply (apresent_writable trbsegs); unfold shadow_addr in HFSpres; rewrite <- SB_SHADOW_OFF in HFSpres;
replace (SB + F / 8 + o) with (SB + F / 8 + o) by lia; apply (proj1 (HFSpres o ltac:(change (256 / 8) with 32; lia)))
| apply Forall_cons; [apply (chunk_ok_val trbsegs Ev _ (SB + F / 8) 0 8 _ 0); [reflexivity | zside | zside | rewrite Z.add_0_r; replace (SB + F / 8) with (SB + F / 8 + 8 * 0) by lia; apply ZS; lia]|];
apply Forall_cons; [apply (chunk_ok_val trbsegs Ev _ (SB + F / 8) 8 8 _ 0); [reflexivity | zside | zside | replace (SB + F / 8 + 8) with (SB + F / 8 + 8 * 1) by lia; apply ZS; lia]|];
apply Forall_cons; [apply (chunk_ok_val trbsegs Ev _ (SB + F / 8) 16 8 _ 0); [reflexivity | zside | zside | replace (SB + F / 8 + 16) with (SB + F / 8 + 8 * 2) by lia; apply ZS; lia]|];
apply Forall_cons; [apply (chunk_ok_val trbsegs Ev _ (SB + F / 8) 24 8 _ 0); [reflexivity | zside | zside | replace (SB + F / 8 + 24) with (SB + F / 8 + 8 * 3) by lia; apply ZS; lia]|];
apply Forall_nil ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint, fshadow_region; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
change (fs_frame_bytes 2 / 8) with 32;
rewrite E58, RF, ?(AG 2%nat), ?(AG 10%nat), ?(AG 32%nat), ?Usp, ?E10, ?E32, !unsigned_lit_small by (unfold SB; lia);
unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob, A_GOT_rawnew, SB; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
aj_run_to_sh trbtbl_lib_ok HS HJ2 0x88ef0. { awrR AG fpos F EFA0. }
upd_above HUP2 HFr AG. rename HUP2 into HUP.
clear HF HFr HG.
lazymatch type of AG with forall n, _ -> ew ?Ev n = _ =>
assert (E10' : ew Ev 10 = Z_to_bv 64 cfgp) by (rewrite (AG 10%nat) by lia; exact E10) end.
fs_ro HS. reshok_bx HS 35%nat.
aj_run_tok trbtbl_lib_ok HS HJ2 SHOK RBspan; [oblF HJ2 E10' E35 HRA HAR Hfin Hcid0 Hflo Hfhi Hfal | awrR AG fpos F EFA0 |].
upd_above HUP HFr AG. clear HF HFr HG.
srr_branch_tok trbtbl_lib_ok HS SHOK RBspan.
-
aj_run_to_tok trbtbl_lib_ok HS HJ2 SHOK RBspan 0x8935c; [awrR AG fpos F EFA0|]. clear HF.
assert (Hing2 : In (g, CGIF_SIZE) (ablocks B ly S2)) by (rewrite Eab; exact Hing).
exitR HS HJ2 AG fpos F cfgp g E57 E58 Hfin2 HfinS2 Hing2 EE Hra HEV EFA0 EFL0.
exists 0. split; [reflexivity|]. left. split; [reflexivity|].
unfold ablocks. rewrite blocks_stack_free_state. fold (ablocks B ly S2). rewrite Eab. apply Permutation_refl.
-
assert (Hsg : sgct <= 256).
{ pose proof Hcfg as Hc'. cbn [obj_at LAY_RawConfig] in Hc'. destruct Hc' as (_ & _ & _ & _ & _ & _ & [_ R32] & _). cbn [fst snd N.to_nat Z.of_N] in R32.
change (2 ^ (8 * 2)) with 65536 in R32.
unfold branch_taken in Hc. rewrite bv_ltu_unsigned in Hc. cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in Hc.
rewrite ?ew_ewset_other in Hc by lia. rewrite E38 in Hc. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, !unsigned_lit_small in Hc by lia.
destruct (Z.ltb_spec 256 sgct); [discriminate Hc | lia]. }
aj_run_tok trbtbl_lib_ok HS HJ2 SHOK RBspan; [awrR AG fpos F EFA0|].
upd_above HUP HFr AG. clear HF HFr HG.
assert (HMM : MALLOC_MAX = 2 ^ 28) by reflexivity.
clear Kgot2 Kcell2 Kguar2 Kuar2 Vgr2. aconsts HROD HJ2 KgotB KcellB KguarB KuarB VgrB.
rreg HS (10%bv : bv 5) Ra0. rreg HS (1%bv : bv 5) Rra. rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp.
rreg HS (4%bv : bv 5) Rtp. rreg HS (8%bv : bv 5) Rs0.
assert (Qceil : alloc_ceiling <= spZ regs) by lia. assert (Qal8 : spZ regs mod 8 = 0) by (pose proof (Z.div_mod (spZ regs) 32 ltac:(lia)) as D; rewrite Hal32, Z.add_0_r in D; rewrite D; replace (32 * (spZ regs / 32)) with ((4 * (spZ regs / 32)) * 8) by lia; apply Z_mod_mult).
assert (Qtop : spZ regs < ly_top ly - 16) by lia. assert (Qtop64 : ly_top ly <= 2 ^ 64) by lia. assert (Qsp : spZ regs - 192 + 16 <= spZ regs) by lia.
assert (Qra : 0 <= raZ regs < 2 ^ 64) by (unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq).
assert (Qs0 : 0 <= s0Z regs < 2 ^ 64) by (unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq).
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W) msX) 2 _ HS eq_refl) as HRstk; cbn [ms_mem restrict] in HRstk;
lazymatch type of HRstk with region_ok _ _ _ (YQ0b.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-8) 8%N (SOff 1 0) (raZ regs) HRstk
ltac:(evalE AG) ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 1%nat) by lia; rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vra;
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-16) 8%N (SOff 8 0) (s0Z regs) HRstk
ltac:(evalE AG) ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 8%nat) by lia; rewrite (EE 8%nat 8%bv eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vs0 end;
clear HRstk;
assert (Hch1 : achain ly (aview trbsegs (w_H W) (ms_mem msX)) (spZ regs - 192) (spZ regs) ((spZ regs, raZ regs, s0Z regs) :: ch));
[ replace (spZ regs - 8) with (spZ regs + -8) in Vra by lia; replace (spZ regs - 16) with (spZ regs + -16) in Vs0 by lia;
exact (achain_push ly _ _ (spZ regs) (s0Z regs) (raZ regs) _ (spZ regs - 192) Hch Qtop64 HUP
(rdword_of_val_mem trbsegs _ _ _ _ Vra Qra) (rdword_of_val_mem trbsegs _ _ _ _ Vs0 Qs0) Hra4 Qceil Qal8 Qtop Qsp)
| ] end.
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
replace (Z_to_bv 64 340936) with (Z_to_bv 64 (pc_wrap_malloc (as_code B))) by (rewrite HBcode; vm_compute; reflexivity).
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_malloc_at trbsegs B LAWS Hsegs errno_low ML AMALLOC _ (ms_regs msX) (ms_mem msX) TRAWNEW_STK (spZ regs) [] ly S W mem md [(2, fpos)]
ly S2 _ 0 48 (-192) (Z_to_bv 64 0x88f0c) ((spZ regs, raZ regs, s0Z regs) :: ch) HJ2) end.
- exact Ra0.
- rewrite HMM. lia.
- rewrite Hbb2. unfold LIVE_MAX in *. lia.
- unfold spZ. rewrite Rsp. evalE AG.
- reflexivity.
- lia.
- rewrite FFS. unfold ASTACK. lia.
- rewrite Rgp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 3%nat) by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
- rewrite Rtp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 4%nat) by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
- exact Rra.
- vm_compute. reflexivity.
- rewrite Hnev2. rewrite HEV in Hev. unfold VEV_MAX in *. lia.
- apply (achain_chain_pre ly _ (spZ regs - 192) (spZ regs) _ _ Hch1);
[ unfold spZ at 1 2; rewrite Rsp; evalE AG
| unfold s0Z; rewrite Rs0; evalE AG
| unfold raZ; rewrite Rra, unsigned_lit_small by lia; lia ].
- rewrite call_trace_of_spine. cbn [spine map fst snd]. fold (spine ch). unfold raZ at 1. rewrite Rra, unsigned_lit_small by lia. rewrite <- Hra68.
rewrite HBcode, (tl_universe B TL). apply TRACES_cgif_raw_newgif_U. apply memZL_In.
destruct Hspine as [Hsp | Hsp]; rewrite Hsp; vm_compute; reflexivity. }
cbv beta. intros W3 c3 Hwle3 (ly3 & S3 & regs3 & mem3 & md3 & res & -> & HJ3 & HP3 & Ha03 & Hfrs3 & Hres3).
clear Ra0 Rra Rsp Rgp Rtp Rs0 Hch1 HUP Vra Vs0 Qceil Qal8 Qtop Qtop64 Qsp Qra Qs0.
unfold ASTACK in Hres3. replace (spZ regs + -192 - 16384) with (spZ regs - 16576) in Hres3 by lia. replace (spZ regs + -192) with (spZ regs - 192) in Hres3 by lia.
pose proof (proj1 HJ3) as HAR3. aconsts HROD HJ3 Kgot3 Kcell3 Kguar3 Kuar3 Vgr3.
destruct (al_layout _ _ LAWS _ _ _ _ _ ly3 HAR (proj1 (proj2 HJ3))) as (_ & EFA3 & _).
assert (EFL3 : forall c p, flag_addr ly3 c p = flag_addr ly c p) by (intros c p; unfold flag_addr; pose proof (EFA3 c p) as X; unfold frame_addr in X; lia).
assert (Hfin3 : In (2, fpos) (frames S3)) by (rewrite Hfrs3; exact Hfin2).
assert (HfinS3 : In (cid, pos) (frames S3)) by (rewrite Hfrs3; exact HfinS2).
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos HAR3 Hfin3) as (_ & _ & HFpres3 & HFSpres3). change (fs_frame_bytes 2) with 256 in HFpres3, HFSpres3.
change (256 / 8) with 32 in HFSpres3. rewrite !EFA3 in HFpres3, HFSpres3. fold F in HFpres3, HFSpres3.
destruct Hres3 as [(Hres0 & Eab3 & HK3) | (Hres4096 & Eab3 & HK3)].
+
assert (Hing3 : In (g, CGIF_SIZE) (ablocks B ly3 S3)) by (rewrite Eab3, Eab; exact Hing).
assert (Hing2 : In (g, CGIF_SIZE) (ablocks B ly S2)) by (rewrite Eab; exact Hing).
assert (HErF : forall a, F <= a < F + 256 -> ~ False) by (intros a Ha Hn; exact Hn).
reseat HS HJ3 HP3 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9]%nat AG
ltac:(idtac; first [ keptR HK3 HJ3 AG Usp E10 E32 HfinS2 Hing2 KgotB Kgot3 KcellB Kcell3 KguarB Kguar3 KuarB Kuar3 VgrB Vgr3
| keptF HK3 AG RF E58 Hfin2 HFpres3 HFSpres3 HErF F
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
pose proof (st_ok_pin_reg' trbsegs _ _ _ (10%bv : bv 5) 0 HS ltac:(cbn [ms_regs restrict mkst]; rewrite Ha03, Hres0; reflexivity) eq_refl) as HS3.
clear HS. rename HS3 into HS. norm_ss HS. reshok_bx HS 35%nat.
aj_run_to_tok trbtbl_lib_ok HS HJ3 SHOK RBspan 0x8935c; [awrR AG fpos F EFA3|]. clear_frames.
exitR HS HJ3 AG fpos F cfgp g E57 E58 Hfin3 HfinS3 Hing3 EE Hra HEV EFA3 EFL3.
exists 0. split; [reflexivity|]. left. split; [reflexivity|].
unfold ablocks. rewrite blocks_stack_free_state. fold (ablocks B ly3 S3). rewrite Eab3, Eab. apply Permutation_refl.
+
assert (Hres_in : In (res, 48) (ablocks B ly3 S3)) by (rewrite Eab3; apply in_app_iff; right; left; reflexivity).
assert (Hing3 : In (g, CGIF_SIZE) (ablocks B ly3 S3)) by (rewrite Eab3; apply in_app_iff; left; rewrite Eab; exact Hing).
assert (Hing2 : In (g, CGIF_SIZE) (ablocks B ly S2)) by (rewrite Eab; exact Hing).
destruct (al_blocks _ _ LAWS _ _ _ _ _ res 48 HAR3 Hres_in) as (Hr16 & Hr4096 & Hrceil & Hrh_ia & Hrpres & _). pose proof (proj1 Hrh_ia) as Hrh.
pose proof (blk_off_img _ _ _ _ _ _ res 48 HAR3 Hres_in) as Hrh_img.
change (req_size 48) with 48 in Hrceil, Hrpres, Hrh_img.
pose proof (aftok_new_block trbsegs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ res 48 HJ2 HAR3 Eab3 ltac:(lia)) as Tres.
assert (Ares : forall blc lyq ownq i, In (res, 48) blc -> 0 <= i < 48 -> awr_byte TRAWNEW_STK (spZ regs) [] (ablocks B ly S) blc lyq ownq (res + i)).
{ intros blc lyq ownq i Hbl Hi. exact (awr_new_block_any trbsegs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ res 48 blc i lyq ownq HJ2 HAR3 Eab3 ltac:(lia) Hbl ltac:(change (req_size 48) with 48; lia)). }
pose proof (sep_block_frame trbsegs B LAWS ly3 S3 _ _ _ res 48 2 fpos HAR3 Hres_in Hfin3) as HdRF.
unfold zdisjoint in HdRF. cbn [fst snd] in HdRF. change (req_size 48) with 48 in HdRF. change (fs_frame_bytes 2) with 256 in HdRF. rewrite EFA3 in HdRF. fold F in HdRF.
pose proof (sep_block_frame trbsegs B LAWS ly3 S3 _ _ _ res 48 cid pos HAR3 Hres_in HfinS3) as HdRC.
unfold zdisjoint in HdRC. cbn [fst snd] in HdRC. change (req_size 48) with 48 in HdRC. rewrite EFA3 in HdRC.
pose proof (sep_blocks trbsegs B LAWS ly3 S3 _ _ _ g CGIF_SIZE res 48 HAR3 Hing3 Hres_in ltac:(unfold CGIF_SIZE; intros X; injection X; lia)) as HdRG.
unfold zdisjoint in HdRG. cbn [fst snd] in HdRG. change (req_size 48) with 48 in HdRG. change (req_size CGIF_SIZE) with 96 in HdRG.
assert (HErF : forall a, F <= a < F + 256 -> ~ (res <= a < res + req_size 48)) by (change (req_size 48) with 48; intros a Ha; lia).
reseat HS HJ3 HP3 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9]%nat AG
ltac:(idtac; first [ keptR HK3 HJ3 AG Usp E10 E32 HfinS2 Hing2 KgotB Kgot3 KcellB Kcell3 KguarB Kguar3 KuarB Kuar3 VgrB Vgr3
| keptF HK3 AG RF E58 Hfin2 HFpres3 HFSpres3 HErF F
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
rreg HS (10%bv : bv 5) Rres. cbn [ms_regs] in Rres. rewrite Ha03 in Rres. symmetry in Rres. unfold w64 in Rres.
lazymatch type of Rres with ew ?Ex ?nx = _ =>
pose proof (st_ok_add_fact trbsegs Ex _ _ nx (HPTR 4) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite Rres, unsigned_lit_small by lia; change (2 ^ 4) with 16; lia)) as HS3;
clear HS; rename HS3 into HS;
pose proof (ast_ok_add_region trbsegs Ex _ _ (YQ0b.mkRegion (Some nx) 0 48 0 48 []) HS eq_refl
ltac:(unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst];
rewrite Rres, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable trbsegs); apply (proj1 (Hrpres (res + o) ltac:(lia))))
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
rewrite Rres; change (fs_frame_bytes 2) with 256; change (fs_frame_bytes 2 / 8) with 32; evalE AG;
unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob, A_GOT_rawnew, CGIF_SIZE; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS. reshok_bx HS 35%nat.
aj_run_tok trbtbl_lib_ok HS HJ3 SHOK RBspan.
{ lazymatch type of Rres with ew _ ?nx = _ =>
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ nx); [reflexivity | evalE AG | cbn [YQ0b.r_wlo YQ0b.r_whi]; intros a Ha; replace a with (res + (a - res)) by lia; apply Ares; [exact Hres_in | lia] |] end.
awrR AG fpos F EFA3. }
clear HF HFr HG.
rreg HS (10%bv : bv 5) Ra0. rreg HS (11%bv : bv 5) Ra1. rreg HS (12%bv : bv 5) Ra2. rreg HS (1%bv : bv 5) Rra.
rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp.
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
change (Z_to_bv 64 335988) with (Z_to_bv 64 A_asan_memcpy).
destruct (al_frames _ _ LAWS _ _ _ _ _ cid pos (proj1 HJ3) HfinS3) as (_ & _ & HCpres3 & _). rewrite EFA3 in HCpres3.
assert (Qcs : cfgp + 40 <= spZ regs - 192 - ESTACK) by (unfold ESTACK; lia).
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_intrin_at trbsegs B LAWS Hsegs OCpy A_asan_memcpy AMEMCPY _ (ms_regs msX) (ms_mem msX) TRAWNEW_STK (spZ regs) [] ly S W mem md [(2, fpos)]
ly3 S3 _ _ res cfgp 40 (-192) (Z_to_bv 64 0x88f28) HJ3) end.
- rewrite Ra0. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite Rres. reflexivity.
- rewrite Ra1. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 10%nat) by lia. rewrite E10. reflexivity.
- exact Ra2.
- lia. - lia. - lia.
- unfold spZ at 1. rewrite Rsp. evalE AG.
- reflexivity. - lia. - rewrite FFS. unfold ESTACK. lia.
- rewrite Rgp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 3%nat) by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
- rewrite Rtp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 4%nat) by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
- exact Rra.
- vm_compute. reflexivity.
- intros a Ha. split; [replace a with (res + (a - res)) by lia; apply Ares; [exact Hres_in | lia] | unfold ESTACK; lia].
- apply (amem_range_of_block trbsegs B LAWS ly3 S3 _ _ _ res 48 _ _ (proj1 HJ3) Hres_in); change (req_size 48) with 48; lia.
- apply (range_addressable_of_block trbsegs B LAWS ly3 S3 _ _ _ res 48 _ _ (proj1 HJ3) Hres_in); change (req_size 48) with 48; lia.
- intros _. apply (shadow_hull_vis_of_block trbsegs B LAWS ly3 S3 _ _ _ res 48 _ _ (proj1 HJ3) Hres_in); change (req_size 48) with 48; lia.
- split; [lia|]. split; [lia|]. split.
{ intros a Ha. split; [| unfold spZ; rewrite Rsp; evalE AG].
apply (aview_some_of_apresent trbsegs). apply (proj1 (HCpres3 a ltac:(lia))). }
split; [lia|]. split; [apply amem_range_high; zone_lia|]. split.
+ eapply (range_addressable_entry_frame trbsegs B LAWS); [exact HJ3 | exact Hfin | exact Hcid0 | exact Hflo | exact Hfhi | exact Hfal
| intros x Hx; exfalso; exact (inFP_nil x Hx) | exact HAR | exact HRA].
+ intros _. eapply (shadow_hull_vis_of_frame trbsegs B LAWS ly3 S3 _ _ _ cid pos cfgp 40 (proj1 HJ3) HfinS3); [rewrite EFA3; exact Hflo | rewrite EFA3; exact Hfhi | lia]. }
cbv beta. intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & HP4 & Ha04 & Heff & Hfr4 & Hpres4).
clear Ra0 Ra1 Ra2 Rra Rsp Rgp Rtp.
pose proof Hcfg as Hc'. cbn [obj_at LAY_RawConfig] in Hc'.
destruct Hc' as ([V0 _] & [V8 R8] & [V16 R16] & [V24 R24] & [V28 R28] & [V30 R30] & [V32 R32] & [V34 R34] & _).
cbn [fst snd N.to_nat Z.of_N] in V0, V8, V16, V24, V28, V30, V32, V34, R8, R16, R24, R28, R30, R32, R34.
change (2 ^ (8 * 8)) with (2 ^ 64) in R8, R16. change (2 ^ (8 * 4)) with (2 ^ 32) in R24. change (2 ^ (8 * 2)) with 65536 in R28, R30, R32, R34.
lazymatch type of Heff with forall i, _ -> aview _ _ _ _ = aview _ _ ?memT _ =>
let cmove off w v V Vr :=
pose proof (val_mem_moved trbsegs (w_H W3) (w_H W3) memT mem4 (cfgp + off) (res + off) w v
ltac:(intros k Hk; replace (res + off + k) with (res + (off + k)) by lia; replace (cfgp + off + k) with (cfgp + (off + k)) by lia;
apply Heff; cbn [Z.of_nat Pos.to_nat Pos.iter_op Nat.add] in Hk; lia)
(val_mem_entry_frame trbsegs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cid pos (cfgp + off) w v HJ3 Hfin
ltac:(lia) ltac:(cbn [Z.of_nat Pos.to_nat Pos.iter_op Nat.add]; lia) ltac:(intros x Hx HF; exact (inFP_nil x HF)) V)) as Vr in
cmove 0 8%nat A_cgif_writecb V0 W0;
cmove 8 8%nat g V8 W8; cmove 16 8%nat pgct V16 W16; cmove 24 4%nat rattr V24 W24;
cmove 28 2%nat Wd V28 W28; cmove 30 2%nat Hd V30 W30; cmove 32 2%nat sgct V32 W32; cmove 34 2%nat loops V34 W34 end.
rewrite Z.add_0_r in W0.
aconsts HROD HJ4 Kgot4 Kcell4 Kguar4 Kuar4 Vgr4.
destruct (al_blocks _ _ LAWS _ _ _ _ _ res 48 (proj1 HJ4) Hres_in) as (_ & _ & _ & _ & Hrpres4 & _). change (req_size 48) with 48 in Hrpres4.
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos (proj1 HJ4) Hfin3) as (_ & _ & HFpres4 & HFSpres4). change (fs_frame_bytes 2) with 256 in HFpres4, HFSpres4.
change (256 / 8) with 32 in HFSpres4. rewrite !EFA3 in HFpres4, HFSpres4. fold F in HFpres4, HFSpres4.
clear Kgot3 Kcell3 Kguar3 Kuar3 Vgr3. aconsts HROD HJ3 Kgot3 Kcell3 Kguar3 Kuar3 Vgr3.
reseat HS HJ4 HP4 [1; 2; 3; 4; 5; 6; 7; 8; 9; 10]%nat AG
ltac:(idtac; first [ keptI Hfr4 Hpres4 AG Kgot3 Kgot4 Kcell3 Kcell4 Kguar3 Kguar4 Kuar3 Kuar4 Vgr3 Vgr4
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
lazymatch type of HS with st_ok _ ?Ev _ _ =>
lazymatch type of Rres with ew _ ?nx = _ =>
let ckv HE := cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
try rewrite (AG 32%nat) by lia; rewrite HE; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity in
pose proof (ast_ok_add_region trbsegs Ev _ _
(YQ0b.mkRegion (Some nx) 0 48 40 48
[YQ0b.mkChunk 0 (CVal 8 (SLit A_cgif_writecb)); YQ0b.mkChunk 8 (CVal 8 (SOff 32 0)); YQ0b.mkChunk 16 (CVal 8 (SOff 33 0));
YQ0b.mkChunk 24 (CVal 4 (SOff 34 0)); YQ0b.mkChunk 28 (CVal 2 (SOff 36 0)); YQ0b.mkChunk 30 (CVal 2 (SOff 37 0));
YQ0b.mkChunk 32 (CVal 2 (SOff 38 0)); YQ0b.mkChunk 34 (CVal 2 (SOff 39 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst];
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite Rres, unsigned_lit_small by lia;
split; [lia|]; split; [lia|]; split; [intros o Ho; apply (apresent_writable trbsegs); apply (proj1 (Hrpres4 (res + o) ltac:(lia)))|];
apply Forall_cons; [apply (chunk_ok_val trbsegs Ev _ res 0 8 _ A_cgif_writecb); [reflexivity | unfold A_cgif_writecb; zside | zside | rewrite Z.add_0_r; exact W0]|];
apply Forall_cons; [apply (chunk_ok_val trbsegs Ev _ res 8 8 _ g); [ckv E32 | zside | zside | exact W8]|];
apply Forall_cons; [apply (chunk_ok_val trbsegs Ev _ res 16 8 _ pgct); [ckv E33 | zside | zside | exact W16]|];
apply Forall_cons; [apply (chunk_ok_val trbsegs Ev _ res 24 4 _ rattr); [ckv E34 | zside | zside | exact W24]|];
apply Forall_cons; [apply (chunk_ok_val trbsegs Ev _ res 28 2 _ Wd); [ckv E36 | zside | zside | exact W28]|];
apply Forall_cons; [apply (chunk_ok_val trbsegs Ev _ res 30 2 _ Hd); [ckv E37 | zside | zside | exact W30]|];
apply Forall_cons; [apply (chunk_ok_val trbsegs Ev _ res 32 2 _ sgct); [ckv E38 | zside | zside | exact W32]|];
apply Forall_cons; [apply (chunk_ok_val trbsegs Ev _ res 34 2 _ loops); [ckv E39 | zside | zside | exact W34]|];
apply Forall_nil)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
rewrite Rres; change (fs_frame_bytes 2) with 256; change (fs_frame_bytes 2 / 8) with 32; evalE AG;
unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob, A_GOT_rawnew, CGIF_SIZE; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS end end.
norm_ss HS. clear W0 W8 W16 W24 W28 W30 W32 W34 Heff.
lazymatch type of HS with st_ok _ ?Ev ?ssx (restrict _ ?msv) =>
change ssx with ss_B in HS;
eapply (rn_B B TL LAWS AMEMSET (rn_C B TL LAWS (rn_D B TL LAWS AMEMSET (rn_X B TL LAWS ML ASF FFL)) (rn_G B TL LAWS (rn_D B TL LAWS AMEMSET (rn_X B TL LAWS ML ASF FFL))))
ly S W regs mem md _ cfgp g pgct rattr Wd Hd sgct loops ctx rest cid pos E Ev W3 ly3 S3 msv _ _ fpos res);
[ exact HPRE | exact Hal32 | exact HROD
| split; [exact Hfin | split; [exact Hcid0 | split; [exact Hfal | split; [exact Hflo | split; [exact Hfhi | split; [exact Hcal | exact HRA]]]]]]
| exact Hcfg | exact HPerm | exact Hev
| split; [exact EE | split; [exact E10 | split; [exact E32 | exact Usp]]]
| split; [exact AG | repeat (split; [eassumption|]); eassumption]
| split; [exact HJ4 | split; [clear; lia | split; [rewrite Hfrs3, Hfrs2; reflexivity | split; [rewrite Eab3, Eab; reflexivity | split; [exact Hres4096 | split; [exact Tres | exact Ares]]]]]]
| exact Hsg | exact HS ] end.
Qed.
End RN.
End b.
