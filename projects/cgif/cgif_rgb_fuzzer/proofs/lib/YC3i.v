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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI03 YI04 YI1i YI20.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YC04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YC19 YF8z YC1d YC1a YC2o YC10 YC2p YC0x YC1b YC2u YC3p YC3q YC3j YC3m YC3l YC3k YC3n YC3o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section NG.
Variable B : asyms.
Hypothesis TL : TraLib B.
Hypothesis LAWS : AR_laws trasegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AMALLOC : amalloc_realizes trasegs B.
Hypothesis AFREE : afree_realizes trasegs B.
Hypothesis AMEMSET : aintrin_realizes trasegs B OSet A_asan_memset.
Hypothesis AMEMCPY : aintrin_realizes trasegs B OCpy A_asan_memcpy.
Hypothesis ASM1 : astack_malloc_realizes trasegs B 1.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASF : astack_free_law trasegs B.
Hypothesis FFL : frame_flag_lawP trasegs B.
Hypothesis RAWNEW : trawnew_spec B.
Let HBcode := tl_code B TL. Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL.
Let HBguar := tl_got_uar B TL. Let HBuar := tl_uar_cell B TL. Let errno_low := tl_env B TL.
Local Notation code := (as_code B).
Lemma ng_main : NG_B_stmt B -> tnewgif_spec B.
Proof.
unfold tnewgif_spec.
intros NGB ly S W regs mem md ch cfgp pal0 pala attr gen Wd Hd ngp loops rest HPRE Hal32 Hctx Hroom Htop32 HROD H10 HFO Hcfg HWH Hpala HPerm Hev Hlive.
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs.
pose proof (ng_entry B TL LAWS W ly S regs mem md ch cfgp pal0 attr gen Wd Hd ngp loops HPRE Hal32 HROD H10 HFO Hcfg) as HS.
pose proof (ajournal_init trasegs B TNEWGIF_STK [] ly S W regs mem md ch HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5). assert (FFS : TNEWGIF_STK = 16768) by reflexivity.
assert (HEV : EV_NEWGIF = 12) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
destruct HFO as ((cid & pos & Hfin & Hcid0 & Hfal & Hflo & Hfhi) & Hcal & HRA).
destruct (frames_bounds trasegs B LAWS ly S W mem md cid pos HAR Hfin) as (Hf4096 & Hfceil & Hfhigh).
pose proof (frm_off_img _ _ _ _ _ _ _ _ HAR Hfin) as Hfhigh_img.
assert (EFA0 : forall c p, frame_addr ly c p = frame_addr ly c p) by reflexivity. assert (EFL0 : forall c p, flag_addr ly c p = flag_addr ly c p) by reflexivity.
remember (Ereg regs (ng_extra pal0 attr gen Wd Hd ngp loops)) as E eqn:HE.
assert (E1 : ew E 1 = getr regs 1) by (subst E; exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (subst E; exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (subst E; exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E8 : ew E 8 = getr regs 8) by (subst E; exact (ew_Ereg_nat regs _ 8 8%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 cfgp) by (subst E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (EX : forall j, ew E (32 + j) = nth j (ng_extra pal0 attr gen Wd Hd ngp loops) (Z_to_bv 64 0)) by (intros j; subst E; apply ew_Ereg_extra).
pose proof (EX 0%nat) as E32. pose proof (EX 1%nat) as E33. pose proof (EX 2%nat) as E34. pose proof (EX 3%nat) as E35.
pose proof (EX 4%nat) as E36. pose proof (EX 5%nat) as E37. pose proof (EX 6%nat) as E38. pose proof (EX 7%nat) as E39. pose proof (EX 8%nat) as E40.
cbn [Nat.add nth ng_extra map] in E32, E33, E34, E35, E36, E37, E38, E39, E40. clear EX.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r) by (intros n r Hn; rewrite HE; apply ew_Ereg_nat; exact Hn).
clear HE.
cbn [CTX_cgif_newgif In] in Hctx.
assert (Hra88 : 0x81de4 = raZ regs) by (destruct Hctx as [H | [H | []]]; injection H as Hr Hs; exact Hr).
assert (Hspine : spine ch = [0x81338] \/ spine ch = [0x81338; 0x80ea8])
by (destruct Hctx as [H | [H | []]]; injection H as Hr Hs; rewrite <- Hs; [left | right]; reflexivity).
unfold cfg_at. change (w64 A_cgif_newgif) with (Z_to_bv 64 A_cgif_newgif).
shok_auto SHOK NBx E (mrestrict (w_H W) mem).
aj_run_tok tratbl_lib_ok HS HJ SHOK NBspan. { awr_ok_tac. exact Usp. }
lazymatch type of HFr with frame_of ?Ef ?rs (mrestrict _ _) (mrestrict _ (ms_mem ?msX)) =>
assert (HUP : forall a, spZ regs <= a < 2 ^ 64 -> aview trasegs (w_H W) (ms_mem msX) a = aview trasegs (w_H W) mem a);
[ eapply (aview_kept_frame Ef rs _ _ _ (spZ regs) HFr); [lia|];
intros a Ha (rg & Hin & Hrg);
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In rg rs1) in Hin end; cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin]; [cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val] in Hrg; rewrite ?Usp in Hrg; lia|]);
match goal with |- ?g => match type of Hin with ?t => idtac "HUPLEFT" t end end; destruct Hin | ] end.
clear HF HFr HG.
aconsts HROD HJ Kgot0 Kcell0 Kguar0 Kuar0 Vgr0.
rreg HS (2%bv : bv 5) R2. rreg HS (3%bv : bv 5) R3. rreg HS (4%bv : bv 5) R4. rreg HS (1%bv : bv 5) R1.
rewrite (st_ok_restrict_mkst trasegs _ _ _ _ HS eq_refl). cbn [ss_pc].
replace 249516 with (pc_stack_malloc code 1) by (rewrite HBcode; reflexivity).
pose proof (count_cid_le_length 1 (frames S)) as Hcnt.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_stack_malloc_at trasegs B LAWS Hsegs errno_low ML SMP 1 ASM1 ltac:(lia) W (ms_regs msX) (ms_mem msX) TNEWGIF_STK (spZ regs) [] ly S W mem md [] ly S _ 0 (-192) _ HJ) end.
- unfold spZ. rewrite R2, E2. fold (spZ regs). rewrite unsigned_lit_small by lia. lia.
- reflexivity. - lia. - rewrite FFS, Hes; lia.
- rewrite R3, E3. exact Hgp. - rewrite R4, E4. exact Htp.
- exact R1. - vm_compute. reflexivity.
- change (fs_frames 1) with 8192. lia. }
cbv beta. clear R2 R3 R4 R1 HJ SHOK.
intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & fpos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2 & Hbb2 & Hz & Hflag & HK).
rewrite Hes in HK. replace (spZ regs + -192 - 4096) with (spZ regs - 4288) in HK by lia. replace (spZ regs + -192) with (spZ regs - 192) in HK by lia.
assert (HUP2 : forall a, spZ regs <= a < 2 ^ 64 -> aview trasegs (w_H W) mem2 a = aview trasegs (w_H W) mem a).
{ intros a Ha. rewrite <- (HUP a Ha). pose proof HK as (K1 & _). apply K1; lia. }
clear HUP.
aconsts HROD HJ2 Kgot2 Kcell2 Kguar2 Kuar2 Vgr2.
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
assert (AG : forall n, (n < 33)%nat -> ew E n = ew E n) by (intros; reflexivity).
reseat HS HJ2 HP2 [0; 1; 2; 3; 4; 5; 6]%nat AG
ltac:(idtac; first [ keptR HK HJ2 AG Usp E10 E32 Hfin I Kgot0 Kgot2 Kcell0 Kcell2 Kguar0 Kguar2 Kuar0 Kuar2 Vgr0 Vgr2 EFA0 | match goal with |- ?g => idtac "KEPTFAIL" g end; fail ]).
rreg HS (10%bv : bv 5) RF. cbn [ms_regs] in RF. rewrite Ha0 in RF. symmetry in RF. unfold w64 in RF. fold F in RF.
lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
pose proof (st_ok_agree trasegs 57 Ev (havoc Ev 57 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)]) ssv msv HS
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
destruct (FFL ly S2 W mem2 md2 1 fpos HAR2 Hfin2) as (HFLpres & HFLown & HFLrng). fold FL in HFLpres, HFLown, HFLrng.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
pose proof (st_ok_add_fact trasegs Ev _ _ 45 (HPTR 5) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite RF, unsigned_lit_small by lia; change (2 ^ 5) with 32; lia)) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_add_fact trasegs Ev _ _ 57 (HPTR 0) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite E57, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_add_fact trasegs Ev _ _ 58 (mkAF (SB + 512) (SB + 17592186044416) 2) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E58, unsigned_lit_small by (unfold SB; lia); change (2 ^ 2) with 4; unfold SB;
split; [lia|]; split; [rewrite HF8; replace (2147450880 + 4 * (F / 32)) with ((536862720 + F / 32) * 4) by lia; apply Z_mod_mult | lia])) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_add_alias trasegs Ev _ _ _ _ HS (shadow_decl_ok Ev 45 35 58 F SB RF ltac:(lia) E35 E58)) as HS3;
clear HS; rename HS3 into HS;
pose proof (ast_ok_add_region trasegs Ev _ _ (fframe_region 45 57 1 []) HS eq_refl
ltac:(unfold region_ok, fframe_region; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst app];
change (fs_frame_bytes 1) with 128; rewrite RF, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split;
[ intros o Ho; apply (apresent_writable trasegs); apply (proj1 (HFpres (F + o) ltac:(lia)))
| apply Forall_cons; [|apply Forall_nil]; apply (chunk_ok_val trasegs Ev _ F (128 - 8) 8 _ FL);
[cbn [sv_denot]; rewrite E57, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | replace (F + (128 - 8)) with (F + 128 - 8) by lia; exact (val_mem_of_rdword trasegs _ _ _ _ Hflag)] ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint, fframe_region; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
change (fs_frame_bytes 1) with 128;
rewrite RF, ?(AG 2%nat), ?(AG 10%nat), ?(AG 32%nat), ?Usp, ?E10, ?E32, !unsigned_lit_small by lia; unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob, A_GOT_newgif;
repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS end.
assert (ZS : forall j, 0 <= j < 2 -> val_mem trasegs (mrestrict (w_H W) mem2) (SB + F / 8 + 8 * j) 8 0).
{ intros j Hj. apply val_mem_zero8. intros i Hi. unfold zero_shadow, shadow_of_addr in Hz. rewrite <- SB_SHADOW_OFF in Hz.
replace (SB + F / 8 + 8 * j + i) with (SB + F / 8 + (8 * j + i)) by lia. apply Hz. change (128 / 8) with 16. lia. }
lazymatch type of HS with st_ok _ ?Ev _ _ =>
pose proof (ast_ok_add_region trasegs Ev _ _
(fshadow_region 58 1 0 16 [YQ0b.mkChunk 0 (CVal 8 (SLit 0)); YQ0b.mkChunk 8 (CVal 8 (SLit 0))]) HS eq_refl
ltac:(unfold region_ok, fshadow_region; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst app];
change (fs_frame_bytes 1 / 8) with 16; rewrite E58, unsigned_lit_small by (unfold SB; lia); split; [unfold SB; lia|]; split; [unfold SB; lia|]; split;
[ intros o Ho; apply (apresent_writable trasegs); unfold shadow_addr in HFSpres; rewrite <- SB_SHADOW_OFF in HFSpres;
replace (SB + F / 8 + o) with (SB + F / 8 + o) by lia; apply (proj1 (HFSpres o ltac:(change (128 / 8) with 16; lia)))
| apply Forall_cons; [apply (chunk_ok_val trasegs Ev _ (SB + F / 8) 0 8 _ 0); [reflexivity | zside | zside | rewrite Z.add_0_r; replace (SB + F / 8) with (SB + F / 8 + 8 * 0) by lia; apply ZS; lia]|];
apply Forall_cons; [apply (chunk_ok_val trasegs Ev _ (SB + F / 8) 8 8 _ 0); [reflexivity | zside | zside | replace (SB + F / 8 + 8) with (SB + F / 8 + 8 * 1) by lia; apply ZS; lia]|];
apply Forall_nil ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint, fshadow_region; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
change (fs_frame_bytes 1 / 8) with 16;
rewrite E58, RF, ?(AG 2%nat), ?(AG 10%nat), ?(AG 32%nat), ?Usp, ?E10, ?E32, !unsigned_lit_small by (unfold SB; lia);
unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob, A_GOT_newgif, SB; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
aj_run_to_sh tratbl_lib_ok HS HJ2 0x856ec. { awrR AG fpos F EFA0. }
upd_above HUP2 HFr AG. rename HUP2 into HUP.
clear HF HFr HG.
fs_ro HS. reshok_bx HS 35%nat.
aj_run_tok tratbl_lib_ok HS HJ2 SHOK NBspan; [awrR AG fpos F EFA0 |].
upd_above HUP HFr AG. clear HF HFr HG.
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W) msX) 0 _ HS eq_refl) as HRfs; cbn [ms_mem restrict] in HRfs;
lazymatch type of HRfs with region_ok _ _ _ (YQ0b.mkRegion (Some 58%nat) ?lo ?hi ?wlo ?whi ?cs) =>
assert (ZS5 : forall j, 4 <= j <= 8 -> val_mem trasegs (mrestrict (w_H W) (ms_mem msX)) (SB + F / 8 + j) 1 0);
[ intros j Hj;
assert (Hj5 : j = 4 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 8) by lia;
destruct Hj5 as [-> | [-> | [-> | [-> | ->]]]];
(eapply (field_of_region Ex _ 58 (SB + F / 8) cs lo hi wlo whi _ 1%N (SLit 0) 0 HRfs);
[evalE AG | cbn; tauto | reflexivity | cbn; lia | cbn; lia])
| ] end;
clear HRfs;
assert (HRA40 : range_addressable (aview trasegs (w_H W) (ms_mem msX)) SHADOW_OFF (F + 32) 40);
[ apply zero_shadow_range; [rewrite HFq; replace (32 * (F / 32) + 32) with ((4 * (F / 32) + 4) * 8) by lia; apply Z_mod_mult | reflexivity |];
intros i Hi; change (40 / 8) with 5 in Hi; unfold shadow_of_addr; rewrite <- SB_SHADOW_OFF;
replace (SB + (F + 32) / 8 + i) with (SB + F / 8 + (4 + i)) by (rewrite HFq at 2; rewrite HF8; replace (32 * (F / 32) + 32) with ((4 * (F / 32) + 4) * 8) by lia; rewrite Z.div_mul by lia; lia);
apply (aview_of_val_mem1 trasegs); [apply ZS5; lia | lia]
| ] end.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
assert (Hpres2F : forall a, F <= a < F + 128 -> apresent (w_H W) (ms_mem msX) a) end.
{ destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos (proj1 HJ2) Hfin2) as (_ & _ & HFpresX & _). change (fs_frame_bytes 1) with 128 in HFpresX. fold F in HFpresX.
intros a Ha. exact (proj1 (HFpresX a Ha)). }
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 45%nat in let i := eval vm_compute in i in
pose proof (st_ok_submem trasegs Ex ssx msx (firstn i (ss_mem ssx) ++ trim_lo (nth i (ss_mem ssx) got_region) 72 :: skipn (Datatypes.S i) (ss_mem ssx)) HS
ltac:(cbn [ss_mem nth skipn firstn app]; repeat (apply submem_keep; [first [apply subregion_trim_lo | apply subregion_refl]|]); apply submem_refl)
ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
lazymatch type of HS with st_ok _ ?Ex _ _ =>
pose proof (ast_ok_add_region trasegs Ex _ _ (YQ0b.mkRegion (Some 45%nat) 0 32 0 32 []) HS eq_refl
ltac:(unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst];
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
rewrite RF, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable trasegs); apply Hpres2F; lia)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
rewrite RF; evalE AG; unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob, A_GOT_newgif; repeat split; first [zone_lia | match goal with |- ?g => idtac "DISJ" g; fail end])) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS. reshok_bx HS 35%nat.
rreg HS (10%bv : bv 5) Ra0. rreg HS (11%bv : bv 5) Ra1. rreg HS (12%bv : bv 5) Ra2. rreg HS (1%bv : bv 5) Rra.
rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp.
rewrite (st_ok_restrict_mkst trasegs _ _ _ _ HS eq_refl). cbn [ss_pc].
change (Z_to_bv 64 336460) with (Z_to_bv 64 A_asan_memset).
clear Kgot2 Kcell2 Kguar2 Kuar2 Vgr2. aconsts HROD HJ2 Kgot2 Kcell2 Kguar2 Kuar2 Vgr2.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_intrin_at trasegs B LAWS Hsegs OSet A_asan_memset AMEMSET _ (ms_regs msX) (ms_mem msX) TNEWGIF_STK (spZ regs) [] ly S W mem md [(1, fpos)]
ly S2 _ _ (F + 32) 0 40 (-192) (Z_to_bv 64 0x856fc) HJ2) end.
- rewrite Ra0. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite RF. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
- exact Ra1.
- exact Ra2.
- lia. - lia. - lia.
- unfold spZ at 1. rewrite Rsp. evalE AG.
- reflexivity. - lia. - rewrite FFS. unfold ESTACK. lia.
- rewrite Rgp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 3%nat) by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
- rewrite Rtp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 4%nat) by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
- exact Rra.
- vm_compute. reflexivity.
- intros a Ha. split; [| unfold ESTACK; lia]. right. right. right. exists 1, fpos. split; [left; reflexivity|]. left.
unfold in_zr, frame_rng. cbn [fst snd]. change (fs_frame_bytes 1) with 128. fold F. lia.
- apply amem_range_high; zone_lia.
- exact HRA40.
- intros _. eapply (shadow_hull_vis_of_frame trasegs B LAWS ly S2 _ _ _ 1 fpos (F + 32) 40 (proj1 HJ2) Hfin2);
[fold F; lia | fold F; change (fs_frame_bytes 1) with 128; lia | lia].
- exact I. }
cbv beta. intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & HP4 & Ha04 & Heff & Hfr4 & Hpres4).
clear Ra0 Ra1 Ra2 Rra Rsp Rgp Rtp ZS5 HRA40.
aconsts HROD HJ4 Kgot4 Kcell4 Kguar4 Kuar4 Vgr4.
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos (proj1 HJ4) Hfin2) as (_ & _ & HFpres4 & HFSpres4). change (fs_frame_bytes 1) with 128 in HFpres4, HFSpres4.
change (128 / 8) with 16 in HFSpres4. fold F in HFpres4, HFSpres4.
reseat HS HJ4 HP4 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9]%nat AG
ltac:(idtac; first [ keptI Hfr4 Hpres4 AG Kgot2 Kgot4 Kcell2 Kcell4 Kguar2 Kguar4 Kuar2 Kuar4 Vgr2 Vgr4
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos (proj1 HJ4) Hfin2) as (_ & _ & HFpres4' & _). change (fs_frame_bytes 1) with 128 in HFpres4'. fold F in HFpres4'.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
pose proof (ast_ok_add_region trasegs Ev _ _ (YQ0b.mkRegion (Some 45%nat) 32 72 32 72 []) HS eq_refl
ltac:(unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst];
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
rewrite RF, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable trasegs); apply (proj1 (HFpres4' (F + o) ltac:(lia))))
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
rewrite RF; evalE AG; unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob, A_GOT_newgif; repeat split; first [zone_lia | match goal with |- ?g => idtac "DISJ" g; fail end])) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS. reshok_bx HS 35%nat. clear_frames.
lazymatch type of HS with st_ok _ ?Ev ?ssx (restrict _ ?msv) =>
change ssx with ss_NB in HS;
eapply (NGB ly S W regs mem md ch cfgp pal0 pala attr gen Wd Hd ngp loops rest cid pos E Ev W ly S2 msv _ 0 fpos);
[ split; [exact HPRE | split; [exact Hal32 | split; [| split; [exact Hroom | split; [exact Htop32 | split; [exact HROD | split; [exact Hcfg | split; [exact HWH | split; [exact Hpala | split; [exact HPerm | split; [exact Hev | exact Hlive]]]]]]]]]]]
| split; [exact Hfin | split; [exact Hcid0 | split; [exact Hfal | split; [exact Hflo | split; [exact Hfhi | split; [exact Hcal | exact HRA]]]]]]
| split; [exact EE | split; [exact E10 | split; [exact E32 | exact Usp]]]
| split; [exact AG | repeat (split; [eassumption|]); eassumption]
| split; [exact HJ4 | split; [clear; lia | split; [exact Hfrs2 | exact Eab]]]
| exact HS ] end.
rewrite <- Hra88. destruct Hspine as [Hs | Hs]; rewrite Hs; cbn; tauto.
Qed.
Theorem tra_cgif_newgif : tnewgif_spec B.
Proof.
apply ng_main. apply ng_B; try assumption. apply ng_M; try assumption. apply ng_K; try assumption.
- apply ng_P0; assumption.
- apply ng_G; try assumption. apply ng_P1; assumption.
Qed.
End NG. End b.
