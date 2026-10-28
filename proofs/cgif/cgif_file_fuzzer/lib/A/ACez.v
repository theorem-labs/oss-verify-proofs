(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI08 YI0n.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YC85.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI5w YI5z.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v ACef AF0l ACej ACeh ACem ACek ACei ACep.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCeo.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACer ACfm ACf5 ACf9 ACf7.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {ROB : ACeh.ro_tfa_below_ofl}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASM2 : astack_malloc_realizes tfibsegs B 2.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis FFL : frame_flag_lawP tfibsegs B.
Let HBcode := tl_code B TL. Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL.
Let HBguar := tl_got_uar B TL. Let HBuar := tl_uar_cell B TL. Let errno_low := tl_env B TL.
Local Notation code := (as_code B).
Hypothesis MTF : ameter_fs_laws MT.
Variable FP : list (Z * Z).
Variable POST : rtcx -> world tfibsegs -> config -> Prop.
Hypothesis RB : rt_from B MT FP POST ss_A2 (INV_0 B MT 0).
Theorem tfib_lib_A_seg : forall ly S (W : world tfibsegs) (regs : bvmap 5 word) mem md p n T,
afn_pre tfibsegs B LLVMF_STK ly S W regs mem md [] ->
raZ regs = RA_LLVMF ->
getr regs 10 = w64 p -> getr regs 11 = w64 n ->
((n = 0 /\ p = A_EMPTY) \/ (0 < n < 2 ^ 26 /\ In (p, n) (ablocks B ly S))) ->
frames S = [] -> st_nev S + EV_LIB <= EV_MAX -> blocks_bytes S + LIVE_LIB <= LIVE_MAX ->
arodata_ok B (aview tfibsegs (w_H W) mem) ->
mo_ok MT S T -> RT_NEED1 MT <= T ->
SRr tfibsegs W (cfg_at tfibsegs A_LLVMF regs mem md)
(fun W' c' => exists fpos sp1 E0, POST (mkRTCX ly S W regs mem md p n fpos sp1 E0 T) W' c').
Proof.
intros ly S W regs mem md p n T HPRE Hra Hp Hn Hpn Hfr0 Hev Hlive HROD HMOK HNEED.
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof (rt_entry B TL LAWS W ly S regs mem md p n HPRE Hp Hn Hpn) as HS.
pose proof (ajournal_init tfibsegs B LLVMF_STK FP ly S W regs mem md [] HPRE) as HJ.
pose proof HPRE as (HAR & Hra1 & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5). assert (FFS : LLVMF_STK = 32768) by reflexivity.
assert (HEV : EV_LIB = 2000) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
assert (Hn26 : 0 <= n < 2 ^ 26) by (destruct Hpn as [[-> _] | [Hn' _]]; lia).
remember (Ereg regs rt_extra) as E eqn:HE.
assert (E1 : ew E 1 = getr regs 1) by (subst E; exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (subst E; exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (subst E; exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E8 : ew E 8 = getr regs 8) by (subst E; exact (ew_Ereg_nat regs _ 8 8%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 p) by (subst E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact Hp).
assert (E11 : ew E 11 = Z_to_bv 64 n) by (subst E; rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs rt_extra) E) by (rewrite HE; split; [intros nn Hnn; reflexivity | reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r) by (intros nn r Hnn; rewrite HE; apply ew_Ereg_nat; exact Hnn).
clear HE.
unfold cfg_at. change (w64 A_LLVMF) with (Z_to_bv 64 A_LLVMF).
shok_auto SHOK RTBx E (mrestrict (w_H W) mem).
assert (AG : forall n, (n < 33)%nat -> ew E n = ew E n) by (intros; reflexivity).
assert (EFA0 : forall c p, frame_addr ly c p = frame_addr ly c p) by reflexivity.
aj_run_to_tok tfibtbl_lib_ok HS HJ SHOK RTBspan 0x804d0. { awrRT AG 0 0 EFA0. }
upd_aboveW_init HFr AG HUP. clear_frames.
set (sp1 := 32 * ((spZ regs + -128) / 32)).
destruct (sp1_facts (spZ regs + -128) ltac:(clear - Hceil Hslo Hstk0 FFS C1; lia)
ltac:(rewrite <- Zplus_mod_idemp_l, Hal16; reflexivity)) as (Hsp1r & Hsp1al & Hsp1al16). fold sp1 in Hsp1r, Hsp1al, Hsp1al16.
assert (Hsp1 : spZ regs - 144 <= sp1 <= spZ regs - 128) by (clear - Hsp1r; lia). clear Hsp1r.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
rreg_by HS (2%bv : bv 5) (Z_to_bv 64 sp1)
(denot_and_m32 Ev 2 (spZ regs) (-128) ltac:(rewrite E2; symmetry; apply Z_to_bv_bv_unsigned)
ltac:(clear - Hceil Hslo Hstk0 FFS C1; lia) ltac:(clear - Hshi H47; lia) ltac:(clear - Hceil Hslo Hstk0 FFS C1 Hshi H47; lia)) R2 end.
lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
pose proof (st_ok_agree tfibsegs 70 Ev (havoc Ev 70 [Z_to_bv 64 sp1]) ssv msv HS
(env_agree_havoc_ge 70 70 Ev Ev _ ltac:(lia) (env_agree_refl 70 Ev)) ltac:(vm_compute; reflexivity)) as HS3 end.
clear HS. rename HS3 into HS. rebaseE HS AG HEv.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
assert (E70 : ew Ev 70 = Z_to_bv 64 sp1) by (rewrite HEv; exact (ew_havoc_new _ 70 [Z_to_bv 64 sp1] 0 (Z_to_bv 64 0) ltac:(cbn; lia))) end.
clear HEv.
lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
pose proof (ast_ok_set_reg_fp tfibsegs Ev ssx msx (2%bv : bv 5) (SOff 70 0) HS ltac:(vm_compute; reflexivity)
ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite E70, Z.add_0_r, R2; rewrite unsigned_lit_small by (clear - Hsp1 Hceil Hslo Hstk0 FFS C1 Hshi H47; lia); reflexivity)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS. clear R2.
lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
pose proof (st_ok_add_fact tfibsegs Ev ssx msx 70%nat (mkAF (2 ^ 46 - 512) (2 ^ 47) 5) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E70, unsigned_lit_small by (clear - Hsp1 Hceil Hslo Hstk0 FFS C1 Hshi H47; lia); change (2 ^ 5) with 32;
clear - Hsp1 Hsp1al Hslo Hstk0 Hshi H47 Hceil FFS C1 C3; lia)) as HS3;
clear HS; rename HS3 into HS end.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let rs' := eval vm_compute in (trim_stack rs (-96) 0) in
pose proof (st_ok_submem tfibsegs Ex ssx (restrict (w_H W) msX) rs' HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
pose proof (ast_ok_add_region tfibsegs Ev _ _ (YP09.mkRegion (Some 70%nat) 0 32 0 32 []) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite E70, unsigned_lit_small by (clear - Hsp1 Hceil Hslo Hstk0 FFS C1 Hshi H47; lia); split; [clear - Hsp1 Hceil Hslo Hstk0 FFS C1; lia|]; split; [clear - Hsp1 Hshi H47; lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable tfibsegs); apply HJpres; rewrite FFS; clear - Ho Hsp1; lia)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
evalE AG; unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob;
clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1; repeat split; zone_lia)) as HS3; clear HJpres;
clear HS; rename HS3 into HS end.
norm_ss HS.
reshok HS. unfold RTBx in *.
aj_run_tok tfibtbl_lib_ok HS HJ SHOK RTBspan. { awrRT AG 0 0 EFA0. }
upd_aboveW HUP HFr AG. clear HF HFr HG.
aconstsF HJ Kgot0 Kcell0 Kguar0 Kuar0.
rreg HS (2%bv : bv 5) R2. rreg HS (3%bv : bv 5) R3. rreg HS (4%bv : bv 5) R4. rreg HS (1%bv : bv 5) R1.
rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
replace 248372 with (pc_stack_malloc code 2) by (rewrite HBcode; reflexivity).
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_stack_malloc_atS tfibsegs B LAWS Hsegs errno_low ML SMP 2 ASM2 ltac:(lia) W (ms_regs msX) (ms_mem msX) LLVMF_STK (spZ regs) FP ly S W mem md [] ly S _ 0 (sp1 - spZ regs) _ HJ) end.
- unfold spZ at 1. rewrite R2. evalE AG.
- rewrite <- Zminus_mod_idemp_l, Hsp1al16, <- Zminus_mod_idemp_r, Hal16. reflexivity.
- clear - Hsp1; lia. - rewrite FFS, Hes; clear - Hsp1; lia.
- rewrite R3. evalE AG. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp. - rewrite R4. evalE AG. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
- exact R1. - vm_compute. reflexivity.
- rewrite Hfr0. change (fs_frames 2) with 4096. cbn. clear; lia. }
cbv beta. clear R2 R3 R4 R1 HJ SHOK.
intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & fpos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2 & Hbb2 & Hz & Hflag & HK & _ & (fS2 & ES2)).
rewrite Hes in HK. replace (spZ regs + (sp1 - spZ regs) - 4096) with (sp1 - 4096) in HK by (clear; lia).
replace (spZ regs + (sp1 - spZ regs)) with sp1 in HK by (clear; lia).
assert (HUP2 : forall a, spZ regs <= a < 2 ^ 64 -> aview tfibsegs (w_H W) mem2 a = aview tfibsegs (w_H W) mem a).
{ intros a Ha. rewrite <- (HUP a Ha). pose proof HK as (K1 & _). apply K1; clear - Ha Hsp1 Hceil Hslo Hstk0 FFS C1; lia. }
clear HUP. rename HUP2 into HUP.
aconstsF HJ2 Kgot2 Kcell2 Kguar2 Kuar2.
pose proof (proj1 HJ2) as HAR2.
assert (Hfin2 : In (2, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos HAR2 Hfin2) as (HFal & [HFhi _] & HFpres & HFSpres).
pose proof (frm_off_img _ _ _ _ _ _ _ _ HAR2 Hfin2) as Hfin2_img.
destruct (frames_bounds tfibsegs B LAWS _ _ _ _ _ 2 fpos HAR2 Hfin2) as (HF4096 & HFceil & HFhigh).
pose proof (frm_off_img _ _ _ _ _ _ _ _ HAR2 Hfin2) as HFhigh_img.
change (fs_frame_bytes 2) with 256 in *.
set (F := frame_addr ly 2 fpos) in *. set (FL := flag_addr ly 2 fpos) in *.
reseat HS HJ2 HP2 [0; 1; 2; 3; 4; 5]%nat AG
ltac:(idtac; first [keptRT HK HJ2 AG Kgot0 Kgot2 Kcell0 Kcell2 Kguar0 Kguar2 Kuar0 Kuar2 ltac:(idtac; fail) ltac:(idtac; fail) | match goal with |- ?g => idtac "KEPTFAIL" g end]).
rreg HS (10%bv : bv 5) RF. cbn [ms_regs] in RF. rewrite Ha0 in RF. symmetry in RF. unfold w64 in RF. fold F in RF.
lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
pose proof (st_ok_agree tfibsegs 87 Ev (havoc Ev 87 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)]) ssv msv HS
(env_agree_havoc_ge 87 87 Ev Ev _ ltac:(lia) (env_agree_refl 87 Ev)) ltac:(vm_compute; reflexivity)) as HS3 end.
clear HS. rename HS3 into HS. rebaseE HS AG HEv.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
assert (E87 : ew Ev 87 = Z_to_bv 64 FL) by (rewrite HEv; exact (ew_havoc_new _ 87 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 0 (Z_to_bv 64 0) ltac:(cbn; lia)));
assert (E88 : ew Ev 88 = Z_to_bv 64 (SB + F / 8)) by (rewrite HEv; exact (ew_havoc_new _ 87 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 1 (Z_to_bv 64 0) ltac:(cbn; lia))) end.
clear HEv.
lazymatch type of HS with st_ok _ ?Ev _ _ => assert (E32' : ew Ev 32 = Z_to_bv 64 SB) by (rewrite (AG 32%nat) by lia; exact E32) end.
assert (HFq : F = 32 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(lia)); lia).
assert (HF8 : F / 8 = 4 * (F / 32)) by (rewrite HFq at 1; replace (32 * (F / 32)) with (4 * (F / 32) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
assert (HF8lo : 512 <= F / 8) by (apply Z.div_le_lower_bound; lia)    .
assert (HF8hi : F / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia).
destruct (FFL ly S2 W mem2 md2 2 fpos HAR2 Hfin2) as (HFLpres & HFLown & HFLrng). fold FL in HFLpres, HFLown, HFLrng.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
pose proof (st_ok_add_fact tfibsegs Ev _ _ 75 (HPTR 5) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite RF, unsigned_lit_small by lia; change (2 ^ 5) with 32; lia)) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_add_fact tfibsegs Ev _ _ 87 (HPTR 0) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite E87, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_add_fact tfibsegs Ev _ _ 88 (mkAF (SB + 512) (SB + 17592186044416) 2) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E88, unsigned_lit_small by (unfold SB; lia); change (2 ^ 2) with 4; unfold SB;
split; [lia|]; split; [rewrite HF8; replace (2147450880 + 4 * (F / 32)) with ((536862720 + F / 32) * 4) by lia; apply Z_mod_mult | lia])) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_add_alias tfibsegs Ev _ _ _ _ HS (shadow_decl_ok Ev 75 32 88 F SB RF ltac:(lia) E32' E88)) as HS3;
clear HS; rename HS3 into HS;
pose proof (ast_ok_add_region tfibsegs Ev _ _ (YP09.mkRegion (Some 75%nat) 0 256 0 256 [YP09.mkChunk 248 (CVal 8 (SOff 87 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
rewrite RF, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split;
[ intros o Ho; apply (apresent_writable tfibsegs); apply (proj1 (HFpres (F + o) ltac:(lia)))
| apply Forall_cons; [|apply Forall_nil]; apply (chunk_ok_val tfibsegs Ev _ F 248 8 _ FL);
[cbn [sv_denot]; rewrite E87, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | replace (F + 248) with (F + 256 - 8) by lia; exact (val_mem_of_rdword tfibsegs _ _ _ _ Hflag)] ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite RF; evalE AG; unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob;
clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 C3 HF4096 HFceil HFhigh HFhigh_img; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS end.
assert (ZS : forall j, 0 <= j < 4 -> val_mem tfibsegs (mrestrict (w_H W) mem2) (SB + F / 8 + 8 * j) 8 0).
{ intros j Hj. apply val_mem_zero8. intros ii Hii. unfold zero_shadow, shadow_of_addr in Hz. rewrite <- SB_SHADOW_OFF in Hz.
replace (SB + F / 8 + 8 * j + ii) with (SB + F / 8 + (8 * j + ii)) by lia. apply Hz. change (256 / 8) with 32. lia. }
lazymatch type of HS with st_ok _ ?Ev _ _ =>
pose proof (ast_ok_add_region tfibsegs Ev _ _
(fshadow_region 88 2 0 32 [YP09.mkChunk 0 (CVal 8 (SLit 0)); YP09.mkChunk 8 (CVal 8 (SLit 0)); YP09.mkChunk 16 (CVal 8 (SLit 0)); YP09.mkChunk 24 (CVal 8 (SLit 0))]) HS eq_refl
ltac:(unfold region_ok, fshadow_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
change (fs_frame_bytes 2 / 8) with 32; rewrite E88, unsigned_lit_small by (unfold SB; lia); split; [unfold SB; lia|]; split; [unfold SB; lia|]; split;
[ intros o Ho; apply (apresent_writable tfibsegs); unfold shadow_addr in HFSpres; rewrite <- SB_SHADOW_OFF in HFSpres;
apply (proj1 (HFSpres o ltac:(change (256 / 8) with 32; lia)))
| apply Forall_cons; [apply (chunk_ok_val tfibsegs Ev _ (SB + F / 8) 0 8 _ 0); [reflexivity | zside | zside | replace (SB + F / 8 + 0) with (SB + F / 8 + 8 * 0) by lia; apply ZS; lia]|];
apply Forall_cons; [apply (chunk_ok_val tfibsegs Ev _ (SB + F / 8) 8 8 _ 0); [reflexivity | zside | zside | replace (SB + F / 8 + 8) with (SB + F / 8 + 8 * 1) by lia; apply ZS; lia]|];
apply Forall_cons; [apply (chunk_ok_val tfibsegs Ev _ (SB + F / 8) 16 8 _ 0); [reflexivity | zside | zside | replace (SB + F / 8 + 16) with (SB + F / 8 + 8 * 2) by lia; apply ZS; lia]|];
apply Forall_cons; [apply (chunk_ok_val tfibsegs Ev _ (SB + F / 8) 24 8 _ 0); [reflexivity | zside | zside | replace (SB + F / 8 + 24) with (SB + F / 8 + 8 * 3) by lia; apply ZS; lia]|];
apply Forall_nil ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint, fshadow_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
change (fs_frame_bytes 2 / 8) with 32; rewrite E88, RF; evalE AG;
unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob, SB;
clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 C3 HF4096 HFceil HFhigh HFhigh_img HF8lo HF8hi HFq HF8; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
aj_run_to_sh tfibtbl_lib_ok HS HJ2 0x80608. { awrRT AG fpos F EFA0. }
upd_aboveW HUP HFr AG. clear HF HFr HG.
rebaseE HS AG HEv. clear HEv.
lazymatch goal with |- SRr _ ?Wg (mkCfg ?msF ?mdF) _ =>
lazymatch type of HS with st_ok _ ?Ev _ _ =>
eapply SRr_mono; [eapply (RB (mkRTCX ly S W regs mem md p n fpos sp1 E T) Ev 0 0 _ _ Wg msF mdF) | cbv beta; intros W' c' _ HPOST; exists fpos, sp1, E; exact HPOST] end end.
- unfold rt_base. cbn [c_ly c_S c_W c_regs c_mem c_md c_p c_n c_fpos c_sp1 c_E0 c_T].
repeat match goal with |- _ /\ _ => split end; try assumption; try reflexivity.
- unfold rt_E, rt_F, rt_FL. cbn [c_ly c_fpos c_E0 c_sp1]. fold F FL.
split; [exact AG|]. split; [exact E70 | split; [exact RF | split; [exact E87 | exact E88]]].
- cbn [c_regs c_ly c_S c_W c_mem c_md c_fpos]. exact HJ2.
- cbn [c_S c_fpos]. rewrite Hfrs2, Hfr0. reflexivity.
-   cbn [c_S]. rewrite ES2. apply (mo_le_set_fs_r MT MTF). apply (mo_le_refl MT MTL).
- split; [clear; lia | split; [unfold ACC0; clear; lia | cbn [c_ly c_S]; exact Eab]].
- lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let rs' := eval vm_compute in (ss_mem ss_A2) in
pose proof (st_ok_submem tfibsegs Ex ssx msx rs' HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3 end.
exact HS3.
Qed.
End d.
End b.
