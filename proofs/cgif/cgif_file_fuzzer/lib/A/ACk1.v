(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI0m YI0n YI5w YI5z.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0x YC4a YC80 YC1f YC1g YC1h YC81 YC4b YC20 YC44 YC45.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC8h AC8a ACjr ACk4 ACk5.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YE00 YE01 YI00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO08 YC5d YC7z YC7x YC21 YC85 YC86 YC88.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI17 YE02 YC5n YC5l.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACk0 ACk2 ACk3 ACjo ACjs ACjv ACju ACjt ACjw ACjx.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Ltac fs_pair_tac2 :=
lazymatch goal with |- _ + ?Fv / 8 + _ <= _ \/ _ <= _ + _ / 8 + _ =>
let HFce := lazymatch goal with H : Fv + _ <= alloc_ceiling |- _ => H end in
let HC1 := lazymatch goal with H : _ <= alloc_ceiling <= _ |- _ => H end in
let HF8 := lazymatch goal with H : Fv / 8 = 4 * (Fv / 32) |- _ => H end in
let HFq := lazymatch goal with H : Fv = 32 * (Fv / 32) |- _ => H end in
let HF8lo := lazymatch goal with H : _ <= Fv / 8 |- _ => H end in
match goal with Hin : in_app _ _ |- _ =>
let H := fresh "Hia" in pose proof Hin as H; unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, RAW_SIZE, CGIF_SIZE in H;
try (change (req_size 48) with 48 in H); try (change (req_size 96) with 96 in H);
let H4 := fresh "H4" in let Hlow := fresh "Hlow" in let Hhi := fresh "Hhi" in let Hce2 := fresh "Hce2" in
destruct H as [H4 [Hlow | [Hhi Hce2]]];
[ solve [ right; try (match goal with Hflo : frame_addr _ _ _ <= ?c |- _ => match goal with Hfhi : c + _ <= frame_addr _ _ _ + _ |- _ => revert Hflo Hfhi end end);
revert Hlow HF8 HFq HF8lo; clear; intros; lia ]
| solve [ left; try (match goal with Hflo : frame_addr _ _ _ <= ?c |- _ => match goal with Hfhi : c + _ <= frame_addr _ _ _ + _ |- _ => revert Hflo Hfhi end end);
revert Hhi HFce HC1 HF8 HFq HF8lo; clear; intros; lia ] ]
end end.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Context {PI : PAImg lib_asan3_0_listing}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ lib_asan3_0_listing PI) (@pa_relro_lo _ lib_asan3_0_listing PI) (@pa_relro_hi _ lib_asan3_0_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_asan3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_asan3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_asan3_0_listing PI A_TEXT).
Context {NP : ng_params}.
#[local] Notation hw := (@ngp_hw NP).
#[local] Notation CTX := (@ngp_ctx NP).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Section e.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AMALLOC : amalloc_realizes SEGS B.
Hypothesis AFREE : afree_realizes SEGS B.
Hypothesis AMEMSET : aintrin_realizes SEGS B OSet (SIGMA AS_asan_memset).
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA AS_asan_memcpy).
Hypothesis ASM1 : astack_malloc_realizes SEGS B 1.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Variable CTXR : list (list Z).
Hypothesis HCTXR : forall l, In l CTX -> In ((BASE + 0x398) :: l) CTXR.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL. Let HBfree := pal_free B TL. Let HBmalloc := pal_malloc B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_asan3_0) (PI := PI).
Let PBASE := @pa_B_ok _ _ PI. Let PBLO := @pa_base_lo _ _ PL_asan3_0 PI.
Hypothesis TLF : PALibF B.
Hypothesis Rhw : 0 <= hw < 2 ^ 64.
Hypothesis HGOT3 : forall (H : word -> bool) mem, arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS H mem) ->
val_mem SEGS (mrestrict H mem) (VAL (A_OBJ 3)) 8 (BASE + 0).
Hypothesis HU : forall c t, In c CTX -> In t (ng_traces B c) -> In t (as_universe B).
Let RUNP := SRr_run_pi_AJ B LAWS. Let RUNTOP := SRr_run_to_pi_AJ B LAWS. Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let RUNF := aj_flag_store_pi B LAWS ML ASF FFL.
Local Notation code := (as_code B).
Variable K : asink_syms.
Hypothesis AIL : asink_img_laws SEGS B K.
Variable MT : ameter_ops.
Hypothesis MLAW : ameter_laws MT.
Hypothesis MLAWF : ameter_fs_laws MT.
Hypothesis AMALLOC4 : amalloc04_rule SEGS B MT.
Variable XN : xnums.
Hypothesis HXN : forall ngp, 0 <= ngp <= 65535 -> ng_msum MT ngp <= xn_newgif XN ngp.
Hypothesis HXM : forall ngp, 0 <= ngp <= 65535 -> ng_msum MT ngp <= xm_newgif XN ngp.
Hypothesis AFM : afile_meter SEGS B MT.
Hypothesis AFREE4 : afree04_rule SEGS B MT.
Variable ra_fo : Z.
Hypothesis AFOPENX : afopen_x SEGS B K (SIGMA AS_fopen) ra_fo pa_relro_lo pa_relro_hi.
Hypothesis HUfo : In [pc_malloc_ra0 code; ra_fo] (as_universe B).
Variable ra_fc1 ra_fc2 : Z.
Hypothesis AFCLOSE : afclose_spec SEGS B K (SIGMA AS_fclose) ra_fc1 ra_fc2 pa_relro_lo pa_relro_hi.
Hypothesis HUfc1 : In [pc_free_ra0 code; ra_fc1] (as_universe B).
Hypothesis HUfc2 : In [pc_free_ra0 code; ra_fc2] (as_universe B).
Hypothesis HMODE : VAL (A_OBJ 4) = ak_mode K.
Hypothesis Hhw0 : hw = 0.
Hypothesis RAWNEWX : trawnew_specX SEGS K B MT (SIGMA AS_cgif_raw_newgif) CTXR (BASE + 0x614) hw pa_relro_lo pa_relro_hi.
Lemma ng_mainX : NG_B_stmtX B K MT XN -> tnewgif_x SEGS K B MT XN (BASE + AF_asan3_cgif_newgif) CTX (BASE + 0x614) pa_relro_lo pa_relro_hi.
Proof.
unfold tnewgif_x.
intros NGB ly S W regs mem md ch cfgp pal0 pala attr gen Wd Hd ngp loops aM rest GPAL TA TB HAI HPRE Hal32 Hctx Hroom Htop32 HROD H10 HFO Hcfg0 HWH Hpala HPerm HGP HSNK0 HFD0 HAM0 Hev Hlive HMOK KA KB0 KB1.
assert (Hcfg : obj_at SEGS (mrestrict (w_H W) mem) cfgp LAY_Config [pal0; ak_path K; attr; gen; Wd; Hd; ngp; loops; hw; 0]) by (rewrite Hhw0; exact Hcfg0).
assert (Rpath : 0x10000 <= ak_path K < 0x5fb000).
{ apply (pa_img_range (ak_path K)). apply (proj1 (ail_env _ _ _ AIL (ak_path K) ltac:(unfold aenv_addr; right; right; right; left; lia))). }
change (if g_opens (newgif_cfg Wd Hd attr gen ngp GPAL) then openat_shape (m_fs md) TA TB else TA) with (ng_treeX md attr gen Wd Hd ngp GPAL TA TB).
eapply (srz_enterX SEGS W); [exact HAI|]. clear HAI.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof (ng_entryX B TL LAWS TLF Rhw (ak_path K) Rpath HGOT3 W ly S regs mem md ch cfgp pal0 attr gen Wd Hd ngp loops HPRE Hal32 HROD H10 HFO Hcfg) as HS.
pose proof (ajournal_init SEGS B TNEWGIFX_STK [] ly S W regs mem md ch HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5). assert (FFS : TNEWGIFX_STK = 18816) by reflexivity.
assert (HEV : EV_NEWGIF = 12) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
destruct HFO as ((cid & pos & Hfin & Hcid0 & Hfal & Hflo & Hfhi) & Hcal & HRA).
destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR Hfin) as (Hf4096 & Hfceil & Hfhigh).
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR Hfin) as Hfhigh_img.
assert (EFA0 : forall c p, frame_addr ly c p = frame_addr ly c p) by reflexivity. assert (EFL0 : forall c p, flag_addr ly c p = flag_addr ly c p) by reflexivity.
remember (Eimg (Ereg regs (ng_extraX pal0 attr gen Wd Hd ngp loops (as_uar_cell B) (ak_path K)))) as E eqn:HE.     assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E1 : ew E 1 = getr regs 1) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E8 : ew E 8 = getr regs 8) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 8 8%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 cfgp) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (EX : forall j, (j < 11)%nat -> ew E (32 + j) = nth j (ng_extraX pal0 attr gen Wd Hd ngp loops (as_uar_cell B) (ak_path K)) (Z_to_bv 64 0))
by (intros j Hj; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33. pose proof (EX 2%nat ltac:(lia)) as E34. pose proof (EX 3%nat ltac:(lia)) as E35.
pose proof (EX 4%nat ltac:(lia)) as E36. pose proof (EX 5%nat ltac:(lia)) as E37. pose proof (EX 6%nat ltac:(lia)) as E38. pose proof (EX 7%nat ltac:(lia)) as E39.
pose proof (EX 8%nat ltac:(lia)) as E40. pose proof (EX 9%nat ltac:(lia)) as E41. pose proof (EX 10%nat ltac:(lia)) as E42.
cbn [Nat.add nth ng_extraX ng_extra map app] in E32, E33, E34, E35, E36, E37, E38, E39, E40, E41, E42. clear EX.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r) by (intros n r Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn).
img_facts E. img_hull_facts.
clear HE.
unfold cfg_at. change (w64 (BASE + AF_asan3_cgif_newgif)) with (Z_to_bv 64 (BASE + AF_asan3_cgif_newgif)).
shok_auto SHOK NBx E (mrestrict (w_H W) mem).
hei_havoc HS; paj_run_tok RUN HS HJ SHOK NBspan. { awr_ok_tac. exact Usp. }
lazymatch type of HFr with frame_of ?Ef ?rs (mrestrict _ _) (mrestrict _ (ms_mem ?msX)) =>
assert (HUP : forall a, spZ regs <= a < 2 ^ 64 -> aview SEGS (w_H W) (ms_mem msX) a = aview SEGS (w_H W) mem a);
[ eapply (aview_kept_frame Ef rs _ _ _ (spZ regs) HFr); [lia|];
intros a Ha (rg & Hin & Hrg);
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In rg rs1) in Hin end; cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrg; rewrite ?Usp in Hrg; lia|]);
match goal with |- ?g => match type of Hin with ?t => idtac "HUPLEFT" t end end; destruct Hin | ] end.
clear HF HFr HG.
aconsts HROD HJ Kgot0 Kcell0 Kguar0 Kuar0 Vgr0.
prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4. prreg HS (1%bv : bv 5) R1.
pmkst HS.
rewrite (palf_sm1 B TLF).
pose proof (count_cid_le_length 1 (frames S)) as Hcnt.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_stack_malloc_at SEGS B LAWS Hsegs errno_low ML SMP 1 ASM1 ltac:(lia) W (ms_regs msX) (ms_mem msX) TNEWGIFX_STK (spZ regs) [] ly S W mem md [] ly S _ 0 (-192) _ HJ) end.
- unfold spZ. rewrite R2, E2. fold (spZ regs). rewrite unsigned_lit_small by lia. lia.
- reflexivity. - lia. - rewrite FFS, Hes; lia.
- rewrite R3, E3. exact Hgp. - rewrite R4, E4. exact Htp.
- exact R1. - apply ret_ok_codeptr_v; [lazymatch goal with |- _ <= ?k < _ => try unfold k end; lia | reflexivity].
- change (fs_frames 1) with 8192. lia. }
cbv beta. clear R2 R3 R4 R1 HJ SHOK.
intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & fpos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2 & Hbb2 & Hz & Hflag & HK).
rewrite Hes in HK. replace (spZ regs + -192 - 4096) with (spZ regs - 4288) in HK by lia. replace (spZ regs + -192) with (spZ regs - 192) in HK by lia.
assert (HUP2 : forall a, spZ regs <= a < 2 ^ 64 -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem a).
{ intros a Ha. rewrite <- (HUP a Ha). pose proof HK as (K1 & _). apply K1; lia. }
clear HUP.
aconsts HROD HJ2 Kgot2 Kcell2 Kguar2 Kuar2 Vgr2.
pose proof (proj1 HJ2) as HAR2.
assert (Hfin2 : In (1, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
assert (HfinS2 : In (cid, pos) (frames S2)) by (rewrite Hfrs2; right; exact Hfin).
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR2 Hfin2) as (HFal & [HFhi _] & HFpres & HFSpres).
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR2 Hfin2) as HFapp_img.
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 fpos HAR2 Hfin2) as (HF4096 & HFceil & HFhigh).
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR2 Hfin2) as HFhigh_img.
change (fs_frame_bytes 1) with 128 in *.
set (F := frame_addr ly 1 fpos) in *. set (FL := flag_addr ly 1 fpos) in *.
destruct (in_split _ _ Hfin) as (fl1 & fl2 & Efl).
pose proof (sep_frames_pos SEGS B LAWS ly S2 W mem2 md2 (1, fpos) (cid, pos) [] fl1 fl2 HAR2 ltac:(rewrite Hfrs2, Efl; reflexivity)) as HdFC.
unfold zdisjoint, frame_rng in HdFC. cbn [fst snd] in HdFC. change (fs_frame_bytes 1) with 128 in HdFC. fold F in HdFC.
assert (AG : forall n, (n < 33)%nat -> ew E n = ew E n) by (intros; reflexivity).
reseat HS HJ2 HP2 [0; 1; 2; 3; 4; 5; 6]%nat AG
ltac:(idtac; first [ keptR HK HJ2 AG Usp E10 E32 Hfin I Kgot0 Kgot2 Kcell0 Kcell2 Kguar0 Kguar2 Kuar0 Kuar2 Vgr0 Vgr2 EFA0 | match goal with |- ?g => idtac "KEPTFAIL" g end; fail ]).
prreg HS (10%bv : bv 5) RF. cbn [ms_regs] in RF. rewrite Ha0 in RF. symmetry in RF. unfold w64 in RF. fold F in RF.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_havoc_hi 528 Ev ssv msv [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] HS ltac:(vm_compute; reflexivity)) as HS3; hei_pose Ev 528%nat [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] | st_ok _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_havoc_hi 528 Ev ssv msv [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] HS ltac:(vm_compute; reflexivity)) as HS3; hei_pose Ev 528%nat [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)]  end.
clear HS. rename HS3 into HS. rebaseE HS AG HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (E528 : ew Ev 528 = Z_to_bv 64 FL) by (rewrite HEv; exact (ew_havoc_new _ 528 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 0 (Z_to_bv 64 0) ltac:(cbn; lia)));
assert (E529 : ew Ev 529 = Z_to_bv 64 (SB + F / 8)) by (rewrite HEv; exact (ew_havoc_new _ 528 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 1 (Z_to_bv 64 0) ltac:(cbn; lia))) | st_ok _ ?Ev _ _ =>
assert (E528 : ew Ev 528 = Z_to_bv 64 FL) by (rewrite HEv; exact (ew_havoc_new _ 528 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 0 (Z_to_bv 64 0) ltac:(cbn; lia)));
assert (E529 : ew Ev 529 = Z_to_bv 64 (SB + F / 8)) by (rewrite HEv; exact (ew_havoc_new _ 528 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 1 (Z_to_bv 64 0) ltac:(cbn; lia)))  end.
clear HEv.
assert (HFq : F = 32 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(lia)); lia).
assert (HF8 : F / 8 = 4 * (F / 32)) by (rewrite HFq at 1; replace (32 * (F / 32)) with (4 * (F / 32) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
assert (HF8lo : 512 <= F / 8) by (apply Z.div_le_lower_bound; lia)    .
assert (HF8hi : F / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia).
destruct (FFL ly S2 W mem2 md2 1 fpos HAR2 Hfin2) as (HFLpres & HFLown & HFLrng). fold FL in HFLpres, HFLown, HFLrng.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_fact Ev _ _ 516 (HPTR 5) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite RF, unsigned_lit_small by lia; change (2 ^ 5) with 32; lia)) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_pi_add_fact Ev _ _ 528 (HPTR 0) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite E528, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_pi_add_fact Ev _ _ 529 (mkAF (SB + 512) (SB + 17592186044416) 2) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E529, unsigned_lit_small by (unfold SB; lia); change (2 ^ 2) with 4; unfold SB;
split; [lia|]; split; [rewrite HF8; replace (2147450880 + 4 * (F / 32)) with ((536862720 + F / 32) * 4) by lia; apply Z_mod_mult | lia])) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_pi_add_alias Ev _ _ _ _ HS (shadow_decl_ok Ev 516 35 529 F SB RF ltac:(lia) E35 E529)) as HS3;
clear HS; rename HS3 into HS; norm_ss HS;
pose proof (st_ok_pi_add_region Ev _ _ (fframe_region 516 528 1 []) HS eq_refl
ltac:(unfold region_ok, fframe_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
change (fs_frame_bytes 1) with 128; rewrite RF, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split;
[ intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFpres (F + o) ltac:(lia)))
| apply Forall_cons; [|apply Forall_nil]; apply (chunk_ok_val SEGS Ev _ F (128 - 8) 8 _ FL);
[cbn [sv_denot]; rewrite E528, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | replace (F + (128 - 8)) with (F + 128 - 8) by lia; exact (val_mem_of_rdword SEGS _ _ _ _ Hflag)] ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint, fframe_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
change (fs_frame_bytes 1) with 128;
rewrite RF; evalE AG;
repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS | st_ok _ ?Ev _ _ =>
pose proof (st_ok_add_fact SEGS Ev _ _ 516 (HPTR 5) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite RF, unsigned_lit_small by lia; change (2 ^ 5) with 32; lia)) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_add_fact SEGS Ev _ _ 528 (HPTR 0) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite E528, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_add_fact SEGS Ev _ _ 529 (mkAF (SB + 512) (SB + 17592186044416) 2) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E529, unsigned_lit_small by (unfold SB; lia); change (2 ^ 2) with 4; unfold SB;
split; [lia|]; split; [rewrite HF8; replace (2147450880 + 4 * (F / 32)) with ((536862720 + F / 32) * 4) by lia; apply Z_mod_mult | lia])) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_add_alias SEGS Ev _ _ _ _ HS (shadow_decl_ok Ev 516 35 529 F SB RF ltac:(lia) E35 E529)) as HS3;
clear HS; rename HS3 into HS;
pose proof (ast_ok_add_region SEGS Ev _ _ (fframe_region 516 528 1 []) HS eq_refl
ltac:(unfold region_ok, fframe_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
change (fs_frame_bytes 1) with 128; rewrite RF, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split;
[ intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFpres (F + o) ltac:(lia)))
| apply Forall_cons; [|apply Forall_nil]; apply (chunk_ok_val SEGS Ev _ F (128 - 8) 8 _ FL);
[cbn [sv_denot]; rewrite E528, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | replace (F + (128 - 8)) with (F + 128 - 8) by lia; exact (val_mem_of_rdword SEGS _ _ _ _ Hflag)] ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint, fframe_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
change (fs_frame_bytes 1) with 128;
rewrite RF; evalE AG;
repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS; norm_ss HS  end.
assert (ZS : forall j, 0 <= j < 2 -> val_mem SEGS (mrestrict (w_H W) mem2) (SB + F / 8 + 8 * j) 8 0).
{ intros j Hj. apply val_mem_zero8. intros i Hi. unfold zero_shadow, shadow_of_addr in Hz. rewrite <- SB_SHADOW_OFF in Hz.
replace (SB + F / 8 + 8 * j + i) with (SB + F / 8 + (8 * j + i)) by lia. apply Hz. change (128 / 8) with 16. lia. }
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv _ =>
let rs2 := eval vm_compute in (ss_mem ssv) in
assert (DJ : all_disjoint Ev (fshadow_region 529 1 0 16 [YP09.mkChunk 0 (CVal 8 (SLit 0)); YP09.mkChunk 8 (CVal 8 (SLit 0))]) rs2) by
( cbn [all_disjoint]; unfold extent_disjoint, fshadow_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
change (fs_frame_bytes 1 / 8) with 16; rewrite E529, RF; evalE AG; unfold CGIF_SIZE, SB; repeat split; first [fs_pair_tac2 | zone_lia]);
pose proof (st_ok_pi_add_region Ev _ _
(fshadow_region 529 1 0 16 [YP09.mkChunk 0 (CVal 8 (SLit 0)); YP09.mkChunk 8 (CVal 8 (SLit 0))]) HS eq_refl
ltac:(unfold region_ok, fshadow_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
change (fs_frame_bytes 1 / 8) with 16; rewrite E529, unsigned_lit_small by (unfold SB; lia); split; [unfold SB; lia|]; split; [unfold SB; lia|]; split;
[ intros o Ho; apply (apresent_writable SEGS); unfold shadow_addr in HFSpres; rewrite <- SB_SHADOW_OFF in HFSpres;
replace (SB + F / 8 + o) with (SB + F / 8 + o) by lia; apply (proj1 (HFSpres o ltac:(change (128 / 8) with 16; lia)))
| apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ (SB + F / 8) 0 8 _ 0); [reflexivity | zside | zside | rewrite Z.add_0_r; replace (SB + F / 8) with (SB + F / 8 + 8 * 0) by lia; apply ZS; lia]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ (SB + F / 8) 8 8 _ 0); [reflexivity | zside | zside | replace (SB + F / 8 + 8) with (SB + F / 8 + 8 * 1) by lia; apply ZS; lia]|];
apply Forall_nil ])
DJ) as HS3;
clear HS DJ; rename HS3 into HS end.
norm_ss HS.
paj_run_to_shc RUNTOP HS HJ2 0x11c. { awrR AG fpos F EFA0. }
upd_above HUP2 HFr AG. rename HUP2 into HUP.
clear HF HFr HG.
fs_ro HS. reshok_bx HS 35%nat.
hei_havoc HS; paj_run_tok RUN HS HJ2 SHOK NBspan; [awrR AG fpos F EFA0 |].
upd_above HUP HFr AG. clear HF HFr HG.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msX) =>
pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H W) msX) 0 _ HS eq_refl) as HRfs; cbn [ms_mem restrict] in HRfs;
lazymatch type of HRfs with region_ok _ _ _ (YP09.mkRegion (Some 529%nat) ?lo ?hi ?wlo ?whi ?cs) =>
assert (ZS5 : forall j, 4 <= j <= 8 -> val_mem SEGS (mrestrict (w_H W) (ms_mem msX)) (SB + F / 8 + j) 1 0);
[ intros j Hj;
assert (Hj5 : j = 4 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 8) by lia;
destruct Hj5 as [-> | [-> | [-> | [-> | ->]]]];
(eapply (field_of_region Ex _ 529 (SB + F / 8) cs lo hi wlo whi _ 1%N (SLit 0) 0 HRfs);
[evalE AG | cbn; tauto | reflexivity | cbn; lia | cbn; lia])
| ] end;
clear HRfs;
assert (HRA40 : range_addressable (aview SEGS (w_H W) (ms_mem msX)) SHADOW_OFF (F + 32) 40);
[ apply zero_shadow_range; [rewrite HFq; replace (32 * (F / 32) + 32) with ((4 * (F / 32) + 4) * 8) by lia; apply Z_mod_mult | reflexivity |];
intros i Hi; change (40 / 8) with 5 in Hi; unfold shadow_of_addr; rewrite <- SB_SHADOW_OFF;
replace (SB + (F + 32) / 8 + i) with (SB + F / 8 + (4 + i)) by (rewrite HFq at 2; rewrite HF8; replace (32 * (F / 32) + 32) with ((4 * (F / 32) + 4) * 8) by lia; rewrite Z.div_mul by lia; lia);
apply (aview_of_val_mem1 SEGS); [apply ZS5; lia | lia]
| ] | st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W) msX) 0 _ HS eq_refl) as HRfs; cbn [ms_mem restrict] in HRfs;
lazymatch type of HRfs with region_ok _ _ _ (YP09.mkRegion (Some 529%nat) ?lo ?hi ?wlo ?whi ?cs) =>
assert (ZS5 : forall j, 4 <= j <= 8 -> val_mem SEGS (mrestrict (w_H W) (ms_mem msX)) (SB + F / 8 + j) 1 0);
[ intros j Hj;
assert (Hj5 : j = 4 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 8) by lia;
destruct Hj5 as [-> | [-> | [-> | [-> | ->]]]];
(eapply (field_of_region Ex _ 529 (SB + F / 8) cs lo hi wlo whi _ 1%N (SLit 0) 0 HRfs);
[evalE AG | cbn; tauto | reflexivity | cbn; lia | cbn; lia])
| ] end;
clear HRfs;
assert (HRA40 : range_addressable (aview SEGS (w_H W) (ms_mem msX)) SHADOW_OFF (F + 32) 40);
[ apply zero_shadow_range; [rewrite HFq; replace (32 * (F / 32) + 32) with ((4 * (F / 32) + 4) * 8) by lia; apply Z_mod_mult | reflexivity |];
intros i Hi; change (40 / 8) with 5 in Hi; unfold shadow_of_addr; rewrite <- SB_SHADOW_OFF;
replace (SB + (F + 32) / 8 + i) with (SB + F / 8 + (4 + i)) by (rewrite HFq at 2; rewrite HF8; replace (32 * (F / 32) + 32) with ((4 * (F / 32) + 4) * 8) by lia; rewrite Z.div_mul by lia; lia);
apply (aview_of_val_mem1 SEGS); [apply ZS5; lia | lia]
| ]  end.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msX) =>
assert (Hpres2F : forall a, F <= a < F + 128 -> apresent (w_H W) (ms_mem msX) a) | st_ok _ _ _ (restrict _ ?msX) =>
assert (Hpres2F : forall a, F <= a < F + 128 -> apresent (w_H W) (ms_mem msX) a)  end.
{ destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos (proj1 HJ2) Hfin2) as (_ & _ & HFpresX & _). change (fs_frame_bytes 1) with 128 in HFpresX. fold F in HFpresX.
intros a Ha. exact (proj1 (HFpresX a Ha)). }
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 516%nat in let i := eval vm_compute in i in
pose proof (st_ok_pi_submem Ex ssx msx (firstn i (ss_mem ssx) ++ trim_lo (nth i (ss_mem ssx) got_regionP) 72 :: skipn (Datatypes.S i) (ss_mem ssx)) HS
ltac:(cbn [ss_mem nth skipn firstn app]; repeat (apply submem_keep; [first [apply subregion_trim_lo | apply subregion_refl]|]); apply submem_refl)
ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS | st_ok _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 516%nat in let i := eval vm_compute in i in
pose proof (st_ok_submem SEGS Ex ssx msx (firstn i (ss_mem ssx) ++ trim_lo (nth i (ss_mem ssx) got_regionP) 72 :: skipn (Datatypes.S i) (ss_mem ssx)) HS
ltac:(cbn [ss_mem nth skipn firstn app]; repeat (apply submem_keep; [first [apply subregion_trim_lo | apply subregion_refl]|]); apply submem_refl)
ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS  end.
norm_ss HS.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
pose proof (st_ok_pi_add_region Ex _ _ (YP09.mkRegion (Some 516%nat) 0 32 0 32 []) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
rewrite RF, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable SEGS); apply Hpres2F; lia)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite RF; evalE AG; repeat split; first [zone_lia | match goal with |- ?g => idtac "DISJ" g; fail end])) as HS3;
clear HS; rename HS3 into HS | st_ok _ ?Ex _ _ =>
pose proof (ast_ok_add_region SEGS Ex _ _ (YP09.mkRegion (Some 516%nat) 0 32 0 32 []) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
rewrite RF, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable SEGS); apply Hpres2F; lia)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite RF; evalE AG; repeat split; first [zone_lia | match goal with |- ?g => idtac "DISJ" g; fail end])) as HS3;
clear HS; rename HS3 into HS  end.
norm_ss HS. reshok_bx HS 35%nat.
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2. prreg HS (1%bv : bv 5) Rra.
prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
pmkst HS.
idtac.
clear Kgot2 Kcell2 Kguar2 Kuar2 Vgr2. aconsts HROD HJ2 Kgot2 Kcell2 Kguar2 Kuar2 Vgr2.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_intrin_at SEGS B LAWS Hsegs OSet (SIGMA AS_asan_memset) AMEMSET _ (ms_regs msX) (ms_mem msX) TNEWGIFX_STK (spZ regs) [] ly S W mem md [(1, fpos)]
ly S2 _ _ (F + 32) 0 40 (-192) (Z_to_bv 64 (BASE + 0x12c)) HJ2) end.
- rewrite Ra0. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite RF. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
- exact Ra1.
- exact Ra2.
- lia. - lia. - lia.
- unfold spZ at 1. rewrite Rsp. evalE AG.
- reflexivity. - lia. - rewrite FFS. unfold ESTACK. lia.
- rewrite Rgp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 3%nat) by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
- rewrite Rtp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 4%nat) by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
- exact Rra.
- apply ret_ok_codeptr_v; [lazymatch goal with |- _ <= ?k < _ => try unfold k end; lia | reflexivity].
- intros a Ha. split; [| unfold ESTACK; lia]. right. right. right. exists 1, fpos. split; [left; reflexivity|]. left.
unfold in_zr, frame_rng. cbn [fst snd]. change (fs_frame_bytes 1) with 128. fold F. lia.
- apply amem_range_high; zone_lia.
- exact HRA40.
- intros _. eapply (shadow_hull_vis_of_frame SEGS B LAWS ly S2 _ _ _ 1 fpos (F + 32) 40 (proj1 HJ2) Hfin2);
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
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 516%nat) 32 72 32 72 []) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
rewrite RF, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFpres4' (F + o) ltac:(lia))))
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite RF; evalE AG; repeat split; first [zone_lia | match goal with |- ?g => idtac "DISJ" g; fail end])) as HS3;
clear HS; rename HS3 into HS | st_ok _ ?Ev _ _ =>
pose proof (ast_ok_add_region SEGS Ev _ _ (YP09.mkRegion (Some 516%nat) 32 72 32 72 []) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
rewrite RF, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFpres4' (F + o) ltac:(lia))))
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite RF; evalE AG; repeat split; first [zone_lia | match goal with |- ?g => idtac "DISJ" g; fail end])) as HS3;
clear HS; rename HS3 into HS  end.
norm_ss HS. reshok_bx HS 35%nat. clear_frames.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx (restrict _ ?msv) =>
eapply (NGB ly S W regs mem md ch cfgp pal0 pala attr gen Wd Hd ngp loops aM rest GPAL cid pos E Ev W ly S2 msv _ 0 fpos TA TB);
[ split; [exact HPRE | split; [exact Hal32 | split; [| split; [exact Hroom | split; [exact Htop32 | split; [exact HROD | split; [exact Hcfg | split; [exact HWH | split; [exact Hpala | split; [exact HPerm | split; [exact Hev | exact Hlive]]]]]]]]]]]
| split; [exact HGP | split; [exact HSNK0 | split; [exact HFD0 | split; [exact HAM0 | exact HMOK]]]]
| split; [exact KA | split; [exact KB0 | exact KB1]]
| split; [exact Hfin | split; [exact Hcid0 | split; [exact Hfal | split; [exact Hflo | split; [exact Hfhi | split; [exact Hcal | exact HRA]]]]]]
| split; [exact EE | split; [exact E10 | split; [exact E32 | exact Usp]]]
| split; [split; [exact AG | repeat (split; [eassumption|]); eassumption] | exact E42]
| split; [exact HJ4 | split; [clear; lia | split; [exact Hfrs2 | exact Eab]]]
| lazymatch goal with |- st_ok_pi _ _ ?Eg ?ssT _ =>
let fa := eval vm_compute in (f_atoms (ss_facts ssT)) in let al := eval vm_compute in (f_alias (ss_facts ssT)) in
exact (st_ok_pi_facts_incl Eg ssx _ fa al HS ltac:(incl_lit_tac) ltac:(incl_lit_tac)) end ] | st_ok _ ?Ev ?ssx (restrict _ ?msv) =>
eapply (NGB ly S W regs mem md ch cfgp pal0 pala attr gen Wd Hd ngp loops aM rest GPAL cid pos E Ev W ly S2 msv _ 0 fpos TA TB);
[ split; [exact HPRE | split; [exact Hal32 | split; [| split; [exact Hroom | split; [exact Htop32 | split; [exact HROD | split; [exact Hcfg | split; [exact HWH | split; [exact Hpala | split; [exact HPerm | split; [exact Hev | exact Hlive]]]]]]]]]]]
| split; [exact HGP | split; [exact HSNK0 | split; [exact HFD0 | split; [exact HAM0 | exact HMOK]]]]
| split; [exact KA | split; [exact KB0 | exact KB1]]
| split; [exact Hfin | split; [exact Hcid0 | split; [exact Hfal | split; [exact Hflo | split; [exact Hfhi | split; [exact Hcal | exact HRA]]]]]]
| split; [exact EE | split; [exact E10 | split; [exact E32 | exact Usp]]]
| split; [split; [exact AG | repeat (split; [eassumption|]); eassumption] | exact E42]
| split; [exact HJ4 | split; [clear; lia | split; [exact Hfrs2 | exact Eab]]]
| lazymatch goal with |- st_ok_pi _ _ ?Eg ?ssT _ =>
let fa := eval vm_compute in (f_atoms (ss_facts ssT)) in let al := eval vm_compute in (f_alias (ss_facts ssT)) in
exact (st_ok_pi_facts_incl Eg ssx _ fa al HS ltac:(incl_lit_tac) ltac:(incl_lit_tac)) end ]  end.
exact Hctx.
Qed.
Theorem pb_cgif_newgifX : tnewgif_x SEGS K B MT XN (BASE + AF_asan3_cgif_newgif) CTX (BASE + 0x614) pa_relro_lo pa_relro_hi.
Proof.
apply ng_mainX.
eapply ng_BX; try eassumption.
eapply ng_MX; try eassumption.
eapply ng_KX; try eassumption.
- eapply ng_P0X; eassumption.
- eapply ng_GX; try eassumption. eapply ng_P1X; eassumption.
Qed.
End e. End d.
End b.
