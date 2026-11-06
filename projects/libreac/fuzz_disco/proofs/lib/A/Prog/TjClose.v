(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/AChf.v, with its module paths, module names and numbers changed; 185 of its 334 lines of code are new or changed and 217 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/TjEntry.v, with its addresses changed; 257 of its 322 lines of code are new or changed and 269 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import YCkd.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import PaRun PaShadow PaStep DiscoSyms DiscoList DiscoAddr DiscoPa.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import PaJournal DiscoPaLib YC1g YC1h YC81 YC4b DiscoFrame YC45 YC85 YC88.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import DiscoBase YC1i.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import DiscoACjr ACj1 DiscoACja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import TjSpec TjBase DiscoRo TjCuts TjEntry TjSnSh.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import SnShared PfFacts SnprintfDef SnprintfDefR.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_json_text.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require tj_lemmas.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require disco_table_c reac_disco_table_json_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Rt Require Import SnprintfConsts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import AmemBlock8.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma tjc_sub : forall c l z, zcanon z = 2 ^ 64 - 1 -> 0 < l <= c -> c < 2 ^ 63 -> zcanon (c + zcanon (l * zcanon z)) = c - l.
Proof.
intros c l z Hz Hl Hc. rewrite Hz. unfold zcanon, M64.
replace (l * (2 ^ 64 - 1)) with ((2 ^ 64 - l) + (l - 1) * 2 ^ 64) by ring.
rewrite Z_mod_plus_full, (Z.mod_small (2 ^ 64 - l)) by lia.
replace (c + (2 ^ 64 - l)) with ((c - l) + 1 * 2 ^ 64) by ring.
rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.
Ltac notw AG :=
let rg := fresh "rg" in let Hin := fresh "Hin" in let Hrg := fresh "Hrg" in
intros (rg & Hin & Hrg);
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In rg rs1) in Hin end; cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrg; revert Hrg; evalE AG; intros Hrg; lia|]);
destruct Hin.
Ltac fa2 tac := apply Forall_cons; [tac | apply Forall_cons; [tac | apply Forall_nil]].
Ltac tjc_kept AG Hfr Hpres2 :=
eapply region_kept_aview; [evalE AG | let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; apply Hfr; lia | exact Hpres2].
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
Context {RO : ro_below_ofl (@pa_segs _ disco_listing PI) (@pa_relro_lo _ disco_listing PI) (@pa_relro_hi _ disco_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
Section h.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TLF : PALibF B.
Variables SNPC GC GV IMGLO IMGHI : Z.
Variable CR : list (Z * Z).
Hypothesis HSNPC : pa_sigma DS___interceptor_trampoline_snprintf = SNPC.
Hypothesis ASNP : forall fq : YK11.FPState,
SnprintfDefR.asnprintf_realizesR (fx := fq) SEGS B pa_relro_lo pa_relro_hi GC GV IMGLO IMGHI disco_fmt_lo disco_fmt_hi CR SNPC.
Hypothesis tj_snp_consts : forall (W : world SEGS) mem, arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) -> consts_view SEGS W mem CR.
Hypothesis tj_snp_cr : Forall (fun r => IMG_LO <= fst r /\ 0 <= snd r /\ fst r + snd r <= IMG_TOP) CR.
Hypothesis tj_snp_canary : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
exists cval, rdword (aview SEGS (w_H W) mem) GC = Some GV /\ rdword (aview SEGS (w_H W) mem) GV = Some cval.
Hypothesis tj_snp_gcgv : IMG_LO <= GC /\ GC + 8 <= IMG_TOP /\ IMG_LO <= GV /\ GV + 8 <= IMG_TOP.
Hypothesis tj_snp_img : IMG_LO <= IMGLO /\ IMGHI <= IMG_TOP.
Hypothesis GM : globs_marked SEGS B disco_globs.
Hypothesis HV : img_shadow_vis SEGS B.
Hypothesis DRO : disco_ro_unowned B.
Hypothesis TJS : tj_strs.
Variables STK EV EVB : Z.
Variable IMG : world SEGS -> (word -> option byte) -> Prop.
Hypothesis HSTK : TJ_FRAME + SNPRINTF_STK <= STK.
Hypothesis HEV : 8 * EVB <= EV.
Hypothesis FX : tj_fromX B STK EV IMG.
Theorem pb_tj_close : tj_fromC B STK EV EVB IMG.
Proof.
unfold tj_fromC, tj_from0.
intros cx E k ly3 S3 W3 ms3 md3 HBASE HEX HJ HFR HINV HS.
destruct cx as [fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0].
pose proof HBASE as HB0. pose proof HEX as HX0. unfold tj_baseX in HB0. unfold tj_EX, tj_F, tj_FL in HX0.
cbn [c_fq c_ly c_S c_W c_regs c_mem c_md c_ch c_t c_now c_buf c_cap c_Nb c_T c_fpos c_sp1 c_E0 tj_F tj_FL]
in HB0, HX0, HINV, HJ, HFR, HS.
pose proof HB0 as (HPRE & Hfrm0 & Hroom & HROD & HIM & H10 & H11 & H12 & H13 & Hnow & Hcap & Hobj & Harr & HlenT & Hok
& Hbuf & Hev & Hsp1b & HE0 & HE032 & HE02).
pose proof HX0 as (AG & E60 & E516 & E528 & E529 & HEI).
unfold INV_tjC in HINV. cbn [c_cap c_T c_now c_buf] in HINV.
destruct HINV as (Hk0 & Hperm & HKEEP & Hcap3 & acc & E695 & Hacc & Htxt & Hgarr).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity. assert (HSNP : SNPRINTF_STK = 11776) by reflexivity.
assert (HSK : 11776 + 640 <= STK) by (unfold TJ_FRAME in HSTK; lia).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBOK. pose proof pa_base_lo as HBLO.
destruct (sp1_facts (spZ regs + -288) ltac:(clear - Hceil Hslo Hstk0 HSK C1; lia)
ltac:(rewrite <- Zplus_mod_idemp_l, Hal16; reflexivity)) as (Hsp1r & Hsp1al & Hsp1al16).
rewrite <- Hsp1b in Hsp1r, Hsp1al, Hsp1al16.
assert (Hsp1 : spZ regs - 304 <= sp1 <= spZ regs - 288) by (clear - Hsp1r; lia). clear Hsp1r.
pose (BR := paj_branch (fx := fq) (PI := PI)).
pose proof HJ as (HAR3 & Hly3 & _ & _ & _ & Hfrs3 & Hnev3 & Hk3 & _ & _ & _ & _ & _ & Hpres3 & _ & _ & HQT3).
destruct (al_layout _ _ LAWS ly S W mem md ly3 HAR Hly3) as (Eab3 & EFA & Eown3).
assert (EFA0 : forall c p, frame_addr ly3 c p = frame_addr ly c p) by exact EFA.
set (F := frame_addr ly 2 fpos) in *. set (FLg := flag_addr ly 2 fpos) in *.
assert (Hfin : In (2, fpos) (frames S3)) by (rewrite HFR; left; reflexivity).
assert (E1 : ew E 1 = getr regs 1) by (rewrite (AG 1%nat ltac:(lia)); exact (HE0 1%nat 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite (AG 2%nat ltac:(lia)); exact (HE0 2%nat 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (rewrite (AG 3%nat ltac:(lia)); exact (HE0 3%nat 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (rewrite (AG 4%nat ltac:(lia)); exact (HE0 4%nat 4%bv eq_refl)).
assert (E12 : ew E 12 = Z_to_bv 64 buf) by (rewrite (AG 12%nat ltac:(lia)); rewrite (HE0 12%nat 12%bv eq_refl); exact H12).
assert (E13 : ew E 13 = Z_to_bv 64 cap) by (rewrite (AG 13%nat ltac:(lia)); rewrite (HE0 13%nat 13%bv eq_refl); exact H13).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite (AG 32%nat ltac:(lia)); exact HE032).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (AG 2%nat ltac:(lia)); exact HE02).
img_factsF E.
pose proof (pa_obj_img 1 ltac:(unfold disco_nobj; lia)) as Hob242. pose proof (pa_obj_img 0 ltac:(unfold disco_nobj; lia)) as Hob241.
pose proof (pa_obj_img 66 ltac:(unfold disco_nobj; lia)) as Hob307. pose proof (pa_obj_img 67 ltac:(unfold disco_nobj; lia)) as Hob308.
cbv [A_OBJ Nat.add] in Hob241, Hob242, Hob307, Hob308.
pose proof (palf_uar_img B TL) as Huar. pose proof (palf_uar_al B TLF) as Huar4.
unfold IMG_LO, IMG_TOP in Hob241, Hob242, Hob307, Hob308, Huar.
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos HAR3 Hfin) as (HFal & [HFhi _] & HFpres & HFSpres).
rewrite EFA in HFal, HFhi, HFpres, HFSpres. fold F in HFal, HFhi, HFpres, HFSpres.
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 2 fpos HAR3 Hfin) as (HF4096 & HFceil & HFhigh).
rewrite EFA in HF4096, HFceil, HFhigh. fold F in HF4096, HFceil, HFhigh.
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR3 Hfin) as HFhigh_img. rewrite EFA in HFhigh_img. fold F in HFhigh_img.
change (fs_frame_bytes 2) with 256 in *.
assert (HFq : F = 32 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(lia)); lia).
assert (HF8 : F / 8 = 4 * (F / 32)) by (rewrite HFq at 1; replace (32 * (F / 32)) with (4 * (F / 32) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
assert (HF8lo : 512 <= F / 8) by (apply Z.div_le_lower_bound; lia).
assert (HF8hi : F / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia).
pose (RUNP := SRr_run_pi_AJ (fx := fq) B LAWS). pose (RUNTOP := SRr_run_to_pi_AJ (fx := fq) B LAWS).
pose (RUNC := SRr_run_pi_AJ_call (fx := fq) B LAWS).

paj_run_shc RUNP RUNC HS HJ. { awrFL_with ltac:(idtac; tj_hd AG HSK) AG fpos F EFA0. }

assert (HK1 : forall a, buf <= a < buf + cap -> aview SEGS (w_H W3) (ms_mem ms) a = aview SEGS (w_H W3) (ms_mem ms3) a).
{ intros a Ha. pose proof (proj1 HJ) as HARq.
assert (Hinq : In (buf, Nb) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact (proj1 (Hbuf Hcap3))]).
pose proof (proj2 (Hbuf Hcap3)) as Hcq.
destruct (al_blocks _ _ LAWS _ _ _ _ _ buf Nb HARq Hinq) as (_ & Hq4096 & Hqceil & Hqapp & _).
pose proof (blk_off_imgP _ _ _ _ _ _ buf Nb HARq Hinq) as Hqimg.
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ buf Nb 2 fpos HARq Hinq Hfin) as Hqsep.
rewrite EFA0 in Hqsep. fold F in Hqsep. change (fs_frame_bytes 2) with 256 in Hqsep. unfold zdisjoint in Hqsep. cbn [fst snd] in Hqsep.
unfold in_app, kLowShadowBeg, kHighMemBeg in Hqapp. unfold off_img, IMG_LO, IMG_TOP in Hqimg.
eapply aview_kept_out; [exact HFr | lia | notw AG]. }
clear HF HFr HG.
pose proof (proj1 HJ) as HARc.
assert (Hinb0 : In (buf, Nb) (ablocks B ly S)) by exact (proj1 (Hbuf Hcap3)).
assert (Hcapb : cap <= req_size Nb) by exact (proj2 (Hbuf Hcap3)).
assert (Hinb : In (buf, Nb) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hinb0]).
destruct (al_blocks _ _ LAWS _ _ _ _ _ buf Nb HARc Hinb) as (Hb16 & Hb4096 & Hbceil & Hbapp & _ & _ & HNb).
pose proof (blk_off_imgP _ _ _ _ _ _ buf Nb HARc Hinb) as Hbimg.
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ buf Nb 2 fpos HARc Hinb Hfin) as Hbsep.
rewrite EFA0 in Hbsep. fold F in Hbsep. change (fs_frame_bytes 2) with 256 in Hbsep. unfold zdisjoint in Hbsep. cbn [fst snd] in Hbsep.
unfold in_app, kLowShadowBeg, kHighMemBeg in Hbapp. unfold off_img, IMG_LO, IMG_TOP in Hbimg.
set (L := Z.of_nat (length acc)) in *.
pose proof (img_env_atomP E 296 HEI ltac:(unfold A_TEXT, A_LIM; lia)) as E296.
pose proof TJS as (_ & Hcl & _).
unfold tj_ro_at, tj_s_close in Hcl. change (A_OBJ 55) with 296%nat in Hcl. cbn [length Z.of_nat] in Hcl.
destruct Hcl as (Hg55 & Hro55 & Hlo55 & Hhi55 & _ & Hb55). unfold IMG_LO, IMG_TOP in Hlo55, Hhi55.
pose proof (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HROD) as HRODc.
destruct (tj_snp_canary _ _ _ _ _ HARc) as (cval & HG1 & HG2).
pose proof tj_snp_gcgv as (Hgc1 & Hgc2 & Hgv1 & Hgv2). unfold IMG_LO, IMG_TOP in Hgc1, Hgc2, Hgv1, Hgv2.
unfold w64 in E695.
rregU HS (10%bv : bv 5) (buf + L) ltac:(rewrite U_SAlu; cbn [zalu_raw]; rewrite (U_atom E 12 buf E12), (U_atom E 695 L E695) by lia; apply zcanon_id; unfold M64; lia) Ra0.
rregU HS (11%bv : bv 5) (cap - L) ltac:(rewrite U_SAlu; cbn [zalu_raw]; rewrite U_SMd; cbn [zmd_raw]; rewrite (U_atom E 13 cap E13), (U_atom E 695 L E695) by lia; rewrite U_SLit; apply tjc_sub; [reflexivity | lia | lia]) Ra1.
prreg HS (2%bv : bv 5) Qsp. prreg HS (3%bv : bv 5) Qgp. prreg HS (4%bv : bv 5) Qtp. prreg HS (1%bv : bv 5) Qra. prreg HS (12%bv : bv 5) Qa2.
destruct (ro_read_ok_glob SEGS B disco_globs _ _ _ _ _ (VAL 296) _ (VAL 296) 2 GM Hg55 HV HARc ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold IMG_LO; lia) ltac:(unfold IMG_TOP; lia)) as [Hfra Hfrh].

pmkst HS. rewrite HSNPC.
eapply (aj_sh_snprintf_at B LAWS pa_segs_low STK fq GC GV IMGLO IMGHI CR SNPC (ASNP fq) W3 (ms_regs ms) (ms_mem ms) (spZ regs) (tj_fp buf cap) ly S W mem md [(2, fpos)] ly3 S3 _ k (buf + L) (cap - L) (VAL 296) [93] [PLit 93] [] (map (argZ (ms_regs ms)) [3; 4; 5; 6; 7] ++ []) [] [93] cval (sp1 - spZ regs) (Z_to_bv 64 (BASE + 25032)) _ HJ HRODc).
{ unfold spZ at 1. rewrite Qsp, E60, unsigned_lit_small by lia. lia. }
{ rewrite <- Zminus_mod_idemp_l, Hsp1al16, <- Zminus_mod_idemp_r, Hal16. reflexivity. }
{ lia. }
{ lia. }
{ rewrite Qgp, E3. exact Hgp. }
{ rewrite Qtp, E4. exact Htp. }
{ exact Qra. }
{ apply ret_ok_codeptr_v; [lia | reflexivity]. }
{ exact Ra0. }
{ exact Ra1. }
{ rewrite Qa2, E296. reflexivity. }
{ exact (tj_snp_consts _ _ HRODc). }
{ eapply Forall_impl; [|exact tj_snp_cr]. intros r Hr. cbv beta in *. unfold IMG_LO, IMG_TOP in Hr. lia. }
{ eapply Forall_impl; [|exact tj_snp_cr]. intros r Hr. cbv beta in *. unfold IMG_LO, IMG_TOP in Hr. unfold snp_out. fa2 ltac:(unfold zdisjoint; cbn [fst snd]; lia). }
{ exact HG1. }
{ exact HG2. }
{ lia. }
{ lia. }
{ lia. }
{ lia. }
{ unfold snp_out. fa2 ltac:(unfold zdisjoint; cbn [fst snd]; lia). }
{ unfold snp_out. fa2 ltac:(unfold zdisjoint; cbn [fst snd]; lia). }
{ unfold fmt_at. cbn [length Z.of_nat app nth].
split; [lia|]. split.
+ intros i Hi. rewrite (ro_bytes SEGS pa_relro_lo pa_relro_hi B _ (VAL 296) 2 (VAL 296 + i) HRODc (Hro55 (VAL 296 + i) ltac:(lia))
(disco_ro_unowned_at B _ _ DRO ltac:(unfold disco_ro_ranges; apply in_or_app; left; exact Hg55)) ltac:(lia)).
assert (Hi' : i = 0 \/ i = 1) by lia. destruct Hi' as [-> | ->].
* pose proof (Hb55 0%nat ltac:(cbn; lia)) as Hq. cbn [Z.of_nat nth app] in Hq. exact Hq.
* pose proof (Hb55 1%nat ltac:(cbn; lia)) as Hq. cbn [Z.of_nat nth app] in Hq. exact Hq.
+ split; [unfold snp_out; fa2 ltac:(unfold zdisjoint; cbn [fst snd]; lia)|].
split; [unfold amem_range; left; lia|]. split; assumption. }
{ exact (tj_ro_fmt_rng 55 tj_s_close (proj1 (proj2 TJS)) ltac:(cbn; lia)). }
{ discriminate. }
{ reflexivity. }
{ constructor; [exact I | constructor]. }
{ split; [reflexivity | intros i Hi; cbn in Hi; lia]. }
{ cbn [length Z.of_nat]. lia. }
{ unfold snp_out. fa2 ltac:(unfold zdisjoint; cbn [fst snd]; lia). }
{ exact I. }
{ exact I. }
{ reflexivity. }
{ lia. }
{ cbn. lia. }
{ lia. }
{ lia. }
{ unfold snp_out. cbn [pairwise]. split; [apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; lia | apply Forall_nil] | split; [apply Forall_nil | exact I]]. }
{ intros a Ha. split; [|lia]. right. left. split.
+ exists (buf, buf + cap). split; [unfold tj_fp; rewrite (proj2 (Z.ltb_ge cap 3) Hcap3); left; reflexivity | cbn [fst snd]; lia].
+ exists buf, Nb. split; [exact Hinb | lia]. }
{ apply (amem_range_of_block8 SEGS B LAWS _ _ _ _ _ buf Nb _ _ HARc Hinb); lia. }
{ apply (range_addressable_of_block SEGS B LAWS _ _ _ _ _ buf Nb _ _ HARc Hinb); lia. }
{ apply (shadow_hull_vis_of_block SEGS B LAWS _ _ _ _ _ buf Nb _ _ HARc Hinb); lia. }
{ eapply tj_dest_off_globals; [exact (proj1 tj_snp_img) | exact (proj2 tj_snp_img) | exact HARc | exact Hinb | lia | lia]. }
{ exact Hfrm0. }

intros fx' regs2 mem2 md2 Hf1 Hf2 HJ2 HP2 Ha0' Hwr Hnul Hfr Hpres2 Hsame.
cbn [length Z.of_nat] in Ha0', Hwr, Hnul, Hfr.
replace (spZ regs + (sp1 - spZ regs)) with sp1 in Hfr by lia. rewrite HSNP in Hfr.

reseat HS HJ2 HP2 [0; 1; 2; 3; 4; 5; 6; 7]%nat AG ltac:(idtac; tjc_kept AG Hfr Hpres2).
apply (st_ok_pi_restrict_fx fq fx') in HS.
clear RUNP RUNTOP RUNC BR.
pose (BR := paj_branch (fx := fx') (PI := PI)).
pose (RUNP := SRr_run_pi_AJ (fx := fx') B LAWS). pose (RUNTOP := SRr_run_to_pi_AJ (fx := fx') B LAWS).
pose (RUNC := SRr_run_pi_AJ_call (fx := fx') B LAWS).

prreg HS (10%bv : bv 5) Qr0. cbn [ms_regs] in Qr0. rewrite Ha0' in Qr0. symmetry in Qr0. unfold w64 in Qr0.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (E13v : ew Ev 13 = Z_to_bv 64 cap) by (rewrite (AG 13%nat) by lia; rewrite (HE0 13%nat 13%bv eq_refl); exact H13);
assert (U4 : U Ev (SAlu ALU_ADD (SOff 13 0) (SMd M_MUL (SOff 695 0) (SLit (-1)))) = cap - L)
by (rewrite U_SAlu; cbn [zalu_raw]; rewrite U_SMd; cbn [zmd_raw]; rewrite (U_atom Ev 13 cap E13v), (U_atom Ev 695 L E695) by lia; rewrite U_SLit; apply tjc_sub; [reflexivity | lia | lia]);
assert (U0 : U Ev (SOff 705 0) = 1) by (apply U_atom; [exact Qr0 | lia])
end.

psrr_branch_pi RUNP BR HS.
{ exfalso. lazymatch type of Hc with branch_taken _ (sv_denot ?Ev ?a) (sv_denot _ ?b) = _ =>
rewrite (denot_lit_U Ev a), (denot_lit_U Ev b) in Hc end.
rewrite U0, U_SLit in Hc. vm_compute in Hc. discriminate Hc. }
clear Hc.
paj_run_shc RUNP RUNC HS HJ2. { awrFL_with ltac:(idtac; tj_hd AG HSK) AG fpos F EFA0. }

lazymatch type of HFr with frame_of _ _ (mrestrict _ ?m0) (mrestrict _ ?m1) =>
assert (HK2 : forall a, buf <= a < buf + cap -> aview SEGS (w_H W3) m1 a = aview SEGS (w_H W3) m0 a)
by (intros a Ha; eapply aview_kept_out; [exact HFr | lia | notw AG]) end.
clear HF HFr HG.

psrr_branch_pi RUNP BR HS.
- rewrite branch_geu_U, U0, U4 in Hc. apply negb_true_iff, Z.ltb_ge in Hc.
paj_run_to_shc RUNTOP HS HJ2 0x621c. { awrFL_with ltac:(idtac; tj_hd AG HSK) AG fpos F EFA0. }
prreg HS (21%bv : bv 5) R21.
ra_join HS ss_tjX 640%nat ([1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 20; 21; 23; 24; 26; 27; 28; 29; 30; 31]%bv : list (bv 5)) idtac.
ra_join_val HS 640%nat 13%nat R21 E653.

hei_havoc HS. rebaseE HS AG HEv. clear HEv.
lazymatch goal with |- SRr _ ?Wg (mkCfg ?msF ?mdF) _ =>
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
eapply (tj_from0_at_fx B STK EV IMG _ _ FX (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0) fx' Ev k ly3 S3 Wg msF mdF Hf1 Hf2) end end.
+ exact HBASE.
+ unfold tj_EX, tj_F, tj_FL. cbn [c_ly c_fpos c_E0 c_sp1]. fold F FLg.
split; [exact AG|]. split; [exact E60|]. split; [exact E516|]. split; [exact E528|]. split; [exact E529 | assumption].
+ cbn [c_regs c_ly c_S c_W c_mem c_md c_fpos c_buf c_cap]. exact HJ2.
+ cbn [c_S c_fpos]. exact HFR.
+ unfold INV_tjX. cbn [c_cap c_T c_now c_buf c_ly c_S].
assert (Htl : tj_len T now = L + 1) by (unfold tj_len; rewrite Htxt, length_app; cbn [length]; unfold L; lia).
split; [lia|]. split; [exact Hperm|]. exists (-1). split.
{ rewrite E653. apply bv_eq. unfold w64. rewrite !Z_to_bv_unsigned. vm_compute. reflexivity. }
split; [intros; lia|]. split; [intros _ Hlt; exfalso; lia | intros _ _; reflexivity].
+ exact HS.
- rewrite branch_geu_U, U0, U4 in Hc. apply negb_false_iff, Z.ltb_lt in Hc.
paj_run_to_shc RUNTOP HS HJ2 0x621c. { awrFL_with ltac:(idtac; tj_hd AG HSK) AG fpos F EFA0. }
lazymatch type of HFr with frame_of _ _ (mrestrict _ ?m0) (mrestrict _ ?m1) =>
assert (HK3 : forall a, buf <= a < buf + cap -> aview SEGS (w_H W3) m1 a = aview SEGS (w_H W3) m0 a)
by (intros a Ha; eapply aview_kept_out; [exact HFr | lia | notw AG]) end.
clear HF HFr HG.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (Uw : U Ev (SAluw ALU_ADD (SOff 705 0) (SOff 695 0)) = 1 + L)
by (rewrite U_of_S, S_SAluw; cbn [zalu_raw]; rewrite U0, (U_atom Ev 695 L E695) by lia;
rewrite (Z.mod_small 1 (2 ^ 32)), (Z.mod_small L (2 ^ 32)) by lia; rewrite swrap32_id by lia;
unfold bv_wrap; change (bv_modulus 64) with (2 ^ 64); apply Z.mod_small; lia) end.
rregU HS (21%bv : bv 5) (1 + L) ltac:(exact Uw) R21.
ra_join HS ss_tjX 640%nat ([1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 20; 21; 23; 24; 26; 27; 28; 29; 30; 31]%bv : list (bv 5)) idtac.
ra_join_val HS 640%nat 13%nat R21 E653.

hei_havoc HS. rebaseE HS AG HEv. clear HEv.
lazymatch goal with |- SRr _ ?Wg (mkCfg ?msF ?mdF) _ =>
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
eapply (tj_from0_at_fx B STK EV IMG _ _ FX (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0) fx' Ev k ly3 S3 Wg msF mdF Hf1 Hf2) end end.
+ exact HBASE.
+ unfold tj_EX, tj_F, tj_FL. cbn [c_ly c_fpos c_E0 c_sp1]. fold F FLg.
split; [exact AG|]. split; [exact E60|]. split; [exact E516|]. split; [exact E528|]. split; [exact E529 | assumption].
+ cbn [c_regs c_ly c_S c_W c_mem c_md c_fpos c_buf c_cap]. exact HJ2.
+ cbn [c_S c_fpos]. exact HFR.
+ unfold INV_tjX. cbn [c_cap c_T c_now c_buf c_ly c_S].
assert (Htl : tj_len T now = L + 1) by (unfold tj_len; rewrite Htxt, length_app; cbn [length]; unfold L; lia).
split; [lia|]. split; [exact Hperm|]. exists (1 + L). split; [exact E653|].
split; [intros; lia|]. split; [|intros _ Hge; exfalso; lia].
intros _ _. split; [lia|].
rewrite Htxt, <- app_assoc. cbn [app].
apply (garr8_aview_kept SEGS (w_H W3) (w_H W3) mem2 _ buf).
{ intros a Ha. rewrite length_app in Ha. cbn [length] in Ha. rewrite HK3 by (unfold L in *; lia). apply HK2. unfold L in *; lia. }
apply (proj2 (garr8_app SEGS _ _ _ _)). split.
{ apply (garr8_aview_kept SEGS (w_H W3) (w_H W3) (ms_mem ms3) mem2 buf acc).
- intros a Ha. rewrite Hfr by (unfold L in *; lia). apply HK1. unfold L in *; lia.
- exact (proj1 (proj1 (garr8_app SEGS _ _ _ _) Hgarr)). }
fold L. apply (proj2 (garr8_app SEGS _ _ [93] [0])). split.
{ apply garr8_one_of_aview. pose proof (Hwr 0 ltac:(lia)) as Hq. rewrite Z.add_0_r in Hq.
change (nth (Z.to_nat 0) [93] 0) with 93 in Hq. exact Hq. }
{ apply garr8_one_of_aview. cbn [length Z.of_nat].
lazymatch goal with |- aview _ _ _ ?y = _ => lazymatch type of Hnul with aview _ _ _ ?x = _ => replace y with x by lia end end. exact Hnul. }
+ exact HS.
Qed.
End h.
End f.
End d.
