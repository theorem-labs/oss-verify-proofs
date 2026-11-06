(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/A/ACja.v for libreac/fuzz_disco's program walk, over fuzz_disco's listing. Image objects follow fuzz_disco.asan: the GOT word of the shadow-base cell is object 1 (atom 242), the GOT word of the side-stack flag is object 0 (atom 241), the shadow-base cell is object 66 (atom 307) and the side-stack flag cell is object 67 (atom 308), so img_factsF and img_hull_factsF give E240 E241 E242 E307 E308 and Hob241 Hob242 Hob307 Hob308, keptFL keeps those four regions, and aconstsF rewrites with PALib's pal_got_shadow, pal_cell and DiscoFrame's palf_got_uar. awrFL, keptFL, fs_roF and fs_rwF keep the walks' atoms for the own side-stack frame (516), its shadow (529), the realigned stack (60) and the stack (2), for any frame class; stack bounds compute the walk's own STK constant; cgif's case for its 40-byte FRAME block (atom 11) is left out, and awrFL_with/keptFL_with take a tactic for a walk's own head regions. Module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoACja.v, with its module paths, module names and numbers changed; 628 of its 693 lines of code are new or changed and 266 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/Y/Prog/TjRole.v, with its module names and numbers changed; 286 of its 426 lines of code are new or changed and 553 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YCkd AmemBlock8.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP0d YP0c YP07 YI0w YI0z YI12 YC4a YC8i.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC80 YC1f YC1g YC1h YC81 YC4b YC44 YC45 YC85 YC88.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC8g YC1i.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YCjr YCj1 YCja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import SnShared SnprintfDef PfFacts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require SnprintfDefR.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Rt Require Import SnprintfConsts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YRo.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YA0j.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import ReacDiscoTableJson TjBase TjCuts TjSnSh TjPreL.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_json_text.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require tj_lemmas.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require disco_table_c reac_disco_table_json_c.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
Context {RO : ro_below_ofl (@pa_segs _ lib_both3_0_listing PI) (@pa_relro_lo _ lib_both3_0_listing PI) (@pa_relro_hi _ lib_both3_0_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).

Lemma tjp_garr8_u4 : forall (m : word -> option byte) (a k : Z) (T : list byte),
garr8 SEGS m a (map bv_unsigned T) -> 0 <= k -> k + 4 <= Z.of_nat (length T) ->
val_mem SEGS m (a + k) 4 (disco_table_c.u_at T k 4).
Proof.
intros m a k T HG Hk HkT j Hj.
assert (Hlt : (Z.to_nat k + j < length (map bv_unsigned T))%nat) by (rewrite length_map; lia).
pose proof (garr8_mbyte SEGS m a _ (Z.to_nat k + j) HG Hlt) as Hb.
replace (a + Z.of_nat (Z.to_nat k + j)) with (a + k + Z.of_nat j) in Hb by lia.
rewrite Hb. f_equal.
assert (Hnth : nth_error (disco_table_c.sub T k 4) j = Some (nth (Z.to_nat k + j) T (Z_to_bv 8 0))).
{ unfold disco_table_c.sub. rewrite nth_error_firstn. destruct (Nat.ltb_spec j 4); [|lia].
rewrite nth_error_skipn. apply nth_error_nth'. lia. }
pose proof (YA0j.nth_error_le_byte _ _ _ Hnth) as Hv.
rewrite (nth_indep (map bv_unsigned T) 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; lia).
rewrite map_nth. rewrite Hv. unfold disco_table_c.u_at, YO0f.le_byte.
pose proof (bytes_le_to_Z_nonneg (disco_table_c.sub T k 4)) as H0.
pose proof (bytes_le_to_Z_bound (disco_table_c.sub T k 4)) as H1.
assert (Hlen : length (disco_table_c.sub T k 4) = 4%nat) by (unfold disco_table_c.sub; rewrite length_firstn, length_skipn; lia).
rewrite Hlen in H1. rewrite (Z.mod_small _ (2 ^ (8 * Z.of_nat 4))) by lia.
rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

Lemma tjp_sext_lts : forall E n u, ew E n = Z_to_bv 64 u -> 0 <= u < 2 ^ 32 ->
bv_lts (sv_denot E (SLit 0)) (sv_denot E (SExt true 32 (SOff n 0))) = (0 <? bv_swrap 32 u).
Proof.
intros E n u Hn Hu. unfold bv_lts. rewrite !(denot_lit_U E). rewrite U_SExt, (U_atom E n u Hn) by lia. rewrite U_lit by lia.
rewrite !signed_lit. rewrite (Z.mod_small u (2 ^ Z.of_N 32)) by (change (2 ^ Z.of_N 32) with (2 ^ 32); lia).
replace (zcanon (zcanon (bv_swrap 32 u))) with (zcanon (bv_swrap 32 u)) by (unfold zcanon; rewrite Zmod_mod; reflexivity).
rewrite swrap64_zcanon_swrap32. reflexivity.
Qed.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TLF : PALibF B.
Variables SNPC GC GV IMGLO IMGHI : Z.
Variable CR : list (Z * Z).
Hypothesis HSNPC : SIGMA AS___interceptor_trampoline_snprintf = SNPC.
Hypothesis ASNP : forall fq : YK11.FPState,
SnprintfDefR.sh_asnprintf_realizesR (fx := fq) SEGS B pa_relro_lo pa_relro_hi (SnFF.FF_disco disco_fmt_lo disco_fmt_hi) SNPRINTF_STK GC GV IMGLO IMGHI CR SNPC.
Hypothesis tj_snp_consts : forall (W : world SEGS) mem, arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) -> consts_view SEGS W mem CR.
Hypothesis tj_snp_cr : Forall (fun r => IMG_LO <= fst r /\ 0 <= snd r /\ fst r + snd r <= IMG_TOP) CR.
Hypothesis tj_snp_canary : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
exists cval, rdword (aview SEGS (w_H W) mem) GC = Some GV /\ rdword (aview SEGS (w_H W) mem) GV = Some cval.
Hypothesis tj_snp_gcgv : IMG_LO <= GC /\ GC + 8 <= IMG_TOP /\ IMG_LO <= GV /\ GV + 8 <= IMG_TOP.
Hypothesis tj_snp_img : IMG_LO <= IMGLO /\ IMGHI <= IMG_TOP.
Hypothesis GM : globs_marked SEGS B tfib_globs.
Hypothesis HV : img_shadow_vis SEGS B.
Hypothesis DRO : tfib_ro_unowned B.
Hypothesis TJS : tj_strs.
Variable IMG : world SEGS -> (word -> option byte) -> Prop.
Hypothesis FX : tj_fromX B IMG.
Hypothesis FC : tj_fromC B IMG.
Hypothesis FL : tj_fromL B IMG 0.
Theorem pb_tj_pre : tj_from0 B IMG ss_tj0 (INV_tj0 B 0).
Proof.
unfold tj_from0.
intros cx E k ly3 S3 W3 ms3 md3 HBASE HEX HJ HFR HINV HS.
destruct cx as [fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0].
pose proof HBASE as HB0. pose proof HEX as HX0.
unfold tj_baseX in HB0. unfold tj_EX, tj_F, tj_FL in HX0. unfold INV_tj0 in HINV.
cbn [c_fq c_ly c_S c_W c_regs c_mem c_md c_ch c_t c_now c_buf c_cap c_Nb c_T c_fpos c_sp1 c_E0 tj_F tj_FL]
in HB0, HX0, HINV, HJ, HFR, HS.
destruct HB0 as (HPRE & Hroom & HROD & HIM & H10 & H11 & H12 & H13 & Hnow & Hcap & Hobj & Harr & HlenT & Hok
& Hbuf & Hsp1b & HE0 & HE032 & HE033 & HE02 & Hfrm).
destruct HX0 as (AG & E60 & E516 & E528 & E529 & HEI).
destruct HINV as (Hk0 & Hab).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity. assert (HSNP : SNPRINTF_STK = 11776) by reflexivity.
assert (HSK : 12416 <= REAC_DISCO_TABLE_JSON_STK) by (unfold REAC_DISCO_TABLE_JSON_STK; lia).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBOK. pose proof pa_base_lo as HBLO.
destruct (sp1_facts (spZ regs + -288) ltac:(clear - Hceil Hslo Hstk0 HSK C1; lia)
ltac:(rewrite <- Zplus_mod_idemp_l, Hal16; reflexivity)) as (Hsp1r & Hsp1al & Hsp1al16).
rewrite <- Hsp1b in Hsp1r, Hsp1al, Hsp1al16.
assert (Hsp1 : spZ regs - 304 <= sp1 <= spZ regs - 288) by (clear - Hsp1r; lia). clear Hsp1r.
pose (RUN := paj_run (fx := fq) B LAWS). pose (RUNTO := paj_run_to (fx := fq) B LAWS).
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
assert (E10 : ew E 10 = Z_to_bv 64 t) by (rewrite (AG 10%nat ltac:(lia)); rewrite (HE0 10%nat 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 now) by (rewrite (AG 11%nat ltac:(lia)); rewrite (HE0 11%nat 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 buf) by (rewrite (AG 12%nat ltac:(lia)); rewrite (HE0 12%nat 12%bv eq_refl); exact H12).
assert (E13 : ew E 13 = Z_to_bv 64 cap) by (rewrite (AG 13%nat ltac:(lia)); rewrite (HE0 13%nat 13%bv eq_refl); exact H13).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite (AG 32%nat ltac:(lia)); exact HE032).
assert (E33 : ew E 33 = Z_to_bv 64 (as_uar_cell B)) by (rewrite (AG 33%nat ltac:(lia)); exact HE033).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (AG 2%nat ltac:(lia)); exact HE02).
assert (AG33 : forall n, (n < 33)%nat -> ew E n = ew E0 n) by (intros n Hn; apply AG; lia).
clear AG. rename AG33 into AG.
img_factsF E.
pose proof (pa_obj_img 0 ltac:(lia)) as Hob241. pose proof (pa_obj_img 1 ltac:(lia)) as Hob242.
pose proof (pa_obj_img 12 ltac:(lia)) as Hob253.
cbv [A_OBJ Nat.add] in Hob241, Hob242, Hob253.
pose proof (palf_uar_img B TLF) as Huar. pose proof (palf_uar_al B TLF) as Huar4.
unfold IMG_LO, IMG_TOP in Hob241, Hob242, Hob253, Huar.
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos HAR3 Hfin) as (HFal & [HFhi _] & HFpres & HFSpres).
rewrite EFA in HFal, HFhi, HFpres, HFSpres. fold F in HFal, HFhi, HFpres, HFSpres.
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 2 fpos HAR3 Hfin) as (HF4096 & HFceil & HFhigh).
rewrite EFA in HF4096, HFceil, HFhigh. fold F in HF4096, HFceil, HFhigh.
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR3 Hfin) as HFhigh_img. rewrite EFA in HFhigh_img. fold F in HFhigh_img.
change (fs_frame_bytes 2) with 256 in *.
assert (HF3 : frame_addr ly3 2 fpos = F) by (rewrite EFA; reflexivity).
assert (HFq : F = 32 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(lia)); lia).
assert (HF8lo : 512 <= F / 8) by (apply Z.div_le_lower_bound; lia).
assert (HF8hi : F / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia).
fs_roF HS.
shok_auto SHOK (SOff 32 0) E (mrestrict (w_H W3) (ms_mem ms3)).
psrr_branch_tok RUN BR HS SHOK Bspan.

- hei_havoc HS; paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x6274. { tjl_awr ltac:(idtac; tjl_hd AG HSK) AG fpos F EFA0. }
clear_frames.
lazymatch goal with Hc : branch_taken _ _ _ = true |- _ =>
rewrite branch_ltu_U, (U_atom E 13 cap E13 ltac:(lia)), U_lit in Hc by lia; apply Z.ltb_lt in Hc end.
pose proof HJ as (HARx & _).
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos HARx Hfin) as (_ & _ & _ & HFSx).
rewrite HF3 in HFSx. change (fs_frame_bytes 2 / 8) with 32 in HFSx.
tjl_rw HS E529 HFSx.
prreg HS (23%bv : bv 5) R23.
ra_join HS ss_tjX 640%nat ([1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 20; 23; 21; 24; 26; 27; 28; 29; 30; 31]%bv : list (bv 5)) idtac.
ra_join_val HS 640%nat 13%nat R23 E653.
hei_havoc HS. rebaseE HS AG HEv. clear HEv.
lazymatch goal with |- SRr _ ?Wg (mkCfg ?msF ?mdF) _ =>
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
eapply (FX (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0) Ev k _ _ Wg msF mdF) end end.
+ exact HBASE.
+ unfold tj_EX, tj_F, tj_FL. cbn [c_ly c_fpos c_E0 c_sp1]. fold F FLg.
split; [intros n Hn; destruct (Nat.eq_dec n 33) as [->|Hn33]; [rewrite E33; symmetry; exact HE033 | apply AG; lia]|].
split; [exact E60|]. split; [exact E516|]. split; [exact E528|]. split; [exact E529 | assumption].
+ cbn [c_regs c_ly c_S c_W c_mem c_md c_fpos c_buf c_cap]. exact HJ.
+ cbn [c_S c_fpos]. exact HFR.
+ unfold INV_tjX. cbn [c_ly c_S c_cap c_T c_now c_buf].
split; [lia|]. split; [rewrite Hab; apply Permutation_refl|].
exists (-1). split; [rewrite E653; unfold w64; apply bv_eq; rewrite !Z_to_bv_unsigned; vm_compute; reflexivity|].
split; [intros _; reflexivity|]. split; [intros H3; lia|]. intros _ _; reflexivity.
+ cbn [c_fq]. exact HS.

- lazymatch goal with Hc : branch_taken _ _ _ = false |- _ =>
rewrite branch_ltu_U, (U_atom E 13 cap E13 ltac:(lia)), U_lit in Hc by lia; apply Z.ltb_ge in Hc; rename Hc into Hc3 end.
destruct (Hbuf Hc3) as (Hbin & Hbsz).
assert (Hbin3 : In (buf, Nb) (ablocks B ly3 S3)) by (rewrite Hab; exact Hbin).
hei_havoc HS; paj_run_tok RUN HS HJ SHOK Bspan. { tjl_awr ltac:(idtac; tjl_hd AG HSK) AG fpos F EFA0. }
clear_frames.
prreg HS (2%bv : bv 5) Qsp. prreg HS (3%bv : bv 5) Qgp. prreg HS (4%bv : bv 5) Qtp. prreg HS (1%bv : bv 5) Qra.
prreg HS (10%bv : bv 5) Qa0. prreg HS (11%bv : bv 5) Qa1. prreg HS (12%bv : bv 5) Qa2.
pmkst HS.
pose proof HJ as (HARc & _).
destruct (tj_snp_canary _ _ _ _ _ HARc) as (cval & HG1 & HG2).
destruct (al_blocks _ _ LAWS _ _ _ _ _ buf Nb HARc Hbin3) as (Hb16 & Hb4096 & Hbceil & Hbapp & Hbpres & _ & HbMAX).
pose proof (blk_off_imgP _ _ _ _ _ _ _ _ HARc Hbin3) as Hbimg.
destruct (al_shadow _ _ LAWS _ _ _ _ _ buf Nb HARc Hbin3) as (Hbsh & Hbhull).
pose proof (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HROD) as HRODc.
pose proof TJS as (TJ39 & _).
unfold tj_ro_at, tj_s_open in TJ39. cbn [A_OBJ Nat.add length app] in TJ39. change (Z.of_nat 1 + 1) with 2 in TJ39.
destruct TJ39 as (Hg39 & Hro39 & Hlo39 & Hhi39 & Hch39 & Hby39).
unfold IMG_LO, IMG_TOP in Hlo39, Hhi39.
pose proof tj_snp_gcgv as Hgcgv. unfold IMG_LO, IMG_TOP in Hgcgv.
assert (E280 : ew E 280 = Z_to_bv 64 (VAL 280)) by (apply img_env_atomP; [assumption | unfold A_TEXT, A_LIM; lia]).
assert (Hsp1e : bv_unsigned (getr (ms_regs ms) 2) = sp1) by (rewrite Qsp, E60; apply unsigned_lit_small; lia).
rewrite HSNPC.
lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_sh_snprintf_at B LAWS Hsegs REAC_DISCO_TABLE_JSON_STK fq GC GV IMGLO IMGHI CR SNPC (ASNP fq) W3 (ms_regs msX) (ms_mem msX)
(spZ regs) (tj_fp buf cap) ly S W mem md [(2, fpos)] ly3 S3 _ k buf cap (VAL 280) [91] [PLit 91] []
(map (argZ (ms_regs msX)) [3; 4; 5; 6; 7] ++ []) [] [91] cval (sp1 - spZ regs) (Z_to_bv 64 (BASE + 23544)) _ HJ HRODc) end.
{ unfold spZ at 1. rewrite Hsp1e. lia. }
{ rewrite <- Zminus_mod_idemp_l, Hsp1al16, <- Zminus_mod_idemp_r, Hal16. reflexivity. }
{ lia. }
{ rewrite HSNP. lia. }
{ rewrite Qgp, E3. exact Hgp. }
{ rewrite Qtp, E4. exact Htp. }
{ exact Qra. }
{ apply ret_ok_codeptr_v; [lia | reflexivity]. }
{ rewrite Qa0, E12. reflexivity. }
{ rewrite Qa1, E13. reflexivity. }
{ rewrite Qa2, E280. reflexivity. }
{ exact (tj_snp_consts _ _ HRODc). }
{ eapply Forall_impl; [|exact tj_snp_cr]. intros r Hr. unfold IMG_LO, IMG_TOP in Hr. lia. }
{ unfold snp_out. rewrite HSNP. eapply Forall_impl; [|exact tj_snp_cr]. intros [lo0 n0] (H1 & H2 & H3). cbn [fst snd] in *.
apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold zdisjoint; cbn [fst snd];
clear - H1 H2 H3 Hbimg Hbsz Hsp1 Hceil Hslo C1 Hc3 HSK; unfold off_img, IMG_LO, IMG_TOP in *; lia. }
{ exact HG1. }
{ exact HG2. }
{ clear - Hgcgv. lia. }
{ clear - Hgcgv. lia. }
{ clear - Hgcgv. lia. }
{ clear - Hgcgv. lia. }
{ unfold snp_out. rewrite HSNP. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold zdisjoint; cbn [fst snd];
clear - Hgcgv Hbimg Hbsz Hsp1 Hceil Hslo C1 Hc3 HSK; unfold off_img, IMG_LO, IMG_TOP in *; lia. }
{ unfold snp_out. rewrite HSNP. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold zdisjoint; cbn [fst snd];
clear - Hgcgv Hbimg Hbsz Hsp1 Hceil Hslo C1 Hc3 HSK; unfold off_img, IMG_LO, IMG_TOP in *; lia. }
{ assert (Hin2 : In (VAL 280, 2) tfib_ro_ranges) by (unfold tfib_ro_ranges; apply in_or_app; left; exact Hg39).
pose proof (tfib_ro_unowned_at B (VAL 280) 2 DRO Hin2) as Hun.
unfold fmt_at, snp_out; cbn [length Z.of_nat]; rewrite HSNP.
split; [lia|]. split.
- intros i Hi.
rewrite (ro_bytes SEGS pa_relro_lo pa_relro_hi B _ (VAL 280) 2 (VAL 280 + i) HRODc (Hro39 (VAL 280 + i) ltac:(lia)) Hun ltac:(lia)).
assert (Hi01 : i = 0 \/ i = 1) by lia. destruct Hi01 as [-> | ->].
+ pose proof (Hby39 0%nat ltac:(cbn; lia)) as Hb. cbn [Z.of_nat nth app] in Hb |- *. exact Hb.
+ pose proof (Hby39 1%nat ltac:(cbn; lia)) as Hb. cbn [Z.of_nat nth app] in Hb |- *. exact Hb.
- split; [apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold zdisjoint; cbn [fst snd];
clear - Hlo39 Hhi39 Hbimg Hbsz Hsp1 Hceil Hslo C1 Hc3 HSK; unfold off_img, IMG_LO, IMG_TOP in *; lia|].
split; [unfold amem_range, kLowMemEnd; lia|].
apply (ro_read_ok_glob SEGS B tfib_globs _ _ _ _ _ (VAL 280) 2 (VAL 280) 2 GM Hg39 HV HARc); unfold IMG_LO, IMG_TOP; lia. }
{ exact (tj_ro_fmt_rng 39 tj_s_open (proj1 TJS) ltac:(cbv; lia)). }
{ discriminate. }
{ reflexivity. }
{ constructor; [exact I | constructor]. }
{ split; [reflexivity | intros i Hi; cbn in Hi; lia]. }
{ cbn [length Z.of_nat]. lia. }
{ cbn [length Z.of_nat]. unfold snp_out. rewrite HSNP. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
unfold zdisjoint; cbn [fst snd]; lia. }
{ exact I. }
{ exact I. }
{ reflexivity. }
{ lia. }
{ cbn. lia. }
{ lia. }
{ clear - Hbceil Hbsz C1 Hc3. lia. }
{ unfold snp_out. rewrite HSNP. cbn [pairwise].
split; [apply Forall_cons; [|apply Forall_nil] | split; [apply Forall_nil | exact I]].
unfold zdisjoint; cbn [fst snd]. clear - Hbceil Hbsz Hsp1 Hceil Hslo C1 Hc3 HSK. lia. }
{ intros a Ha. split; [|rewrite Hes; clear - Ha Hbceil Hbsz Hsp1 Hceil Hslo C1 Hc3 HSK; lia].
right. left. split.
- unfold tj_fp. rewrite (proj2 (Z.ltb_ge cap 3) Hc3). exists (buf, buf + cap). split; [left; reflexivity | cbn [fst snd]; lia].
- exists buf, Nb. split; [exact Hbin3 | lia]. }
{ apply (amem_range_of_block8 SEGS B LAWS _ _ _ _ _ buf Nb _ _ HARc Hbin3); lia. }
{ apply (block_shadow_range _ _ buf (req_size Nb) buf cap Hbsh); lia. }
{ intros s0 Hs0. apply Hbhull. split; [lia|].
assert (shadow_addr (buf + cap - 1) / 8 <= shadow_addr (buf + req_size Nb - 1) / 8)
by (apply Z.div_le_mono; [lia|]; unfold shadow_addr; apply Z.add_le_mono_l; apply Z.div_le_mono; lia).
lia. }
{ eapply tj_dest_off_globals; [exact (proj1 tj_snp_img) | exact (proj2 tj_snp_img) | exact HARc | exact Hbin3 | lia | lia]. }
{ exact Hfrm. }
intros fx' regs2 mem2 md2 Hf1 Hf2 HJ2 HP2 Ha0 Hwr Hnul Hfr Hpres2 Hsame.
clear Qsp Qgp Qtp Qra Qa0 Qa1 Qa2 HJ SHOK.
assert (Hmin : Z.min (Z.of_nat (length [91])) (cap - 1) = 1) by (cbn [length Z.of_nat]; lia).
rewrite Hmin in Hwr, Hnul, Hfr.
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ buf Nb 2 fpos HARc Hbin3 Hfin) as HdBF.
unfold zdisjoint in HdBF. cbn [fst snd] in HdBF. rewrite HF3 in HdBF. change (fs_frame_bytes 2) with 256 in HdBF.
reseat HS HJ2 HP2 [0; 1; 2; 3; 4; 5; 6; 7]%nat AG
ltac:(idtac; eapply region_kept_aview;
[ evalE AG
| let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; apply Hfr;
[ unfold off_img, IMG_LO, IMG_TOP, SB in *; lia
| unfold off_img, in_app, IMG_LO, IMG_TOP, SB, kLowShadowBeg, kHighMemBeg in *; lia
| rewrite ?HSNP; unfold off_img, IMG_LO, IMG_TOP, SB in *; lia ]
| exact Hpres2 ]).
apply (st_ok_pi_restrict_fx fq fx') in HS.
clear RUN RUNTO BR.
pose (RUN := paj_run (fx := fx') B LAWS). pose (RUNTO := paj_run_to (fx := fx') B LAWS).
pose (BR := paj_branch (fx := fx') (PI := PI)).
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
pose proof (st_ok_pi_pin_reg' Ev ssx msx (10%bv : bv 5) 1 HS ltac:(cbn [ms_regs restrict mkst]; rewrite Ha0; reflexivity) ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.

assert (HG91 : garr8 SEGS (mrestrict (w_H W3) mem2) buf ([91] ++ [0])).
{ apply (proj2 (garr8_app SEGS _ _ [91] [0])). split.
- apply garr8_one_of_aview. pose proof (Hwr 0 ltac:(lia)) as Hq. rewrite Z.add_0_r in Hq. exact Hq.
- apply garr8_one_of_aview. cbn [length Z.of_nat]. exact Hnul. }
pose proof Hbapp as Hbapp'. unfold in_app, kLowShadowBeg, kHighMemBeg in Hbapp'.

pose proof (tjl_keep_journal B LAWS IMG (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0) _ _ _ _ _ _ _ HBASE HJ2) as HK2.
unfold tj_keep in HK2. cbn [c_t c_T c_ly c_S] in HK2.
destruct HK2 as (HROD2 & HarrT2 & HobjT2).
pose proof HobjT2 as ((tcid & tpos & Htin & Htcid & Htal8 & Htflo & Htfhi) & Ht8 & HtRA).
set (u := disco_table_c.u_at T 384 4).
assert (Hu4 : val_mem SEGS (mrestrict (w_H W3) mem2) (t + 384) 4 u)
by (apply tjp_garr8_u4; [exact HarrT2 | lia | rewrite HlenT; lia]).
assert (Hurange : 0 <= u < 2 ^ 32).
{ unfold u, disco_table_c.u_at. pose proof (bytes_le_to_Z_nonneg (disco_table_c.sub T 384 4)) as H0.
pose proof (bytes_le_to_Z_bound (disco_table_c.sub T 384 4)) as H1.
assert (Hlen : length (disco_table_c.sub T 384 4) = 4%nat) by (unfold disco_table_c.sub; rewrite length_firstn, length_skipn, HlenT; lia).
rewrite Hlen in H1. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in H1. lia. }
assert (HtF : In (tcid, tpos) (frames S3)) by (rewrite HFR; right; exact Htin).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ tcid tpos HARc HtF) as (Ht4096 & Htceil & Htapp).
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HARc HtF) as Htimg.
rewrite EFA in Ht4096, Htceil, Htapp, Htimg.
destruct (in_split _ _ Htin) as (l2 & l3 & Hsplit).
pose proof (sep_frames_pos SEGS B LAWS _ _ _ _ _ (2, fpos) (tcid, tpos) [] l2 l3 HARc ltac:(rewrite HFR, Hsplit; reflexivity)) as HdFT.
unfold zdisjoint, frame_rng in HdFT. cbn [fst snd] in HdFT. rewrite !EFA in HdFT. fold F in HdFT. change (fs_frame_bytes 2) with 256 in HdFT.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_havoc_hi 600 Ev ssv msv [Z_to_bv 64 u] HS ltac:(vm_compute; reflexivity)) as HS3; hei_pose Ev 600%nat [Z_to_bv 64 u] end.
clear HS. rename HS3 into HS. rebaseE HS AG HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (E600 : ew Ev 600 = Z_to_bv 64 u) by (rewrite HEv; exact (ew_havoc_new _ 600 [Z_to_bv 64 u] 0 (Z_to_bv 64 0) ltac:(cbn; lia)));
assert (E10v : ew Ev 10 = Z_to_bv 64 t) by (rewrite (AG 10%nat ltac:(lia)); rewrite (HE0 10%nat 10%bv eq_refl); exact H10);
assert (E12v : ew Ev 12 = Z_to_bv 64 buf) by (rewrite (AG 12%nat ltac:(lia)); rewrite (HE0 12%nat 12%bv eq_refl); exact H12)
end.
clear HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 10%nat) 384 388 0 0 [YP09.mkChunk 384 (CVal 4 (SOff 600 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite E10v, unsigned_lit_small by (clear - Ht4096 Htflo Htfhi Htceil C1; lia);
split; [clear - Ht4096 Htflo Htfhi Htceil C1; lia|]; split; [clear - Ht4096 Htflo Htfhi Htceil C1; lia|];
split; [intros o Ho; clear - Ho; lia|];
apply Forall_cons; [|apply Forall_nil];
apply (chunk_ok_val SEGS Ev _ t 384 4 (SOff 600 0) u);
[cbn [sv_denot]; rewrite E600, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | zside | exact Hu4])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite E10v; evalE AG;
clear - Htflo Htfhi Ht4096 Htceil Htapp Htimg HdFT HF4096 HFceil HF8lo HF8hi Hsp1 Hceil Hslo Hshi H47 HSK C1 C3
Hob241 Hob242 Hob253 Huar;
unfold off_img, in_app, IMG_LO, IMG_TOP, SB, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *;
repeat split; lia)) as HS3; clear HS; rename HS3 into HS end.
norm_ss HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_fact Ev _ _ 10 (mkAF 4096 140737479966720 3) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E10v, unsigned_lit_small by (clear - Ht4096 Htflo Htfhi Htceil C1; lia);
change (2 ^ 3) with 8; clear - Ht4096 Htflo Htfhi Htceil C1 Ht8; lia)) as HS3;
clear HS; rename HS3 into HS end.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_fact Ev _ _ 12 (mkAF 4096 140737479966720 4) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E12v, unsigned_lit_small by (clear - Hb4096 Hbceil Hbsz Hc3 C1; lia);
change (2 ^ 4) with 16; clear - Hb4096 Hbceil Hbsz Hc3 Hb16 C1; lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
assert (Hshe : forall Ev, ew Ev 10 = Z_to_bv 64 t -> ew Ev 32 = Z_to_bv 64 SB ->
shent_ok SEGS (SOff 32 0) Ev (mrestrict (w_H W3) mem2) (mkSHE 10 0 400)).
{ intros Ev H10v H32v. unfold shent_ok, app_apart. cbn [she_m she_lo she_hi].
rewrite (U_atom Ev 32 SB H32v) by (unfold SB; lia). rewrite (U_atom Ev 10 t H10v) by lia.
rewrite <- (aview_rd_of SEGS). split; [rewrite Z.add_0_r; exact HtRA|].
intros x Hx. unfold in_app, SB, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia. }
lazymatch type of HS with st_ok_pi _ _ ?Ex _ (restrict (w_H ?Wx) ?msx) =>
assert (E32x : ew Ex 32 = Z_to_bv 64 SB) by (rewrite (AG 32%nat ltac:(lia)); exact HE032);
shok_auto_with SHOK (SOff 32 0) Ex (mrestrict (w_H Wx) (ms_mem msx)) [mkSHE 10 0 400]
ltac:(idtac; cbn [ms_mem restrict mkst]; exact (Hshe Ex E10v E32x)) end.

hei_havoc HS; paj_run_tok RUN HS HJ2 SHOK Bspan. { tjl_awr ltac:(idtac; tjl_hd AG HSK) AG fpos F EFA0. }
tjl_carry HG91 HFr AG. clear_frames.
psrr_branch_tok RUN BR HS SHOK Bspan.
{ exfalso. lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (E13v : ew Ev 13 = Z_to_bv 64 cap) by (rewrite (AG 13%nat ltac:(lia)); rewrite (HE0 13%nat 13%bv eq_refl); exact H13) end.
rewrite branch_geu_U, U_lit, (U_atom _ 13 cap E13v) in Hc by lia. apply negb_true_iff, Z.ltb_ge in Hc. lia. }
clear Hc.
hei_havoc HS; paj_run_tok RUN HS HJ2 SHOK Bspan. { tjl_awr ltac:(idtac; tjl_hd AG HSK) AG fpos F EFA0. }
tjl_carry HG91 HFr AG. clear_frames.
assert (Hnu : disco_table_c.n_of T = bv_swrap 32 u) by reflexivity.
pose proof Hok as ((Hn1 & Hn2) & _). rewrite Hnu in Hn1, Hn2.
psrr_branch_tok RUN BR HS SHOK Bspan.
+ cbn [branch_taken] in Hc. rewrite (tjp_sext_lts _ 600 u E600 Hurange) in Hc. apply negb_true_iff, Z.ltb_ge in Hc.
assert (Hn0 : disco_table_c.n_of T = 0) by lia.
hei_havoc HS; paj_run_to_tok RUNTO HS HJ2 SHOK Bspan 0x61f4. { tjl_awr ltac:(idtac; tjl_hd AG HSK) AG fpos F EFA0. }
tjl_carry HG91 HFr AG. clear_frames.
pose proof HJ2 as (HARx & _).
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos HARx Hfin) as (_ & _ & _ & HFSx).
rewrite HF3 in HFSx. change (fs_frame_bytes 2 / 8) with 32 in HFSx.
tjl_rw HS E529 HFSx.
prreg HS (26%bv : bv 5) R26.
ra_join HS ss_tjC 680%nat ([1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 19; 23; 24; 26; 27; 28; 29; 30; 31]%bv : list (bv 5)) idtac.
ra_join_val HS 680%nat 15%nat R26 E695.
hei_havoc HS. rebaseE HS AG HEv. clear HEv.
lazymatch goal with |- SRr _ ?Wg (mkCfg ?msF ?mdF) _ =>
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
eapply (tj_from0_at_fx B IMG _ _ FC (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0) fx' Ev k _ _ Wg msF mdF Hf1 Hf2) end end.
* exact HBASE.
* unfold tj_EX, tj_F, tj_FL. cbn [c_ly c_fpos c_E0 c_sp1]. fold F FLg.
split; [intros n Hn; destruct (Nat.eq_dec n 33) as [->|Hn33]; [rewrite E33; symmetry; exact HE033 | apply AG; lia]|].
split; [exact E60|]. split; [exact E516|]. split; [exact E528|]. split; [exact E529 | assumption].
* cbn [c_regs c_ly c_S c_W c_mem c_md c_fpos c_buf c_cap]. exact HJ2.
* cbn [c_S c_fpos]. exact HFR.
* unfold INV_tjC. cbn [c_ly c_S c_cap c_T c_now c_buf].
split; [lia|]. split; [rewrite Hab; apply Permutation_refl|].
split; [pose proof (tjl_keep_journal B LAWS IMG _ _ _ _ _ _ _ _ HBASE HJ2) as HKk; unfold tj_keep in HKk |- *;
cbn [c_t c_T c_ly c_S] in HKk |- *; exact HKk|]. split; [lia|].
exists [91]. split; [rewrite E695; reflexivity|]. split; [cbn [length Z.of_nat]; lia|].
split; [|exact HG91].
pose proof (tj_lemmas.tj_rest_end T now ltac:(lia)) as Hre. rewrite Hn0 in Hre.
rewrite tj_lemmas.tj_rest_0, Hre. reflexivity.
* exact HS.
+ cbn [branch_taken] in Hc. rewrite (tjp_sext_lts _ 600 u E600 Hurange) in Hc. apply negb_false_iff, Z.ltb_lt in Hc.
assert (Hnpos : 0 < disco_table_c.n_of T) by lia.
norm_ss HS.
pose proof (tj_baseX_fx B IMG _ fx' HBASE Hf2) as HBASE'.
cbn [c_fq c_ly c_S c_W c_regs c_mem c_md c_ch c_t c_now c_buf c_cap c_Nb c_T c_fpos c_sp1 c_E0] in HBASE'.
eapply SRr_mono; [clear HBASE; eapply pb_tj_pre_L; eassumption|].
intros W' c' _ Hq. exact (tj_postX_fx B (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0) fx' W' c' Hf1 Hf2 Hq).
Qed.
End h.
End f.
End d.
