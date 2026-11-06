(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACam.v, with its module paths, module names and numbers changed; 1071 of its 1108 lines of code are new or changed and 293 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/TjModel.v; 382 of its 536 lines of code are new or changed and 954 lines of the source are left out. *)
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
Ltac prreg_raw HS r Hr :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
cbn [ms_regs restrict mkst] in Hr end.
Ltac keep_buf HBK HFr AG :=
let HBK' := fresh "HBK" in
lazymatch type of HFr with frame_of ?Ef ?rs (mrestrict _ ?m0) (mrestrict _ (ms_mem ?msX)) =>
lazymatch type of HBK with forall a, ?lo <= a < ?hi -> aview ?sg ?Hh _ a = aview _ ?Hw ?me a =>
assert (HBK' : forall a, lo <= a < hi -> aview sg Hh (ms_mem msX) a = aview sg Hw me a);
[ let a := fresh "a" in let Ha := fresh "Ha" in
intros a Ha; etransitivity; [|exact (HBK a Ha)]; eapply (aview_kept_out Ef rs _ _ _ HFr a); [lia|];
let rg := fresh "rg" in let Hin := fresh "Hin" in let Hrg := fresh "Hrg" in
intros (rg & Hin & Hrg);
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In rg rs1) in Hin end; cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrg; revert Hrg; evalE AG; intros Hrg; lia|]);
destruct Hin
| clear HBK; rename HBK' into HBK ] end end.
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
Context {RO : ro_below_ofl (@pa_segs _ disco_listing PI) (@pa_relro_lo _ disco_listing PI) (@pa_relro_hi _ disco_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
Lemma tj_bt_ge0 : forall (Ev : env) u n, ew Ev 600 = Z_to_bv 64 u -> 0 <= u < 2 ^ 32 -> n = bv_swrap 32 u -> 0 <= n <= 8 ->
branch_taken BC_GE (sv_denot Ev (SLit 0)) (sv_denot Ev (SExt true 32 (SOff 600 0))) = negb (0 <? n).
Proof.
intros Ev u n H Hu Hn Hr.
rewrite (denot_lit_U Ev (SExt true 32 (SOff 600 0))), U_SExt, (U_atom Ev 600 u H ltac:(lia)).
rewrite (Z.mod_small u) by lia. rewrite <- Hn, zcanon_id by (unfold M64; lia).
cbn [branch_taken sv_denot]. unfold bv_lts. rewrite !Z_to_bv_signed.
unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
change (2 ^ Z.of_N 64) with (2 ^ 64). change (2 ^ (Z.of_N 64 - 1)) with (2 ^ 63).
rewrite (Z.mod_small (0 + 2 ^ 63)) by lia. rewrite (Z.mod_small (n + 2 ^ 63)) by lia.
change (2 ^ 64 / 2) with (2 ^ 63). replace (0 + 2 ^ 63 - 2 ^ 63) with 0 by lia. replace (n + 2 ^ 63 - 2 ^ 63) with n by lia. reflexivity.
Qed.
Lemma tj_garr8_of_aview : forall (W : world SEGS) (m : word -> option byte) a l,
(forall j, (j < length l)%nat -> aview SEGS (w_H W) m (a + Z.of_nat j) = Some (nth j l 0)) ->
garr8 SEGS (mrestrict (w_H W) m) a l.
Proof.
intros W m a l H j Hj. destruct (aview_byte SEGS _ m _ _ (H j Hj)) as (b & Hb & Hv & Hr).
split; [|exact Hr]. intros k Hk. assert (k = 0%nat) as -> by lia. cbn [Z.of_nat]. rewrite Z.add_0_r, Hb. f_equal.
apply bv_eq. rewrite Z_to_bv_unsigned. unfold YO0f.le_byte, bv_wrap. rewrite Hv.
pose proof (bv_unsigned_in_range 8 b) as Hb8. change (bv_modulus 8) with 256 in *.
change (2 ^ (8 * Z.of_nat 1)) with 256. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
rewrite !(Z.mod_small (bv_unsigned b) 256) by lia. reflexivity.
Qed.
Lemma tj_U_shadow : forall (Ev : env) n m v c, ew Ev m = Z_to_bv 64 SB -> ew Ev n = Z_to_bv 64 v ->
0 <= v < 2 ^ 63 -> 0 <= c < 2 ^ 32 ->
sv_denot Ev (SAlu ALU_ADD (SOff m 0) (SAlu ALU_SRL (SOff n c) (SLit 3))) = w64 (SB + (v + c) / 8).
Proof.
intros Ev n m v c Hm Hn Hv Hc. rewrite denot_lit_U. unfold w64. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom Ev m SB Hm) by (unfold SB; lia). rewrite (U_atom_off Ev n v c Hn) by lia. rewrite U_lit by lia.
change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
assert (0 <= (v + c) / 8 < 2 ^ 61) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
unfold zcanon, M64. rewrite (Z.mod_small ((v + c) / 8)) by lia. rewrite Z.mod_small by (unfold SB; lia). reflexivity.
Qed.
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
Hypothesis DRO : disco_ro_unowned B.
Hypothesis GM : globs_marked SEGS B disco_globs.
Hypothesis HV : img_shadow_vis SEGS B.
Hypothesis TJS : tj_strs.
Hypothesis tj_ro_kd_sep : VAL (A_OBJ 17) + 8 <= VAL (A_OBJ 1) /\ VAL (A_OBJ 17) + 8 <= VAL (A_OBJ 0) /\
VAL (A_OBJ 17) + 8 <= VAL (A_OBJ 66) /\ VAL (A_OBJ 17) + 8 <= VAL (A_OBJ 67).
Variables STK EV EVB : Z.
Variable IMG : world SEGS -> (word -> option byte) -> Prop.
Hypothesis HSTK : TJ_FRAME + SNPRINTF_STK <= STK.
Hypothesis HEVB : 0 <= EVB.
Hypothesis HEV : 8 * EVB <= EV.
Hypothesis FX : tj_fromX B STK EV IMG.
Hypothesis FC : tj_fromC B STK EV EVB IMG.
Hypothesis FL : tj_fromL B STK EV EVB IMG 0.
Theorem pb_tj_pre : tj_from0 B STK EV IMG ss_tj0 (INV_tj0 B 0).
Proof.
unfold tj_from0.
intros cx E k ly3 S3 W3 ms3 md3 HBASE HEX HJ HFR HINV HS.
destruct cx as [fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0].
unfold tj_baseX in HBASE. unfold tj_EX, tj_F, tj_FL in HEX. unfold INV_tj0 in HINV.
cbn [c_fq c_ly c_S c_W c_regs c_mem c_md c_ch c_t c_now c_buf c_cap c_Nb c_T c_fpos c_sp1 c_E0 tj_F tj_FL]
in HBASE, HEX, HINV, HJ, HFR, HS.
destruct HBASE as (HPRE & Hfrm0 & Hroom & HROD & HIM & H10 & H11 & H12 & H13 & Hnow & Hcap & Hobj & Harr & HlenT & Hok
& Hbuf & Hev & Hsp1b & HE0 & HE032 & HE02).
destruct HEX as (AG & E60 & E516 & E528 & E529 & HEI).
destruct HINV as (Hk0 & Hab).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity. assert (HSNP : SNPRINTF_STK = 11776) by reflexivity.
assert (HSK : 11776 + 640 <= STK) by (unfold TJ_FRAME in HSTK; lia).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
destruct (sp1_facts (spZ regs + -288) ltac:(clear - Hceil Hslo Hstk0 HSK C1; lia)
ltac:(rewrite <- Zplus_mod_idemp_l, Hal16; reflexivity)) as (Hsp1r & Hsp1al & Hsp1al16).
rewrite <- Hsp1b in Hsp1r, Hsp1al, Hsp1al16.
assert (Hsp1 : spZ regs - 304 <= sp1 <= spZ regs - 288) by (clear - Hsp1r; lia). clear Hsp1r.
pose (RUN := paj_run (fx := fq) B LAWS). pose (RUNTO := paj_run_to (fx := fq) B LAWS).
pose (BR := paj_branch (fx := fq) (PI := PI)).
pose (RUNP := SRr_run_pi_AJ (fx := fq) B LAWS). pose (RUNTOP := SRr_run_to_pi_AJ (fx := fq) B LAWS).
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
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (AG 2%nat ltac:(lia)); exact HE02).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
by (intros n r Hn; pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5;
rewrite (AG n ltac:(lia)); exact (HE0 n r Hn)).
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
assert (HF3 : frame_addr ly3 2 fpos = F) by (rewrite EFA; reflexivity).
assert (HF8lo : 512 <= F / 8) by (apply Z.div_le_lower_bound; lia).
assert (HF8hi : F / 8 <= 17592185044960) by (apply Z.div_le_upper_bound; lia).
fs_roF HS.
shok_auto SHOK (SOff 32 0) E (mrestrict (w_H W3) (ms_mem ms3)).
psrr_branch_tok RUN BR HS SHOK Bspan.
- hei_havoc HS; paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x621c. { awrFL_with ltac:(idtac; tj_hd AG HSK) AG fpos F EFA0. }
clear_frames.
pose proof HJ as (HARx & _).
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos HARx Hfin) as (_ & _ & _ & HFSx).
rewrite HF3 in HFSx. change (fs_frame_bytes 2 / 8) with 32 in HFSx.
fs_rwF HS E529 HFSx.
prreg HS (21%bv : bv 5) R21.
ra_join HS ss_tjX 640%nat ([1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 20; 21; 23; 24; 26; 27; 28; 29; 30; 31]%bv : list (bv 5)) idtac.
ra_join_val HS 640%nat 13%nat R21 E653.
lazymatch goal with |- SRr _ ?Wg (mkCfg ?msF ?mdF) _ =>
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
eapply (FX (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0) Ev k _ _ Wg msF mdF) end end.
+ unfold tj_baseX. cbn [c_fq c_ly c_S c_W c_regs c_mem c_md c_ch c_t c_now c_buf c_cap c_Nb c_T c_fpos c_sp1 c_E0].
repeat match goal with |- _ /\ _ => split end; try assumption; lia.
+ unfold tj_EX, tj_F, tj_FL. cbn [c_ly c_fpos c_E0 c_sp1]. fold F.
fold FLg.
split; [intros n Hn; rewrite ew_havoc_old by lia; exact (AG n Hn)|].
rewrite !ew_havoc_old by (cbn; lia).
split; [exact E60|]. split; [exact E516|]. split; [exact E528|]. split; [exact E529|].
apply img_env_havoc_hi; [assumption | unfold A_LIM; lia].
+ cbn [c_regs c_ly c_S c_W c_mem c_md c_fpos c_buf c_cap]. exact HJ.
+ cbn [c_S c_fpos]. exact HFR.
+ unfold INV_tjX. cbn [c_ly c_S c_cap c_T c_now c_buf].
split; [lia|]. split; [rewrite Hab; apply Permutation_refl|].
exists (-1). split; [rewrite E653; unfold w64; apply bv_eq; rewrite !Z_to_bv_unsigned; vm_compute; reflexivity|].
lazymatch goal with Hc : branch_taken _ _ _ = true |- _ =>
rewrite branch_ltu_U, (U_atom E 13 cap E13 ltac:(lia)), U_lit in Hc by lia; apply Z.ltb_lt in Hc end.
split; [intros _; reflexivity|]. split; [intros H3; lia|]. intros _ _; reflexivity.
+ cbn [c_fq]. exact HS.
- lazymatch goal with Hc : branch_taken _ _ _ = false |- _ =>
rewrite branch_ltu_U, (U_atom E 13 cap E13 ltac:(lia)), U_lit in Hc by lia; apply Z.ltb_ge in Hc; rename Hc into Hc3 end.
destruct (Hbuf Hc3) as (Hbin & Hbsz).
assert (Hbin3 : In (buf, Nb) (ablocks B ly3 S3)) by (rewrite Hab; exact Hbin).
hei_havoc HS; paj_run_tok RUN HS HJ SHOK Bspan. { awrFL_with ltac:(idtac; tj_hd AG HSK) AG fpos F EFA0. }
clear_frames.
prreg HS (2%bv : bv 5) Qsp. prreg HS (3%bv : bv 5) Qgp. prreg HS (4%bv : bv 5) Qtp. prreg HS (1%bv : bv 5) Qra.
prreg HS (10%bv : bv 5) Qa0. prreg HS (11%bv : bv 5) Qa1. prreg HS (12%bv : bv 5) Qa2.
pmkst HS.
rewrite HSNPC.
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
assert (HspX : sp1 - 11776 >= alloc_ceiling) by lia.
lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_sh_snprintf_at B LAWS Hsegs STK fq GC GV IMGLO IMGHI CR SNPC (ASNP fq) W3 (ms_regs msX) (ms_mem msX) (spZ regs) (tj_fp buf cap)
ly S W mem md [(2, fpos)] ly3 S3 _ k buf cap (VAL 280) [91] [PLit 91] [] (map (argZ (ms_regs msX)) [3; 4; 5; 6; 7] ++ [])
[] [91] cval (sp1 - spZ regs) _ _ HJ HRODc) end.
all: lazymatch goal with |- forall _ : YK11.FPState, _ => idtac | |- _ =>
first [ solve [ unfold spZ at 1; rewrite Hsp1e; lia ]
| solve [ rewrite <- Zminus_mod_idemp_l, Hsp1al16, <- Zminus_mod_idemp_r, Hal16; reflexivity ]
| solve [ rewrite ?HSNP; lia ]
| solve [ rewrite Qgp, E3; exact Hgp ] | solve [ rewrite Qtp, E4; exact Htp ]
| solve [ exact Qra ]
| solve [ apply ret_ok_codeptr_v; [lazymatch goal with |- _ <= ?kk < _ => try unfold kk end; lia | reflexivity] ]
| solve [ rewrite Qa0, E12; reflexivity ] | solve [ rewrite Qa1, E13; reflexivity ] | solve [ rewrite Qa2, E280; reflexivity ]
| solve [ exact (tj_snp_consts _ _ HRODc) ]
| solve [ eapply Forall_impl; [|exact tj_snp_cr]; intros r Hr; unfold IMG_LO, IMG_TOP in Hr; lia ]
| solve [ exact HG1 ] | solve [ exact HG2 ]
| solve [ reflexivity ] | solve [ repeat constructor ]
| solve [ split; [reflexivity | intros i Hi; cbn in Hi; lia] ]
| solve [ cbn; exact I ]
| solve [ exact Hfrm0 ]
| solve [ exact (tj_ro_fmt_rng 39 tj_s_open (proj1 TJS) ltac:(cbn; lia)) ]
| solve [ discriminate ]
| idtac ] end.
all: unfold snp_out.
all: lazymatch goal with
| |- forall _ : YK11.FPState, _ => idtac
| |- zdisjoint _ _ =>
eapply tj_dest_off_globals; [exact (proj1 tj_snp_img) | exact (proj2 tj_snp_img) | exact HARc | exact Hbin3 | lia | lia]
| |- Forall (fun r => Forall (zdisjoint r) _) _ =>
eapply Forall_impl; [|exact tj_snp_cr]; intros [lo0 n0] (H1 & H2 & H3); cbn [fst snd] in *;
apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold zdisjoint; cbn [fst snd]; unfold off_img, IMG_LO, IMG_TOP in *; rewrite ?HSNP; lia
| |- Forall (zdisjoint (_, 8)) _ =>
apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold zdisjoint; cbn [fst snd]; unfold off_img, IMG_LO, IMG_TOP in *; rewrite ?HSNP; lia
| |- fmt_at _ _ _ _ =>
assert (Hin2 : In (VAL 280, 2) disco_ro_ranges) by (unfold disco_ro_ranges; apply in_or_app; left; exact Hg39);
pose proof (disco_ro_unowned_at B (VAL 280) 2 DRO Hin2) as Hun;
unfold fmt_at; cbn [length Z.of_nat];
split; [lia|]; split;
[ intros i Hi;
rewrite (ro_bytes SEGS pa_relro_lo pa_relro_hi B _ (VAL 280) 2 (VAL 280 + i) HRODc (Hro39 (VAL 280 + i) ltac:(lia)) Hun ltac:(lia));
assert (Hi01 : i = 0 \/ i = 1) by lia; destruct Hi01 as [-> | ->];
[ pose proof (Hby39 0%nat ltac:(cbn; lia)) as Hb; cbn [Z.of_nat nth app] in Hb |- *; exact Hb
| pose proof (Hby39 1%nat ltac:(cbn; lia)) as Hb; cbn [Z.of_nat nth app] in Hb |- *; exact Hb ]
|];
split; [apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold zdisjoint; cbn [fst snd]; unfold off_img, IMG_LO, IMG_TOP in *; rewrite ?HSNP; lia|];
split; [unfold amem_range, kLowMemEnd; lia|];
apply (ro_read_ok_glob SEGS B disco_globs _ _ _ _ _ (VAL 280) 2 (VAL 280) 2 GM Hg39 HV HARc); unfold IMG_LO, IMG_TOP; lia
| |- _ + 8 * Z.of_nat (length []) <= 0 => cbn [length Z.of_nat]; lia
| |- Forall (zdisjoint (_, 8 * Z.of_nat (length []))) _ =>
cbn [length Z.of_nat]; apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold zdisjoint; cbn [fst snd]; rewrite ?HSNP; lia
| |- pairwise _ _ =>
cbn [pairwise]; split; [apply Forall_cons; [|apply Forall_nil] | split; [apply Forall_nil | exact I]]; unfold zdisjoint; cbn [fst snd]; rewrite ?HSNP; lia
| |- forall a, _ -> awr_byte _ _ _ _ _ _ _ _ /\ _ =>
intros a Ha; split; [|rewrite ?Hes; lia];
right; left; split;
[ unfold tj_fp; rewrite (proj2 (Z.ltb_ge cap 3) Hc3); exists (buf, buf + cap); split; [left; reflexivity | cbn [fst snd]; lia]
| exists buf, Nb; split; [exact Hbin3 | lia] ]
| |- amem_range _ _ =>
apply (amem_range_of_block8 SEGS B LAWS _ _ _ _ _ buf Nb _ _ HARc Hbin3); lia
| |- range_addressable _ _ _ _ =>
apply (block_shadow_range _ _ buf (req_size Nb) buf cap Hbsh); lia
| |- shadow_hull_vis _ _ _ =>
intros s0 Hs0; apply Hbhull; split; [lia|];
assert (shadow_addr (buf + cap - 1) / 8 <= shadow_addr (buf + req_size Nb - 1) / 8)
by (apply Z.div_le_mono; [lia|]; unfold shadow_addr; apply Z.add_le_mono_l; apply Z.div_le_mono; lia);
lia
end.
clear Qsp Qgp Qtp Qra Qa0 Qa1 Qa2 HJ SHOK.
intros fx' regs2 mem2 md2 Hf1 Hf2 HJ2 HP2 Ha0 Hwr Hnul Hfr Hpres2 Hsame.
assert (Hmin : Z.min (Z.of_nat (length [91])) (cap - 1) = 1) by (cbn [length Z.of_nat]; lia).
rewrite Hmin in Hwr, Hnul, Hfr.
assert (HBK : forall a, buf <= a < buf + 2 -> aview SEGS (w_H W3) mem2 a = aview SEGS (w_H W3) mem2 a) by (intros; reflexivity).
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
clear RUN RUNTO BR RUNP RUNTOP.
pose (RUN := paj_run (fx := fx') B LAWS). pose (RUNTO := paj_run_to (fx := fx') B LAWS).
pose (BR := paj_branch (fx := fx') (PI := PI)).
pose (RUNP := SRr_run_pi_AJ (fx := fx') B LAWS). pose (RUNTOP := SRr_run_to_pi_AJ (fx := fx') B LAWS).
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
pose proof (st_ok_pi_pin_reg' Ev ssx msx (10%bv : bv 5) 1 HS ltac:(cbn [ms_regs restrict mkst]; rewrite Ha0; reflexivity) ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
pose proof (tj_keep_journal B LAWS STK EV IMG (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0) _ _ _ _ _ _ _
ltac:(unfold tj_baseX; cbn [c_fq c_ly c_S c_W c_regs c_mem c_md c_ch c_t c_now c_buf c_cap c_Nb c_T c_fpos c_sp1 c_E0];
repeat match goal with |- _ /\ _ => split end; try assumption; lia) HJ2) as HK2.
unfold tj_keep in HK2. cbn [c_t c_T c_ly c_S] in HK2.
destruct HK2 as (HROD2 & HarrT2 & HobjT2).
pose proof HobjT2 as ((tcid & tpos & Htin & Htcid & Htal8 & Htflo & Htfhi) & Ht8 & HtRA).
set (u := disco_table_c.u_at T 384 4).
assert (Hu4 : val_mem SEGS (mrestrict (w_H W3) mem2) (t + 384) 4 u)
by (apply tj_garr8_u4; [exact HarrT2 | lia | rewrite HlenT; lia]).
assert (Hurange : 0 <= u < 2 ^ 32).
{ unfold u, disco_table_c.u_at. pose proof (bytes_le_to_Z_nonneg (disco_table_c.sub T 384 4)) as H0.
pose proof (bytes_le_to_Z_bound (disco_table_c.sub T 384 4)) as H1.
assert (Hlen : length (disco_table_c.sub T 384 4) = 4%nat) by (unfold disco_table_c.sub; rewrite length_firstn, length_skipn, HlenT; lia).
rewrite Hlen in H1. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in H1. lia. }
assert (HtF : In (tcid, tpos) (frames S3)) by (rewrite HFR; right; exact Htin).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ tcid tpos HARc HtF) as (Ht4096 & Htceil & Htapp).
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HARc HtF) as Htimg.
destruct (al_layout _ _ LAWS ly S W mem md ly3 HAR Hly3) as (_ & EFAt & _).
rewrite EFAt in Ht4096, Htceil, Htapp, Htimg.
destruct (in_split _ _ Htin) as (l2 & l3 & Hsplit).
pose proof (sep_frames_pos SEGS B LAWS _ _ _ _ _ (2, fpos) (tcid, tpos) [] l2 l3 HARc ltac:(rewrite HFR, Hsplit; reflexivity)) as HdFT.
unfold zdisjoint, frame_rng in HdFT. cbn [fst snd] in HdFT. rewrite !EFAt in HdFT. fold F in HdFT. change (fs_frame_bytes 2) with 256 in HdFT.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_havoc_hi 600 Ev ssv msv [Z_to_bv 64 u] HS ltac:(vm_compute; reflexivity)) as HS3; hei_pose Ev 600%nat [Z_to_bv 64 u] end.
clear HS. rename HS3 into HS. rebaseE HS AG HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (E600 : ew Ev 600 = Z_to_bv 64 u) by (rewrite HEv; exact (ew_havoc_new _ 600 [Z_to_bv 64 u] 0 (Z_to_bv 64 0) ltac:(cbn; lia)));
assert (E10v : ew Ev 10 = Z_to_bv 64 t) by (rewrite (AG 10%nat ltac:(lia)); rewrite (HE0 10%nat 10%bv eq_refl); exact H10) end.
clear HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 10%nat) 384 388 0 0 [YP09.mkChunk 384 (CVal 4 (SOff 600 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite E10v, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [intros o Ho; lia|];
apply Forall_cons; [|apply Forall_nil];
apply (chunk_ok_val SEGS Ev _ t 384 4 (SOff 600 0) u);
[cbn [sv_denot]; rewrite E600, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | zside | exact Hu4])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite E10v; evalE AG;
unfold off_img, in_app, IMG_LO, IMG_TOP, SB, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *;
repeat split; lia)) as HS3; clear HS; rename HS3 into HS end.
norm_ss HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_fact Ev _ _ 10 (mkAF 4096 140737479966720 3) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E10v, unsigned_lit_small by lia; change (2 ^ 3) with 8; lia)) as HS3;
clear HS; rename HS3 into HS end.
assert (Hshe : forall Ev m, range_addressable (aview SEGS (w_H W3) m) SHADOW_OFF t 400 ->
ew Ev 10 = Z_to_bv 64 t -> ew Ev 32 = Z_to_bv 64 SB ->
shent_ok SEGS (SOff 32 0) Ev (mrestrict (w_H W3) m) (mkSHE 10 0 400)).
{ intros Ev m HtRAm H10v H32v. unfold shent_ok, app_apart. cbn [she_m she_lo she_hi].
rewrite (U_atom Ev 32 SB H32v) by (unfold SB; lia). rewrite (U_atom Ev 10 t H10v) by lia.
rewrite <- (aview_rd_of SEGS). split; [rewrite Z.add_0_r; exact HtRAm|].
intros x Hx. unfold in_app, SB, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia. }
lazymatch type of HS with st_ok_pi _ _ ?Ex _ (restrict (w_H ?Wx) ?msx) =>
try clear SHOK;
assert (E32x : ew Ex 32 = Z_to_bv 64 SB) by (rewrite (AG 32%nat ltac:(lia)); exact HE032);
assert (E10x : ew Ex 10 = Z_to_bv 64 t) by (rewrite (AG 10%nat ltac:(lia)); rewrite (HE0 10%nat 10%bv eq_refl); exact H10);
shok_auto_with SHOK (SOff 32 0) Ex (mrestrict (w_H Wx) (ms_mem msx)) [mkSHE 10 0 400]
ltac:(idtac; cbn [ms_mem restrict mkst]; exact (Hshe Ex _ HtRA E10x E32x)) end.
hei_havoc HS; paj_run_tok RUN HS HJ2 SHOK Bspan. { awrFL_with ltac:(idtac; tj_hd AG HSK) AG fpos F EFA0. }
keep_buf HBK HFr AG. clear_frames.
psrr_branch_tok RUN BR HS SHOK Bspan.
+ exfalso. lazymatch goal with Hc : branch_taken _ (sv_denot ?Ev _) _ = true |- _ =>
rewrite branch_geu_U, U_lit, (U_atom Ev 13 cap ltac:(rewrite (AG 13%nat ltac:(lia)), (HE0 13%nat 13%bv eq_refl); exact H13) ltac:(lia)) in Hc by lia;
apply negb_true_iff, Z.ltb_ge in Hc end. lia.
+ hei_havoc HS; paj_run_tok RUN HS HJ2 SHOK Bspan. { awrFL_with ltac:(idtac; tj_hd AG HSK) AG fpos F EFA0. }
keep_buf HBK HFr AG. clear_frames.
assert (Hn08 : 0 <= disco_table_c.n_of T <= 8) by (destruct Hok as (HT1 & _); exact HT1).
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (E600c : ew Ev 600 = Z_to_bv 64 u) by (rewrite ?ew_havoc_old by lia; exact E600) end.
psrr_branch_tok RUN BR HS SHOK Bspan.
* lazymatch goal with Hc : branch_taken _ _ _ = true |- _ =>
rewrite (tj_bt_ge0 _ u (disco_table_c.n_of T) E600c Hurange eq_refl Hn08) in Hc; apply negb_true_iff, Z.ltb_ge in Hc; rename Hc into Hn0 end.
hei_havoc HS; paj_run_to_tok RUNTO HS HJ2 SHOK Bspan 0x61b0. { awrFL_with ltac:(idtac; tj_hd AG HSK) AG fpos F EFA0. }
keep_buf HBK HFr AG. clear_frames.
pose proof HJ2 as (HARy & _).
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos HARy Hfin) as (_ & _ & _ & HFSy).
rewrite HF3 in HFSy. change (fs_frame_bytes 2 / 8) with 32 in HFSy.
fs_rwF HS E529 HFSy.
prreg HS (26%bv : bv 5) Rs10.
ra_join HS ss_tjC 680%nat ([1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 19; 21; 23; 26; 27; 28; 29; 30; 31]%bv : list (bv 5))
ltac:(idtac; ra_join_fact HS 12%nat (mkAF 4096 140737479966720 4)
ltac:(rewrite ew_havoc_old by lia; rewrite (AG 12%nat ltac:(lia)), (HE0 12%nat 12%bv eq_refl), H12; unfold w64;
rewrite unsigned_lit_small by lia; change (2 ^ 4) with 16; lia)).
ra_join_val HS 680%nat 15%nat Rs10 E695.
lazymatch goal with |- SRr _ ?Wg (mkCfg ?msF ?mdF) _ =>
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
eapply (tj_from0_at_fx B STK EV IMG _ _ FC (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0) fx' Ev k _ _ Wg msF mdF Hf1 Hf2) end end.
-- unfold tj_baseX. cbn [c_fq c_ly c_S c_W c_regs c_mem c_md c_ch c_t c_now c_buf c_cap c_Nb c_T c_fpos c_sp1 c_E0].
repeat match goal with |- _ /\ _ => split end; try assumption; lia.
-- unfold tj_EX, tj_F, tj_FL. cbn [c_ly c_fpos c_E0 c_sp1]. fold F. fold FLg.
split; [intros n Hn; rewrite ew_havoc_old by lia; exact (AG n Hn)|].
rewrite !ew_havoc_old by (cbn; lia).
split; [exact E60|]. split; [exact E516|]. split; [exact E528|]. split; [exact E529|].
apply img_env_havoc_hi; [assumption | unfold A_LIM; lia].
-- cbn [c_regs c_ly c_S c_W c_mem c_md c_fpos c_buf c_cap]. exact HJ2.
-- cbn [c_S c_fpos]. exact HFR.
-- unfold INV_tjC. cbn [c_ly c_S c_cap c_T c_now c_buf].
split; [lia|]. split; [rewrite Hab; apply Permutation_refl|].
split; [exact (tj_keep_journal B LAWS STK EV IMG (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0) _ _ _ _ _ _ _
ltac:(unfold tj_baseX; cbn [c_fq c_ly c_S c_W c_regs c_mem c_md c_ch c_t c_now c_buf c_cap c_Nb c_T c_fpos c_sp1 c_E0];
repeat match goal with |- _ /\ _ => split end; try assumption; lia) HJ2)|].
split; [exact Hc3|].
exists [91]. split; [rewrite E695; reflexivity|]. split; [cbn; lia|]. split.
++ unfold reac_disco_table_json_c.tj_text, table_json_text, reac_disco_table_json_c.tj_entries.
replace (Z.to_nat (disco_table_c.n_of T)) with 0%nat by lia. reflexivity.
++ apply tj_garr8_of_aview. intros j Hj. cbn [length app] in Hj.
rewrite (HBK (buf + Z.of_nat j) ltac:(lia)).
assert (Hj01 : j = 0%nat \/ j = 1%nat) by lia. destruct Hj01 as [-> | ->].
** cbn [Z.of_nat]. pose proof (Hwr 0 ltac:(lia)) as Hw0. cbn [Z.to_nat nth] in Hw0. exact Hw0.
** cbn [Z.of_nat nth app]. exact Hnul.
-- cbn [c_fq]. exact HS.
* lazymatch goal with Hc : branch_taken _ _ _ = false |- _ =>
rewrite (tj_bt_ge0 _ u (disco_table_c.n_of T) E600c Hurange eq_refl Hn08) in Hc; apply negb_false_iff, Z.ltb_lt in Hc; rename Hc into Hn0 end.
pose proof HJ2 as (HARz & _).
pose proof (tj_keep_journal B LAWS STK EV IMG (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0) _ _ _ _ _ _ _
ltac:(unfold tj_baseX; cbn [c_fq c_ly c_S c_W c_regs c_mem c_md c_ch c_t c_now c_buf c_cap c_Nb c_T c_fpos c_sp1 c_E0];
repeat match goal with |- _ /\ _ => split end; try assumption; lia) HJ2) as HK3.
unfold tj_keep in HK3. cbn [c_t c_T c_ly c_S] in HK3. destruct HK3 as (HROD3 & _ & HobjT3).
pose proof HobjT3 as (_ & _ & HtRA3).
pose proof TJS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TJKD).
destruct TJKD as (Hkdin & Hkdro & Hkdby).
cbn [A_OBJ Nat.add] in Hkdin, Hkdro, Hkdby, tj_ro_kd_sep.
pose proof (pa_obj_img 17 ltac:(unfold disco_nobj; lia)) as Hob17. cbn [A_OBJ Nat.add] in Hob17. unfold IMG_LO, IMG_TOP in Hob17.
pose proof tj_ro_kd_sep as (Hks1 & Hks0 & Hks66 & Hks67).
assert (Hin17 : In (VAL 258, 8) disco_ro_ranges) by (unfold disco_ro_ranges; apply in_or_app; right; exact Hkdin).
pose proof (disco_ro_unowned_at B (VAL 258) 8 DRO Hin17) as Hun17.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ (restrict _ ?msx) =>
assert (E258 : ew Ev 258 = Z_to_bv 64 (VAL 258)) by (apply img_env_atomP; [assumption | unfold A_TEXT, A_LIM; lia]);
assert (HKD : val_mem SEGS (mrestrict (w_H W3) (ms_mem msx)) (VAL 258 + 0) 8 tj_KD);
[ rewrite Z.add_0_r; intros kk Hkk;
pose proof (ro_bytes SEGS pa_relro_lo pa_relro_hi B _ (VAL 258) 8 (VAL 258 + Z.of_nat kk) HROD3 (Hkdro (VAL 258 + Z.of_nat kk) ltac:(lia)) Hun17 ltac:(lia)) as Hr;
rewrite (Hkdby kk ltac:(cbn; lia)) in Hr;
destruct (aview_byte SEGS _ _ _ _ Hr) as (b & Hb & Hbv & _); rewrite Hb; f_equal; apply bv_eq; rewrite Z_to_bv_unsigned, <- Hbv;
do 8 (destruct kk as [|kk]; [vm_compute; reflexivity|]); lia
| ] end.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 258%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SLit tj_KD))]) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite E258, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [intros o Ho; lia|];
apply Forall_cons; [|apply Forall_nil];
apply (chunk_ok_val SEGS Ev _ (VAL 258) 0 8 (SLit tj_KD) tj_KD); [reflexivity | unfold tj_KD; cbn; lia | zside | exact HKD])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite E258; evalE AG; rewrite ?(pal_uar_cell B TL) in *;
unfold off_img, in_app, IMG_LO, IMG_TOP, SB, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *;
repeat split; lia)) as HS3; clear HS; rename HS3 into HS end.
norm_ss HS.
try match goal with H : sh_ok _ _ _ _ _ |- _ => clear H end.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ (restrict (w_H ?Wx) ?msx) =>
assert (E32y : ew Ex 32 = Z_to_bv 64 SB) by (rewrite (AG 32%nat ltac:(lia)); exact HE032);
assert (E10y : ew Ex 10 = Z_to_bv 64 t) by (rewrite (AG 10%nat ltac:(lia)); rewrite (HE0 10%nat 10%bv eq_refl); exact H10);
shok_auto_with SHOK (SOff 32 0) Ex (mrestrict (w_H Wx) (ms_mem msx)) [mkSHE 10 0 400]
ltac:(idtac; cbn [ms_mem restrict mkst]; first [exact (Hshe Ex _ HtRA3 E10y E32y) | shent_app_solve]) end.
hei_havoc HS; paj_run_to_tok RUNTO HS HJ2 SHOK Bspan 0x5cec. { awrFL_with ltac:(idtac; tj_hd AG HSK) AG fpos F EFA0. }
keep_buf HBK HFr AG. clear_frames.
pose proof HJ2 as (HARy & _).
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos HARy Hfin) as (_ & _ & _ & HFSy).
rewrite HF3 in HFSy. change (fs_frame_bytes 2 / 8) with 32 in HFSy.
fs_rwF HS E529 HFSy.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (E32z : ew Ev 32 = Z_to_bv 64 SB) by (rewrite (AG 32%nat ltac:(lia)); exact HE032);
assert (E10z : ew Ev 10 = Z_to_bv 64 t) by (rewrite (AG 10%nat ltac:(lia)); rewrite (HE0 10%nat 10%bv eq_refl); exact H10) end.
prreg_raw HS (5%bv : bv 5) Rt0. prreg_raw HS (6%bv : bv 5) Rt1. prreg_raw HS (7%bv : bv 5) Rt2.
prreg_raw HS (26%bv : bv 5) Rs10. prreg_raw HS (28%bv : bv 5) Rt3.
rewrite (tj_U_shadow _ 10 32 t 0 E32z E10z ltac:(lia) ltac:(lia)) in Rt2.
rewrite (tj_U_shadow _ 10 32 t 40 E32z E10z ltac:(lia) ltac:(lia)) in Rt3.
ra_join HS ss_tjL 720%nat ([1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 19; 26; 28; 29; 30; 31]%bv : list (bv 5))
ltac:(idtac; ra_join_fact HS 12%nat (mkAF 4096 140737479966720 4)
ltac:(rewrite ew_havoc_old by lia; rewrite (AG 12%nat ltac:(lia)), (HE0 12%nat 12%bv eq_refl), H12; unfold w64;
rewrite unsigned_lit_small by lia; change (2 ^ 4) with 16; lia)).
ra_join_val HS 720%nat 1%nat Rt0 E721. ra_join_val HS 720%nat 2%nat Rt1 E722. ra_join_val HS 720%nat 3%nat Rt2 E723.
ra_join_val HS 720%nat 13%nat Rs10 E733. ra_join_val HS 720%nat 14%nat Rt3 E734.
lazymatch goal with |- SRr _ ?Wg (mkCfg ?msF ?mdF) _ =>
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
eapply (tj_from0_at_fx B STK EV IMG _ _ FL (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0) fx' Ev k _ _ Wg msF mdF Hf1 Hf2) end end.
-- unfold tj_baseX. cbn [c_fq c_ly c_S c_W c_regs c_mem c_md c_ch c_t c_now c_buf c_cap c_Nb c_T c_fpos c_sp1 c_E0].
repeat match goal with |- _ /\ _ => split end; try assumption; lia.
-- unfold tj_EX, tj_F, tj_FL. cbn [c_ly c_fpos c_E0 c_sp1]. fold F. fold FLg.
split; [intros n Hn; rewrite ew_havoc_old by lia; exact (AG n Hn)|].
rewrite !ew_havoc_old by (cbn; lia).
split; [exact E60|]. split; [exact E516|]. split; [exact E528|]. split; [exact E529|].
apply img_env_havoc_hi; [assumption | unfold A_LIM; lia].
-- cbn [c_regs c_ly c_S c_W c_mem c_md c_fpos c_buf c_cap]. exact HJ2.
-- cbn [c_S c_fpos]. exact HFR.
-- unfold INV_tjL. cbn [c_ly c_S c_cap c_T c_now c_buf c_t].
split; [lia|]. split; [rewrite Hab; apply Permutation_refl|].
split; [exact (tj_keep_journal B LAWS STK EV IMG (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0) _ _ _ _ _ _ _
ltac:(unfold tj_baseX; cbn [c_fq c_ly c_S c_W c_regs c_mem c_md c_ch c_t c_now c_buf c_cap c_Nb c_T c_fpos c_sp1 c_E0];
repeat match goal with |- _ /\ _ => split end; try assumption; lia) HJ2)|].
split; [exact Hc3|]. split; [lia|].
split; [rewrite E721; reflexivity|]. split; [rewrite E722; reflexivity|].
split; [rewrite E723; replace (SB + t / 8 + 6 * 0) with (SB + (t + 0) / 8) by (rewrite Z.add_0_r; lia); reflexivity|].
split; [rewrite E734; replace (SB + (t + 40) / 8 + 6 * 0) with (SB + (t + 40) / 8) by lia; reflexivity|].
exists [91]. split; [rewrite E733; reflexivity|]. split; [cbn; lia|]. split.
++ exact (tj_lemmas.tj_rest_0 T now).
++ apply tj_garr8_of_aview. intros j Hj. cbn [length app] in Hj.
rewrite (HBK (buf + Z.of_nat j) ltac:(lia)).
assert (Hj01 : j = 0%nat \/ j = 1%nat) by lia. destruct Hj01 as [-> | ->].
** cbn [Z.of_nat]. pose proof (Hwr 0 ltac:(lia)) as Hw0. cbn [Z.to_nat nth] in Hw0. exact Hw0.
** cbn [Z.of_nat nth app]. exact Hnul.
-- cbn [c_fq]. exact HS.

Qed.
End h.
End f.
End d.
