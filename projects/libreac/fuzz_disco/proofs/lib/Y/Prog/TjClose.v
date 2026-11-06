(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/A/ACja.v for libreac/fuzz_grant's program walk, over fuzz_grant's listing. Image objects follow fuzz_grant.asan: the GOT word of the shadow-base cell is object 1 (atom 242), the GOT word of the side-stack flag is object 0 (atom 241), the shadow-base cell is object 32 (atom 273) and the side-stack flag cell is object 33 (atom 274), so img_factsF and img_hull_factsF give E240 E241 E242 E273 E274 and Hob241 Hob242 Hob273 Hob274, keptFL keeps those four regions, and aconstsF rewrites with PALib's pal_got_shadow, pal_cell and GrantFrame's palf_got_uar. awrFL, keptFL, fs_roF and fs_rwF keep the walks' atoms for the own side-stack frame (516), its shadow (529), the realigned stack (60) and the stack (2), for any frame class; stack bounds compute the walk's own STK constant; cgif's case for its 40-byte FRAME block (atom 11) is left out, and awrFL_with/keptFL_with take a tactic for a walk's own head regions. Module paths changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v of a working branch ca2ec2ecd18 and re-keyed to fuzz_ctrl.asan, whose shadow-base cell is object 30 (atom 271) and whose side-stack flag cell is object 31 (atom 272): img_factsF and img_hull_factsF now give E240 E241 E242 E271 E272 and Hob241 Hob242 Hob271 Hob272, and keptFL keeps the regions of atoms 241, 242, 271 and 272. The two GOT words (objects 0 and 1, atoms 241 and 242) are unchanged. Module paths and module names re-keyed to fuzz_ctrl. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/CtrlACja.v, with its module paths and module names changed; 342 of its 388 lines of code are new or changed and 285 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP0b YP0a.
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
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import SnShared SnprintfDef.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Rt Require Import SnprintfConsts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YRo.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import ReacDiscoTableJson TjBase TjCuts TjSnSh.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import PfFacts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require SnprintfDefR.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_json_text.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require tj_lemmas.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require disco_table_c reac_disco_table_json_c.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
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
Ltac tjc_hd AG HSK :=
lazymatch goal with
| |- awr_ok _ (YP09.mkRegion (Some 2%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ _ =>
eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat 0); [reflexivity | evalE AG | clear - HSK; cbn; lia | clear; cbn; lia |]
| |- awr_ok _ (YP09.mkRegion (Some 60%nat) _ _ _ _ _ :: _) _ ?sp0 _ _ _ _ _ =>
lazymatch goal with Hsp1 : sp0 - _ <= ?sp1 <= sp0 - _ |- _ =>
eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 60%nat (sp1 - sp0)); [reflexivity | evalE AG | clear - Hsp1 HSK; cbn; lia | clear - Hsp1; cbn; lia |] end
end.
Ltac tjc_fsb := repeat match goal with
| |- context [fs_frame_bytes ?c / 8] => let v := eval vm_compute in (fs_frame_bytes c / 8) in
lazymatch v with Zpos _ => change (fs_frame_bytes c / 8) with v end
| |- context [fs_frame_bytes ?c] => let v := eval vm_compute in (fs_frame_bytes c) in
lazymatch v with Zpos _ => change (fs_frame_bytes c) with v end
end.
Ltac tjc_awr_rec hd AG fpos F EFA :=
lazymatch goal with
| |- awr_ok _ [] _ _ _ _ _ _ _ => apply awr_ok_nil
| |- awr_ok _ (YP09.mkRegion _ _ _ ?wlo ?whi _ :: _) _ _ _ _ _ _ _ =>
first
[ lazymatch (eval vm_compute in (Z.leb whi wlo)) with true => apply awr_ok_cons_ro; [clear; cbn; lia|] end
| hd
| lazymatch goal with
| |- awr_ok _ (YP09.mkRegion (Some 529%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ ((?c, _) :: _) =>
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 529%nat); [reflexivity | evalE AG | | ];
[ cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; right; right; right; exists c, fpos; split; [left; reflexivity|]; right;
unfold in_zr, shadow_addr; cbn [fst snd]; rewrite <- SB_SHADOW_OFF; tjc_fsb; rewrite ?EFA; fold F; unfold SB; clear - Ha; lia
| ]
| |- awr_ok _ (YP09.mkRegion (Some 516%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ ((?c, _) :: _) =>
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 516%nat); [reflexivity | evalE AG | | ];
[ cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; right; right; right; exists c, fpos; split; [left; reflexivity|]; left;
unfold in_zr; cbn [fst snd]; tjc_fsb; rewrite ?EFA; fold F; clear - Ha; lia
| ]
end
| match goal with |- awr_ok _ (?r :: _) _ _ _ _ _ _ _ => idtac "AWR-HEAD" r end; fail 1 "tjc_awr: no rule for the head region" ];
tjc_awr_rec hd AG fpos F EFA
end.
Ltac tjc_awr hd AG fpos F EFA :=
lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end;
tjc_awr_rec hd AG fpos F EFA.
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
Context {RO : ro_below_ofl (@pa_segs _ lib_both3_0_listing PI) (@pa_relro_lo _ lib_both3_0_listing PI) (@pa_relro_hi _ lib_both3_0_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
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
Theorem pb_tj_close : tj_fromC B IMG.
Proof.
unfold tj_fromC, tj_from0.
intros cx E k ly3 S3 W3 ms3 md3 HBASE HEX HJ HFR HINV HS.
destruct cx as [fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0].
pose proof HBASE as HB0. pose proof HEX as HX0. unfold tj_baseX in HB0. unfold tj_EX, tj_F, tj_FL in HX0.
cbn [c_fq c_ly c_S c_W c_regs c_mem c_md c_ch c_t c_now c_buf c_cap c_Nb c_T c_fpos c_sp1 c_E0 tj_F tj_FL]
in HB0, HX0, HINV, HJ, HFR, HS.
pose proof HB0 as (HPRE & Hroom & HROD & HIM & H10 & H11 & H12 & H13 & Hnow & Hcap & Hobj & Harr & HlenT & Hok
& Hbuf & Hsp1b & HE0 & HE032 & HE033 & HE02 & Hfrm).
pose proof HX0 as (AG34 & E60 & E516 & E528 & E529 & HEI).
assert (AG : forall n, (n < 33)%nat -> ew E n = ew E0 n) by (intros n Hn; apply AG34; lia).
assert (E33 : ew E 33 = Z_to_bv 64 (as_uar_cell B)) by (rewrite (AG34 33%nat ltac:(lia)); exact HE033).
clear AG34.
unfold INV_tjC in HINV. cbn [c_cap c_T c_now c_buf] in HINV.
destruct HINV as (Hk0 & Hperm & HKEEP & Hcap3 & acc & E695 & Hacc & Htxt & Hgarr).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity. assert (HSNP : SNPRINTF_STK = 11776) by reflexivity.
assert (HSKe : REAC_DISCO_TABLE_JSON_STK = 640 + 11776) by (unfold REAC_DISCO_TABLE_JSON_STK; lia).
assert (HSK : 4736 <= REAC_DISCO_TABLE_JSON_STK) by lia.
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
img_hull_factsF.
unfold IMG_LO, IMG_TOP in Hob241, Hob242, Hob253, Huar.
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
assert (Hinb0 : In (buf, Nb) (ablocks B ly S)) by exact (proj1 (Hbuf Hcap3)).
assert (Hcapb : cap <= req_size Nb) by exact (proj2 (Hbuf Hcap3)).
assert (Hinb : In (buf, Nb) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hinb0]).
destruct (al_blocks _ _ LAWS _ _ _ _ _ buf Nb HAR3 Hinb) as (Hb16 & Hb4096 & Hbceil & Hbapp & _ & _ & HNb).
pose proof (blk_off_imgP _ _ _ _ _ _ buf Nb HAR3 Hinb) as Hbimg.
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ buf Nb 2 fpos HAR3 Hinb Hfin) as Hbsep.
rewrite EFA0 in Hbsep. fold F in Hbsep. change (fs_frame_bytes 2) with 256 in Hbsep. unfold zdisjoint in Hbsep. cbn [fst snd] in Hbsep.
unfold in_app, kLowShadowBeg, kHighMemBeg in Hbapp. unfold off_img, IMG_LO, IMG_TOP in Hbimg.
set (L := Z.of_nat (length acc)) in *.
unfold w64 in E695.
assert (UA : U E (SAlu ALU_ADD (SOff 12 0) (SOff 695 0)) = buf + L)
by (rewrite U_SAlu; cbn [zalu_raw]; rewrite (U_atom E 12 buf E12), (U_atom E 695 L E695) by lia; apply zcanon_id; unfold M64; lia).
assert (UX : U E (SAlu ALU_XOR (SLit 1) (SAlu ALU_SLTU (SAlu ALU_ADD (SOff 12 0) (SOff 695 0)) (SLit 1))) = 1).
{ rewrite U_SAlu, U_SLit, U_SAlu, UA, U_SLit. cbn [zalu_raw]. change (zcanon 1) with 1.
rewrite (proj2 (Z.ltb_ge (buf + L) 1)) by lia. reflexivity. }
pose (RUNP := SRr_run_pi_AJ (fx := fq) B LAWS). pose (RUNTOP := SRr_run_to_pi_AJ (fx := fq) B LAWS).
pose (RUNC := SRr_run_pi_AJ_call (fx := fq) B LAWS).

paj_run_shc RUNP RUNC HS HJ. { tjc_awr ltac:(idtac; tjc_hd AG HSK) AG fpos F EFA0. }
lazymatch type of HFr with frame_of _ _ (mrestrict _ ?m0) (mrestrict _ ?m1) =>
assert (HKa : forall a, buf <= a < buf + cap -> aview SEGS (w_H W3) m1 a = aview SEGS (w_H W3) m0 a)
by (intros a Ha; eapply aview_kept_out; [exact HFr | lia | notw AG]) end.
clear HF HFr HG.
psrr_branch_pi RUNP BR HS.
{ exfalso. rewrite branch_ltu_U, UA, (U_atom E 12 buf E12) in Hc by lia. apply Z.ltb_lt in Hc. lia. }
clear Hc.
paj_run_shc RUNP RUNC HS HJ. { tjc_awr ltac:(idtac; tjc_hd AG HSK) AG fpos F EFA0. }
lazymatch type of HFr with frame_of _ _ (mrestrict _ ?m0) (mrestrict _ ?m1) =>
assert (HKb : forall a, buf <= a < buf + cap -> aview SEGS (w_H W3) m1 a = aview SEGS (w_H W3) m0 a)
by (intros a Ha; eapply aview_kept_out; [exact HFr | lia | notw AG]) end.
clear HF HFr HG.
psrr_branch_pi RUNP BR HS.
{ exfalso. rewrite branch_eq_U, UX, U_SLit in Hc. vm_compute in Hc. discriminate Hc. }
clear Hc.
paj_run_shc RUNP RUNC HS HJ. { tjc_awr ltac:(idtac; tjc_hd AG HSK) AG fpos F EFA0. }
lazymatch type of HFr with frame_of _ _ (mrestrict _ ?m0) (mrestrict _ ?m1) =>
assert (HKc : forall a, buf <= a < buf + cap -> aview SEGS (w_H W3) m1 a = aview SEGS (w_H W3) m0 a)
by (intros a Ha; eapply aview_kept_out; [exact HFr | lia | notw AG]) end.
clear HF HFr HG.
lazymatch type of HKc with forall a, _ -> aview _ _ ?mC a = _ =>
lazymatch type of HKa with forall a, _ -> _ = aview _ _ ?mT a =>
assert (HK1 : forall a, buf <= a < buf + cap -> aview SEGS (w_H W3) mC a = aview SEGS (w_H W3) mT a)
by (intros a Ha; rewrite (HKc a Ha), (HKb a Ha), (HKa a Ha); reflexivity) end end.
clear HKa HKb HKc.
pose proof (proj1 HJ) as HARc.
pose proof (img_env_atomP E 296 HEI ltac:(unfold A_TEXT, A_LIM; lia)) as E296.
pose proof TJS as (_ & Hcl & _).
unfold tj_ro_at, tj_s_close in Hcl. change (A_OBJ 55) with 296%nat in Hcl. cbn [length Z.of_nat] in Hcl.
destruct Hcl as (Hg55 & Hro55 & Hlo55 & Hhi55 & _ & Hb55). unfold IMG_LO, IMG_TOP in Hlo55, Hhi55.
pose proof (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HROD) as HRODc.
destruct (tj_snp_canary _ _ _ _ _ HARc) as (cval & HG1 & HG2).
pose proof tj_snp_gcgv as (Hgc1 & Hgc2 & Hgv1 & Hgv2). unfold IMG_LO, IMG_TOP in Hgc1, Hgc2, Hgv1, Hgv2.
rregU HS (10%bv : bv 5) (buf + L) ltac:(exact UA) Ra0.
rregU HS (11%bv : bv 5) (cap - L) ltac:(rewrite U_SAlu; cbn [zalu_raw]; rewrite U_SMd; cbn [zmd_raw]; rewrite (U_atom E 13 cap E13), (U_atom E 695 L E695) by lia; rewrite U_SLit; apply tjc_sub; [reflexivity | lia | lia]) Ra1.
prreg HS (2%bv : bv 5) Qsp. prreg HS (3%bv : bv 5) Qgp. prreg HS (4%bv : bv 5) Qtp. prreg HS (1%bv : bv 5) Qra. prreg HS (12%bv : bv 5) Qa2.
destruct (ro_read_ok_glob SEGS B tfib_globs _ _ _ _ _ (VAL 296) _ (VAL 296) 2 GM Hg55 HV HARc ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold IMG_LO; lia) ltac:(unfold IMG_TOP; lia)) as [Hfra Hfrh].

pmkst HS. rewrite HSNPC.
lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_sh_snprintf_at B LAWS pa_segs_low REAC_DISCO_TABLE_JSON_STK fq GC GV IMGLO IMGHI CR SNPC (ASNP fq) W3 (ms_regs msX) (ms_mem msX) (spZ regs) (tj_fp buf cap) ly S W mem md [(2, fpos)] ly3 S3 _ k (buf + L) (cap - L) (VAL 296) [93] [PLit 93] [] (map (argZ (ms_regs msX)) [3; 4; 5; 6; 7] ++ []) [] [93] cval (sp1 - spZ regs) (Z_to_bv 64 (BASE + 25120)) _ HJ HRODc) end.
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
(tfib_ro_unowned_at B _ _ DRO ltac:(unfold tfib_ro_ranges; apply in_or_app; left; exact Hg55)) ltac:(lia)).
assert (Hi' : i = 0 \/ i = 1) by lia. destruct Hi' as [-> | ->].
* pose proof (Hb55 0%nat ltac:(cbn; lia)) as Hq. cbn [Z.of_nat nth app] in Hq. exact Hq.
* pose proof (Hb55 1%nat ltac:(cbn; lia)) as Hq. cbn [Z.of_nat nth app] in Hq. exact Hq.
+ split; [unfold snp_out; fa2 ltac:(unfold zdisjoint; cbn [fst snd]; lia)|].
split; [unfold amem_range; left; lia|]. split; assumption. }
{ exact (tj_ro_fmt_rng 55 tj_s_close (proj1 (proj2 TJS)) ltac:(cbv; lia)). }
{ discriminate. }
{ reflexivity. }
{ constructor; [exact I | constructor]. }
{ split; [reflexivity | intros i Hi; cbn in Hi; lia]. }
{ cbn. lia. }
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
{ exact Hfrm. }

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

paj_run_shc RUNP RUNC HS HJ2. { tjc_awr ltac:(idtac; tjc_hd AG HSK) AG fpos F EFA0. }
lazymatch type of HFr with frame_of _ _ (mrestrict _ ?m0) (mrestrict _ ?m1) =>
assert (HK2 : forall a, buf <= a < buf + cap -> aview SEGS (w_H W3) m1 a = aview SEGS (w_H W3) m0 a)
by (intros a Ha; eapply aview_kept_out; [exact HFr | lia | notw AG]) end.
clear HF HFr HG.

psrr_branch_pi RUNP BR HS.
{ exfalso. lazymatch type of Hc with branch_taken _ (sv_denot ?Ev ?a) (sv_denot _ ?b) = _ =>
rewrite (denot_lit_U Ev a), (denot_lit_U Ev b) in Hc end.
rewrite U0, U_SLit in Hc. vm_compute in Hc. discriminate Hc. }
clear Hc.
paj_run_shc RUNP RUNC HS HJ2. { tjc_awr ltac:(idtac; tjc_hd AG HSK) AG fpos F EFA0. }
lazymatch type of HFr with frame_of _ _ (mrestrict _ ?m0) (mrestrict _ ?m1) =>
assert (HK3 : forall a, buf <= a < buf + cap -> aview SEGS (w_H W3) m1 a = aview SEGS (w_H W3) m0 a)
by (intros a Ha; eapply aview_kept_out; [exact HFr | lia | notw AG]) end.
clear HF HFr HG.

psrr_branch_pi RUNP BR HS.
- rewrite branch_geu_U, U0, U4 in Hc. apply negb_true_iff, Z.ltb_ge in Hc.
paj_run_to_shc RUNTOP HS HJ2 0x6274. { tjc_awr ltac:(idtac; tjc_hd AG HSK) AG fpos F EFA0. }
prreg HS (23%bv : bv 5) R23.
ra_join HS ss_tjX 640%nat ([1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 20; 23; 21; 24; 26; 27; 28; 29; 30; 31]%bv : list (bv 5)) idtac.
ra_join_val HS 640%nat 13%nat R23 E653.
hei_havoc HS. rebaseE HS AG HEv. clear HEv.
lazymatch goal with |- SRr _ ?Wg (mkCfg ?msF ?mdF) _ =>
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
eapply (tj_from0_at_fx B IMG _ _ FX (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0) fx' Ev k ly3 S3 Wg msF mdF Hf1 Hf2) end end.
+ exact HBASE.
+ unfold tj_EX, tj_F, tj_FL. cbn [c_ly c_fpos c_E0 c_sp1]. fold F FLg.
split; [intros n Hn; destruct (Nat.eq_dec n 33) as [->|Hn33]; [rewrite E33; exact (eq_sym HE033) | apply AG; lia]|].
split; [exact E60|]. split; [exact E516|]. split; [exact E528|]. split; [exact E529 | assumption].
+ cbn [c_regs c_ly c_S c_W c_mem c_md c_fpos c_buf c_cap]. exact HJ2.
+ cbn [c_S c_fpos]. exact HFR.
+ unfold INV_tjX. cbn [c_cap c_T c_now c_buf c_ly c_S].
assert (Htl : tj_len T now = L + 1) by (unfold tj_len; rewrite Htxt, length_app; cbn [length]; unfold L; lia).
split; [lia|]. split; [exact Hperm|]. exists (-1). split.
{ rewrite E653. apply bv_eq. unfold w64. rewrite !Z_to_bv_unsigned. vm_compute. reflexivity. }
split; [intros; lia|]. split; [intros _ Hlt; exfalso; lia | intros _ _; reflexivity].
+ exact HS.
- rewrite branch_geu_U, U0, U4 in Hc. apply negb_false_iff, Z.ltb_lt in Hc.
paj_run_to_shc RUNTOP HS HJ2 0x6274. { tjc_awr ltac:(idtac; tjc_hd AG HSK) AG fpos F EFA0. }
lazymatch type of HFr with frame_of _ _ (mrestrict _ ?m0) (mrestrict _ ?m1) =>
assert (HK4 : forall a, buf <= a < buf + cap -> aview SEGS (w_H W3) m1 a = aview SEGS (w_H W3) m0 a)
by (intros a Ha; eapply aview_kept_out; [exact HFr | lia | notw AG]) end.
clear HF HFr HG.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (Uw : U Ev (SAluw ALU_ADD (SOff 705 0) (SOff 695 0)) = 1 + L)
by (rewrite U_of_S, S_SAluw; cbn [zalu_raw]; rewrite U0, (U_atom Ev 695 L E695) by lia;
rewrite (Z.mod_small 1 (2 ^ 32)), (Z.mod_small L (2 ^ 32)) by lia; rewrite swrap32_id by lia;
unfold bv_wrap; change (bv_modulus 64) with (2 ^ 64); apply Z.mod_small; lia) end.
rregU HS (23%bv : bv 5) (1 + L) ltac:(exact Uw) R23.
ra_join HS ss_tjX 640%nat ([1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 20; 23; 21; 24; 26; 27; 28; 29; 30; 31]%bv : list (bv 5)) idtac.
ra_join_val HS 640%nat 13%nat R23 E653.
hei_havoc HS. rebaseE HS AG HEv. clear HEv.
lazymatch goal with |- SRr _ ?Wg (mkCfg ?msF ?mdF) _ =>
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
eapply (tj_from0_at_fx B IMG _ _ FX (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0) fx' Ev k ly3 S3 Wg msF mdF Hf1 Hf2) end end.
+ exact HBASE.
+ unfold tj_EX, tj_F, tj_FL. cbn [c_ly c_fpos c_E0 c_sp1]. fold F FLg.
split; [intros n Hn; destruct (Nat.eq_dec n 33) as [->|Hn33]; [rewrite E33; exact (eq_sym HE033) | apply AG; lia]|].
split; [exact E60|]. split; [exact E516|]. split; [exact E528|]. split; [exact E529 | assumption].
+ cbn [c_regs c_ly c_S c_W c_mem c_md c_fpos c_buf c_cap]. exact HJ2.
+ cbn [c_S c_fpos]. exact HFR.
+ unfold INV_tjX. cbn [c_cap c_T c_now c_buf c_ly c_S].
assert (Htl : tj_len T now = L + 1) by (unfold tj_len; rewrite Htxt, length_app; cbn [length]; unfold L; lia).
split; [lia|]. split; [exact Hperm|]. exists (1 + L). split; [exact E653|].
split; [intros; lia|]. split; [|intros _ Hge; exfalso; lia].
intros _ _. split; [lia|].
rewrite Htxt, <- app_assoc. cbn [app].
apply (garr8_aview_kept SEGS (w_H W3) (w_H W3) mem2 _ buf).
{ intros a Ha. rewrite length_app in Ha. cbn [length] in Ha. rewrite HK4, HK3 by (unfold L in *; lia). apply HK2. unfold L in *; lia. }
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
