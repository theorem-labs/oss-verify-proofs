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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI01 YI06.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YCcz.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI1i YI20.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YF9i YCeb YCe8 YCfq YCdy YCfr YCe9 YCgl YCfu YCft YCrb YCez YCev YCf6 YCf2.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Ltac fl_prelude :=
let LAWS := rnLAWS in let TL := rnTL in let B := lazymatch goal with L : AR_laws trbsegs ?Bv |- _ => Bv end in
let cx := fresh "cx" in
intros cx E k ly3 S3 W3 ms3 md3 HBASE HEE HJ3 Hfrs3 HINV HS;
destruct cx as [ly S W regs mem md ch g s N i f rest fpos sp1 E0];
pose proof HBASE as HBASE0;
unfold fl_base in HBASE; unfold fl_E in HEE; red in HINV; unfold fl_F, fl_FL, fl_FP in HBASE, HEE, HJ3, HINV;
cbn [c_ly c_S c_W c_regs c_mem c_md c_ch c_g c_s c_N c_i c_f c_rest c_fpos c_sp1 c_E0] in HBASE, HEE, HJ3, Hfrs3, HINV;
destruct HBASE as (HPRE & Hctx & Hroom & Htop32 & HROD & H10 & HAT & HWF & Hi & Hf & H11 & H12 & HPerm & Hev & Hlive & Esp1 & EE & EX & Usp);
destruct HEE as (AG & EXE & E70 & RF & E87 & E88);
pose proof Hwx_tfa as Hwx; pose proof trb_segs_low as Hsegs;
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT);
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2);
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5); assert (FFS : TFLUSH_STK = 17440) by reflexivity;
assert (HEV : EV_FLUSH = 35) by reflexivity; assert (Hes : ESTACK = 4096) by reflexivity;
assert (E10 : ew E0 10 = Z_to_bv 64 g) by (rewrite (EE 10%nat 10%bv eq_refl); exact H10);
assert (E11 : ew E0 11 = Z_to_bv 64 (fr_ptr f)) by (rewrite (EE 11%nat 11%bv eq_refl); exact H11);
assert (E12 : ew E0 12 = Z_to_bv 64 (frame_ptr (nth (i - 1) (cg_frames s) None))) by (rewrite (EE 12%nat 12%bv eq_refl); exact H12);
assert (E2 : ew E0 2 = getr regs 2) by (exact (EE 2%nat 2%bv eq_refl));
pose proof (EX 0%nat ltac:(lia)) as E32; cbn [Nat.add nth fl_extra map] in E32;
pose proof (EXE 1%nat ltac:(lia)) as E33; pose proof (EXE 2%nat ltac:(lia)) as E34; pose proof (EXE 3%nat ltac:(lia)) as E35;
pose proof (EXE 4%nat ltac:(lia)) as E36; pose proof (EXE 5%nat ltac:(lia)) as E37; pose proof (EXE 6%nat ltac:(lia)) as E38;
pose proof (EXE 7%nat ltac:(lia)) as E39; pose proof (EXE 8%nat ltac:(lia)) as E40; pose proof (EXE 9%nat ltac:(lia)) as E41;
pose proof (EXE 10%nat ltac:(lia)) as E42; pose proof (EXE 11%nat ltac:(lia)) as E43; pose proof (EXE 12%nat ltac:(lia)) as E44;
pose proof (EXE 13%nat ltac:(lia)) as E45; pose proof (EXE 14%nat ltac:(lia)) as E46; pose proof (EXE 15%nat ltac:(lia)) as E47;
pose proof (EXE 16%nat ltac:(lia)) as E48; pose proof (EXE 17%nat ltac:(lia)) as E49; pose proof (EXE 18%nat ltac:(lia)) as E50;
pose proof (EXE 19%nat ltac:(lia)) as E51; pose proof (EXE 20%nat ltac:(lia)) as E52; pose proof (EXE 21%nat ltac:(lia)) as E53;
pose proof (EXE 22%nat ltac:(lia)) as E54; pose proof (EXE 23%nat ltac:(lia)) as E55; pose proof (EXE 24%nat ltac:(lia)) as E56;
pose proof (EXE 25%nat ltac:(lia)) as E57; pose proof (EXE 26%nat ltac:(lia)) as E58;
cbn [Nat.add nth fl_extra map app tcgif_vals frame_vals] in E33, E34, E35, E36, E37, E38, E39, E40, E41, E42, E43, E44, E45, E46, E47, E48, E49, E50, E51, E52, E53, E54, E55, E56, E57, E58;
let Og' := fresh "Og'" in let Oc' := fresh "Oc'" in
pose proof HAT as HAT'; destruct HAT' as (Og & Oraw & Ofr);
assert (Hfi : In (Some f) (cg_frames s)) by (eapply nth_error_In; exact Hf);
pose proof (Ofr f Hfi) as Oc;
pose proof Og as Og'; cbn [obj_at LAY_CGIF tcgif_vals] in Og';
destruct Og' as ([_ R0] & [_ R1] & [_ R2] & [_ R3] & [_ R4] & [_ R5] & [_ R6] & [_ R7] & [_ R8] & [_ R9] & [_ R10] & [_ R11] & [_ R12] & [_ R13] & [_ R14] & [_ R15] & [_ R16] & _);
cbn [fst snd N.to_nat Z.of_N] in R0, R1, R2, R3, R4, R5, R6, R7, R8, R9, R10, R11, R12, R13, R14, R15, R16;
pose proof Oc as Oc'; cbn [obj_at LAY_Frame LAY_FrameConfig frame_vals app] in Oc';
destruct Oc' as ([_ Q0] & [_ Q1] & [_ Q2] & [_ Q3] & [_ Q4] & [_ Q5] & [_ Q6] & [_ Q7] & [_ Q8] & _);
cbn [fst snd N.to_nat Z.of_N] in Q0, Q1, Q2, Q3, Q4, Q5, Q6, Q7, Q8;
change (2 ^ (8 * 8)) with (2 ^ 64) in *; change (2 ^ (8 * 4)) with (2 ^ 32) in *; change (2 ^ (8 * 2)) with 65536 in *; change (2 ^ (8 * 1)) with 256 in *;
pose proof HWF as HWF'; destruct HWF' as (Hlen3 & HW1 & HH1 & HN & HNle & Hngp & Hih & Hfwf);
destruct (fl_blocks_in B ly S g s N i f rest HPerm Hf) as (Hing & Hraw_in & Hcur_in & Himg_in);
destruct (fl_cblocks_in g s N i f Hf) as (Hg_blk & Hraw_blk & Hcur_blk & Himg_blk);
destruct (al_blocks _ _ LAWS ly S W mem md g CGIF_SIZE HAR Hing) as (Hg16 & Hg4096 & Hgceil & Hgh_ia & Hgpres & _); pose proof (proj1 Hgh_ia) as Hgh;
pose proof (blk_off_img _ _ _ _ _ _ g CGIF_SIZE HAR Hing) as Hgh_img;
destruct (al_blocks _ _ LAWS ly S W mem md (fr_ptr f) FRAME_SIZE HAR Hcur_in) as (Hc16 & Hc4096 & Hcceil & Hcrh_ia & Hcpres & _); pose proof (proj1 Hcrh_ia) as Hcrh;
pose proof (blk_off_img _ _ _ _ _ _ _ _ HAR Hcur_in) as Hcrh_img;
destruct (al_blocks _ _ LAWS ly S W mem md (fr_img f) N HAR Himg_in) as (Hi16 & Hi4096 & Hiceil & Hirh_ia & _ & _); pose proof (proj1 Hirh_ia) as Hirh;
pose proof (blk_off_img _ _ _ _ _ _ _ _ HAR Himg_in) as Hirh_img;
destruct (al_blocks _ _ LAWS ly S W mem md (cg_raw s) RAW_SIZE HAR Hraw_in) as (Hr16 & Hr4096 & Hrceil & Hrh_ia & _ & _); pose proof (proj1 Hrh_ia) as Hrh;
pose proof (blk_off_img _ _ _ _ _ _ _ _ HAR Hraw_in) as Hrh_img;
change (req_size CGIF_SIZE) with 96 in *; change (req_size RAW_SIZE) with 48 in *; change (req_size FRAME_SIZE) with 40 in *;
pose proof (proj1 HJ3) as HAR3;
destruct (al_layout _ _ LAWS _ _ _ _ _ ly3 HAR (proj1 (proj2 HJ3))) as (_ & EFA3 & _);
assert (EFL3 : forall c p, flag_addr ly3 c p = flag_addr ly c p) by (intros c p; unfold flag_addr; pose proof (EFA3 c p) as X; unfold frame_addr in X; lia);
assert (Hfin3 : In (1, fpos) (frames S3)) by (rewrite Hfrs3; left; reflexivity);
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR3 Hfin3) as (HFal & [HFhi _] & HFpres3 & HFSpres3);
pose proof (frm_off_img _ _ _ _ _ _ _ _ HAR3 Hfin3) as HFapp_img;
destruct (frames_bounds trbsegs _ LAWS _ _ _ _ _ 1 fpos HAR3 Hfin3) as (HF4096 & HFceil & HFhigh);
pose proof (frm_off_img _ _ _ _ _ _ _ _ HAR3 Hfin3) as HFhigh_img;
change (fs_frame_bytes 1) with 128 in *; change (128 / 8) with 16 in HFSpres3; rewrite !EFA3 in *;
set (F := frame_addr ly 1 fpos) in *; set (FL := flag_addr ly 1 fpos) in *;
assert (HFq : F = 32 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(lia)); lia);
assert (HF8 : F / 8 = 4 * (F / 32)) by (rewrite HFq at 1; replace (32 * (F / 32)) with (4 * (F / 32) * 8) by lia; rewrite Z.div_mul by lia; reflexivity);
assert (HF8lo : 512 <= F / 8) by (apply Z.div_le_lower_bound; lia)    ;
assert (HF8hi : F / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia);
let Hsp1r := fresh "Hsp1r" in
destruct (sp1_facts (spZ regs + -352) ltac:(clear - Hceil Hslo Hstk0 FFS C1; lia) ltac:(rewrite <- Zplus_mod_idemp_l, Hal16; reflexivity)) as (Hsp1r & Hsp1al & Hsp1al16);
rewrite <- Esp1 in Hsp1r, Hsp1al, Hsp1al16;
assert (Hsp1 : spZ regs - 368 <= sp1 <= spZ regs - 352) by (clear - Hsp1r; lia); clear Hsp1r;
assert (HUP : forall a, spZ regs <= a < 2 ^ 64 -> aview trbsegs (w_H W3) (ms_mem ms3) a = aview trbsegs (w_H W) mem a)
by (let a := fresh "a" in let Ha := fresh "Ha" in let F1 := fresh "F1" in intros a Ha;
pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _); apply F1; clear - Ha Hceil Hslo Hstk0 FFS C1; lia);
let Kgot3 := fresh "Kgot3" in let Kcell3 := fresh "Kcell3" in let Kguar3 := fresh "Kguar3" in let Kuar3 := fresh "Kuar3" in
aconstsF HJ3 Kgot3 Kcell3 Kguar3 Kuar3.
Ltac fl_blocks3 Hing3 Hcur3 :=
let LAWS := rnLAWS in
lazymatch goal with HAR3 : AR trbsegs ?B ?ly3 ?S3 ?W3 ?m3 ?md3 |- _ =>
lazymatch type of Hing3 with In (?g, _) _ => lazymatch type of Hcur3 with In (?cur, _) _ =>
lazymatch goal with Hfin3 : In (1, ?fpos) (frames S3), EFA3 : forall c p, frame_addr ly3 c p = _ |- _ =>
destruct (al_blocks _ _ LAWS _ _ _ _ _ g CGIF_SIZE HAR3 Hing3) as (_ & _ & _ & _ & Hgpres3 & _);
change (req_size CGIF_SIZE) with 96 in Hgpres3;
destruct (al_blocks _ _ LAWS _ _ _ _ _ cur FRAME_SIZE HAR3 Hcur3) as (_ & _ & _ & _ & Hcpres3 & _);
change (req_size FRAME_SIZE) with 40 in Hcpres3;
pose proof (sep_block_frame trbsegs _ LAWS ly3 S3 _ _ _ g CGIF_SIZE 1 fpos HAR3 Hing3 Hfin3) as HdFG;
unfold zdisjoint in HdFG; cbn [fst snd] in HdFG; change (req_size CGIF_SIZE) with 96 in HdFG; change (fs_frame_bytes 1) with 128 in HdFG; rewrite EFA3 in HdFG;
pose proof (sep_block_frame trbsegs _ LAWS ly3 S3 _ _ _ cur FRAME_SIZE 1 fpos HAR3 Hcur3 Hfin3) as HdFC;
unfold zdisjoint in HdFC; cbn [fst snd] in HdFC; change (req_size FRAME_SIZE) with 40 in HdFC; change (fs_frame_bytes 1) with 128 in HdFC; rewrite EFA3 in HdFC;
pose proof (sep_blocks trbsegs _ LAWS ly3 S3 _ _ _ g CGIF_SIZE cur FRAME_SIZE HAR3 Hing3 Hcur3 ltac:(unfold CGIF_SIZE, FRAME_SIZE; intros X; injection X; lia)) as HdGC;
unfold zdisjoint in HdGC; cbn [fst snd] in HdGC; change (req_size FRAME_SIZE) with 40 in HdGC; change (req_size CGIF_SIZE) with 96 in HdGC;
box HdFG; box HdFC; box HdGC
end end end end.
Ltac fl_hand RC HS :=
lazymatch goal with |- SRr _ ?W3 (mkCfg ?ms3 ?md3) (fl_post ?B ?cxv) =>
lazymatch type of HS with st_ok _ ?Ev _ _ =>
eapply (RC cxv Ev _ _ _ W3 ms3 md3);
[ lazymatch goal with H0 : fl_base _ _ |- _ => exact H0 end
| repeat (lazymatch goal with |- fl_E _ (havoc _ _ _) => apply fl_E_havoc; [clear; cbn; lia|] end);
unfold fl_E, fl_F, fl_FL; cbn [c_ly c_fpos c_E0 c_s c_f c_sp1];
split; [assumption|];
split; [let j := fresh "j" in let Hj := fresh "Hj" in intros j Hj; cbn [nth fl_extra map app tcgif_vals frame_vals];
do 27 (try (destruct j as [|j]; [first [assumption | lia] |])); lia|];
repeat (split; [eassumption|]); eassumption
| first [eassumption | idtac]
| first [eassumption | idtac]
| red; cbn [c_ly c_S c_W c_regs c_mem c_md c_ch c_g c_s c_N c_i c_f c_rest c_fpos c_sp1 c_E0]
| exact HS ] end end.
Ltac relowF HS AG E10 E11 E32 E10n E11n E32n :=
try clear E10n; try clear E11n; try clear E32n;
lazymatch type of HS with st_ok _ ?Ev _ _ =>
lazymatch type of E10 with _ = ?v => assert (E10n : ew Ev 10 = v) by (rewrite (AG 10%nat) by lia; exact E10) end;
lazymatch type of E11 with _ = ?v => assert (E11n : ew Ev 11 = v) by (rewrite (AG 11%nat) by lia; exact E11) end;
lazymatch type of E32 with _ = ?v => assert (E32n : ew Ev 32 = v) by (rewrite (AG 32%nat) by lia; exact E32) end end.
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.

End b.
