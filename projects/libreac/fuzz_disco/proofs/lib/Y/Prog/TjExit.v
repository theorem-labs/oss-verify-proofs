(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the contract and walk of reac_ctrl_checksum_verify on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/AC8h.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlChecksumVerify.v, with its module paths and numbers changed; 66 of its 271 lines of code are new or changed and 57 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/CtrlChecksumVerify.v, with its module paths and module names changed; 145 of its 182 lines of code are new or changed and 234 lines of the source are left out. *)
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
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YCkd.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP0d YP0c YP07 YI0w YI0z YI12 YC4a YC8i.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC80 YC1f YC1g YC1h YC81 YC4b YC44 YC45 YC85 YC88.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC8g YC1i.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YCjr YCj1 YCja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import SnprintfDef.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import ReacDiscoTableJson TjBase TjCuts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require disco_table_c reac_disco_table_json_c.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Ltac tjx_split H :=
lazymatch type of H with
| _ /\ _ => let H1 := fresh "HB" in destruct H as [H1 H]; tjx_split H
| _ => idtac
end.
Ltac tjx_fl_disj HnoF HFLown :=
lazymatch goal with |- ?fl + 1 <= ?x + ?l \/ ?x + ?h <= ?fl + 0 =>
destruct (Z_lt_ge_dec fl (x + l)); [left; lia|];
destruct (Z_lt_ge_dec fl (x + h)); [exfalso; apply (HnoF fl); [lia | exact HFLown] | right; lia]
end.
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Variable IMG : world SEGS -> (word -> option byte) -> Prop.
Theorem pb_tj_exit : tj_fromX B IMG.
Proof.
unfold tj_fromX, tj_from0.
intros cx E k ly3 S3 W3 ms3 md3 HB HEX HJ3 Hfrs3 HINV HS.
destruct cx as [fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0].
unfold tj_baseX, tj_EX, INV_tjX, tj_postX, tj_F, tj_FL in *.
cbn [c_fq c_ly c_S c_W c_regs c_mem c_md c_ch c_t c_now c_buf c_cap c_Nb c_T c_fpos c_sp1 c_E0] in *.
tjx_split HB.
lazymatch goal with X : afn_pre _ _ _ _ _ _ _ _ _ _ |- _ => rename X into HPRE end.
lazymatch goal with X : 3 <= cap -> In (buf, Nb) _ /\ _ |- _ => rename X into Hbuf end.
lazymatch goal with X : sp1 = 32 * _ |- _ => rename X into Esp1 end.
lazymatch goal with X : forall (n : nat) (r : bv 5), _ -> ew E0 n = getr regs r |- _ => rename X into EE end.
lazymatch goal with X : bv_unsigned (ew E0 2) = spZ regs |- _ => rename X into Usp end.
destruct HEX as (AG & E60 & E516 & E528 & E529 & HEI).
destruct HINV as (Hk & HPerm3 & r & E653 & Hr1 & Hr2 & Hr3).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5). assert (Hes : ESTACK = 4096) by reflexivity.
assert (HSK : 4736 <= REAC_DISCO_TABLE_JSON_STK)
by (assert (HSNP : SNPRINTF_STK = 11776) by reflexivity; unfold REAC_DISCO_TABLE_JSON_STK; lia).
destruct (sp1_facts (spZ regs + -288) ltac:(clear - Hceil Hslo Hstk0 HSK C1; lia)
ltac:(rewrite <- Zplus_mod_idemp_l, Hal16; reflexivity)) as (Hsp1r & _ & _).
rewrite <- Esp1 in Hsp1r.
assert (Hsp1 : spZ regs - 304 <= sp1 <= spZ regs - 288) by (clear - Hsp1r; lia). clear Hsp1r.
pose proof (proj1 HJ3) as HAR3.
destruct (al_layout _ _ LAWS _ _ _ _ _ ly3 HAR (proj1 (proj2 HJ3))) as (_ & EFA3 & _).
assert (EFL3 : forall c p, flag_addr ly3 c p = flag_addr ly c p)
by (intros c p; unfold flag_addr; pose proof (EFA3 c p) as X; unfold frame_addr in X; lia).
assert (Hfin3 : In (2, fpos) (frames S3)) by (rewrite Hfrs3; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos HAR3 Hfin3) as (HFal & _ & HFpres3 & _).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 2 fpos HAR3 Hfin3) as (HF4096 & HFceil & _).
destruct (FFL ly3 S3 W3 (ms_mem ms3) md3 2 fpos HAR3 Hfin3) as (HFLpres & HFLown & HFLrng).
change (fs_frame_bytes 2) with 256 in HFpres3, HFceil.
rewrite EFA3 in HFal, HFpres3, HF4096, HFceil. rewrite EFL3 in HFLpres, HFLown, HFLrng.
set (F := frame_addr ly 2 fpos) in *. set (FL := flag_addr ly 2 fpos) in *.
destruct HFLrng as ((_ & _) & (HFL4096 & (HFLimg & HFLband) & HFLceil)).
unfold off_img, IMG_LO, IMG_TOP in HFLimg.
assert (HFq : F = 32 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(lia)); lia).
assert (HF8 : F / 8 = 4 * (F / 32))
by (rewrite HFq at 1; replace (32 * (F / 32)) with (4 * (F / 32) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
assert (HF8lo : 512 <= F / 8) by (clear - HFq HF8 HF4096; lia).
assert (HF8hi : F / 8 <= 17592184995808) by (clear - HFq HF8 HFceil C1; lia).
assert (HnoF : forall a, F <= a < F + 256 -> ~ aowned B ly3 S3 a) by (intros a Ha; exact (proj2 (HFpres3 a Ha))).
img_factsF E.
pose proof (pa_obj_img 0 ltac:(lia)) as Hob241. pose proof (pa_obj_img 1 ltac:(lia)) as Hob242.
pose proof (pa_obj_img 12 ltac:(lia)) as Hob253.
cbv [A_OBJ Nat.add] in Hob241, Hob242, Hob253.
unfold IMG_LO, IMG_TOP in Hob241, Hob242, Hob253.
norm_ss HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
let rs := eval vm_compute in (firstn 7 (ss_mem ssx)) in
pose proof (st_ok_pi_submem Ev ssx msx rs HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS0 end.
clear HS. rename HS0 into HS. norm_ss HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 528%nat) 0 1 0 1 []) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite E528, unsigned_lit_small by (clear - HFL4096 HFLceil C1; lia);
split; [lia|]; split; [clear - HFLceil C1; lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable SEGS); replace (FL + o) with FL by lia; exact HFLpres)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
evalE AG;
clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 HSK C1 HF4096 HFceil HF8lo HF8hi HFL4096 HFLceil HFLband HFLimg
Hob241 Hob242 Hob253 HnoF HFLown;
repeat split; first [lia | tjx_fl_disj HnoF HFLown])) as HS1 end.
clear HS. rename HS1 into HS. norm_ss HS.
pose (RUNF := aj_flag_store_pi (fx := fq) B LAWS ML ASF FFL).
paj_run_flag_sh RUNF HS HJ3.
- lia.
- intros a (rg & Hin & Hrg).
lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In rg rs') in Hin end.
cbn [In] in Hin.
repeat (destruct Hin as [<- | Hin];
[ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrg; revert Hrg; evalE AG; intros Hrg;
first
[ exfalso; clear - Hrg; lia
| right; rewrite EFL3; fold FL; clear - Hrg; lia
| left; left; clear - Hrg Hsp1 HSK; lia
| left; right; right; right; exists 2, fpos; split; [left; reflexivity|];
first
[ left; unfold in_zr; cbn [fst snd]; rewrite EFA3; change (fs_frame_bytes 2) with 256; fold F; clear - Hrg; lia
| right; unfold in_zr, shadow_addr; cbn [fst snd]; rewrite <- SB_SHADOW_OFF; change (fs_frame_bytes 2 / 8) with 32;
rewrite EFA3; fold F; unfold SB; clear - Hrg; lia ] ]
| ]).
destruct Hin.
- flag0 E528 EFL3.
- prreg HS (1%bv : bv 5) Rra. prreg HS (10%bv : bv 5) Ra0.
pose (RET := paj_ret_at (fx := fq) (PL := PL_both3_0) (PI := PI)).
lazymatch goal with |- SRr _ ?Wx _ _ => eapply (RET Wx _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)) end.
intros mat'. unfold treac_disco_table_json_post. apply apost_base_same_fx.
lazymatch type of HJ3 with ajournal _ _ _ _ _ _ _ _ _ _ _ ?lyx ?Sx _ _ _ _ =>
lazymatch goal with |- exists ly' S' regs' mem' md', mkCfg (mkst ?rg _ ?mm _) ?mdx = _ /\ _ => exists lyx, Sx, rg, mm, mdx end end.
split; [rewrite Rra, (AG 1%nat) by lia; rewrite (EE 1%nat 1%bv eq_refl), Hra; reflexivity|].
split; [eapply (ajournal_mono_k SEGS B); [apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ3 | exact Hk]|].
split; [apply aregs_preserved_eqs; creg HS AG EE|].
split; [unfold ablocks; rewrite blocks_stack_free_state; exact HPerm3|].
rewrite Ra0.
split; [intros Hc; rewrite E653, (Hr1 Hc); reflexivity|].
split; [|intros Hc Hle; rewrite E653, (Hr3 Hc Hle); reflexivity].
intros Hc Hlt. destruct (Hr2 Hc Hlt) as (Er & Hg). split; [rewrite E653, Er; reflexivity|].
destruct (Hbuf Hc) as (Hbin & Hcapsz).
assert (Hbin3 : In (buf, Nb) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm3 | exact Hbin]).
destruct (al_blocks _ _ LAWS _ _ _ _ _ buf Nb HAR3 Hbin3) as (_ & Hb4096 & Hbceil & Hbapp & Hbpres & _).
pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 buf Nb 2 fpos HAR3 Hbin3 Hfin3) as HdBF.
unfold zdisjoint in HdBF. cbn [fst snd] in HdBF. change (fs_frame_bytes 2) with 256 in HdBF. rewrite EFA3 in HdBF. fold F in HdBF.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hbapp.
assert (HL : Z.of_nat (length (reac_disco_table_json_c.tj_text T now ++ [0])) = tj_len T now + 1)
by (unfold tj_len; rewrite length_app; cbn [length]; lia).
apply (garr8_frame SEGS _ _ _ _ Hg).
intros a Ha. rewrite HL in Ha.
apply (mbyte_of_frame_x SEGS E _ _ _ a HFr); [clear - Ha Hlt Hcapsz Hbceil Hb4096 C1; lia|].
intros rg Hin.
lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In rg rs') in Hin end.
cbn [In] in Hin.
repeat (destruct Hin as [<- | Hin];
[ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; evalE AG; intros Hrg;
first
[ clear - Hrg; lia
| assert (a = FL) by (clear - Hrg; lia); subst a; exact (proj2 (Hbpres FL ltac:(clear - Ha Hlt Hcapsz; lia)) HFLown)
| clear - Hrg Ha Hlt Hcapsz Hbceil Hbapp HF8lo HF8hi; unfold SB in Hrg; lia
| clear - Hrg Ha Hlt Hcapsz HdBF; lia
| clear - Hrg Ha Hlt Hcapsz Hbceil Hsp1 Hceil Hslo HSK; lia ]
| ]).
destruct Hin.
Qed.
End h.
End f.
End d.
