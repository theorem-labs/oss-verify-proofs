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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI5w YI5z.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v ACef AF0l ACej ACeh ACem ACek ACei ACep.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCeo.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACer ACfm ACf5 ACf9 ACf7.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Ltac nat_side := first [ apply (proj1 (Nat.ltb_lt _ _)); vm_compute; reflexivity
| apply (proj1 (Nat.eqb_neq _ _)); vm_compute; reflexivity
| cbn [length Nat.add]; apply (proj1 (Nat.leb_le _ _)); vm_compute; reflexivity ].
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {ROB : ACeh.ro_tfa_below_ofl}.
Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Variable FP : list (Z * Z).
Variable POST : rtcx -> world tfibsegs -> config -> Prop.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis AMEMSET : aintrin_realizes tfibsegs B OSet A_asan_memset.
Let HBcode := tl_code B TL. Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL.
Let HBguar := tl_got_uar B TL. Let HBuar := tl_uar_cell B TL. Let errno_low := tl_env B TL.
Lemma rt_A2_aux : rt_from B MT FP POST ss_B (INV_0 B MT 0) -> rt_from B MT FP POST ss_A2 (INV_0 B MT 0).
Proof.
intros RB. rt_prelude.
pose proof HINV as (Hk0 & Hacc & Eab3).
relowRT HS AG E10 E11 E32 E10n E11n E32n.
fs_roF HS.
trim_base HS 75%nat 80 256.
reshok HS.
aj_run_tok tfibtbl_lib_ok HS HJ3 SHOK RTBspan.
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrRT AG fpos F EFA3.
clear_frames.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msC) =>
assert (ZS : forall i, 0 <= i < 6 -> aview tfibsegs (w_H W3) (ms_mem msC) (SB + F / 8 + 4 + i) = Some 0) end.
{ lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let ih := idx_of_base rs 88%nat in let ih := eval vm_compute in ih in
let rh := eval vm_compute in (nth ih rs got_region) in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3) msX) ih rh HS ltac:(vm_compute; reflexivity)) as HR88; cbn [ms_mem restrict] in HR88 end.
assert (Hb88 : forall Ex, ew Ex 88 = Z_to_bv 64 (SB + F / 8) -> base_val Ex (Some 88%nat) = SB + F / 8)
by (intros Ex HEx; cbn [base_val]; rewrite HEx; apply unsigned_lit_small; unfold SB; clear - HF8lo HF8hi; lia).
intros i Hi.
assert (Hi6 : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5) by (clear - Hi; lia).
destruct Hi6 as [-> | [-> | [-> | [-> | [-> | ->]]]]];
[ replace (SB + F / 8 + 4 + 0) with (SB + F / 8 + 4) by (clear; lia) | replace (SB + F / 8 + 4 + 1) with (SB + F / 8 + 5) by (clear; lia)
| replace (SB + F / 8 + 4 + 2) with (SB + F / 8 + 6) by (clear; lia) | replace (SB + F / 8 + 4 + 3) with (SB + F / 8 + 7) by (clear; lia)
| replace (SB + F / 8 + 4 + 4) with (SB + F / 8 + 8) by (clear; lia) | replace (SB + F / 8 + 4 + 5) with (SB + F / 8 + 9) by (clear; lia) ];
(eapply (zs_chunk1 _ _ _ _ _ _ HR88); [apply Hb88; rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E88 | cbn; tauto | unfold SB; clear - HF8lo; lia | unfold SB; clear - HF8hi; lia]). }
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msC) =>
assert (HRA : range_addressable (aview tfibsegs (w_H W3) (ms_mem msC)) SHADOW_OFF (F + 32) 48) end.
{ apply zero_shadow_range; [replace (F + 32) with ((F / 8 + 4) * 8) by (clear - HFq HF8; lia); apply Z_mod_mult | reflexivity |].
intros i Hi. unfold shadow_of_addr. rewrite <- SB_SHADOW_OFF.
replace ((F + 32) / 8) with (F / 8 + 4) by (replace (F + 32) with ((F / 8 + 4) * 8) by (clear - HFq HF8; lia); rewrite Z.div_mul by (clear; lia); reflexivity).
replace (SB + (F / 8 + 4) + i) with (SB + F / 8 + 4 + i) by (clear; lia).
first [ apply ZS; change (48 / 8) with 6 in Hi; exact Hi | match goal with |- ?g => idtac "ZS-GOAL" g end ]. }
rreg HS (10%bv : bv 5) Ra0. rreg HS (11%bv : bv 5) Ra1. rreg HS (12%bv : bv 5) Ra2. rreg HS (1%bv : bv 5) Rra.
rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp.
rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
change (Z_to_bv 64 334456) with (Z_to_bv 64 A_asan_memset).
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_intrin_at tfibsegs B LAWS Hsegs OSet A_asan_memset AMEMSET _ (ms_regs msX) (ms_mem msX) LLVMF_STK (spZ regs) FP ly S W mem md [(2, fpos)]
ly3 S3 _ _ (F + 32) 0 48 (sp1 - spZ regs) (Z_to_bv 64 RT_memset_ra) HJ3) end.
- rewrite Ra0. evalE AG.
- rewrite Ra1. reflexivity.
- rewrite Ra2. reflexivity.
- clear; lia. - clear - HF4096; lia. - clear - HFceil C1; ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; lia.
- unfold spZ at 1. rewrite Rsp. evalE AG.
- rewrite Zminus_mod, Hsp1al16, Hal16. reflexivity.
- clear - Hsp1; lia. - rewrite FFS. unfold ESTACK. clear - Hsp1; lia.
- rewrite Rgp. evalE AG. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
- rewrite Rtp. evalE AG. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
- exact Rra.
- vm_compute. reflexivity.
- intros a Ha. split; [| unfold ESTACK; clear - Ha Hsp1 HFceil Hceil Hslo Hstk0 FFS C1; ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; lia]. right. right. right. exists 2, fpos. split; [left; reflexivity|]. left.
unfold in_zr, frame_rng. cbn [fst snd]. change (fs_frame_bytes 2) with 256. rewrite EFA3. fold F. clear - Ha; lia.
- apply amem_range_high; clear - HFhigh HFhigh_img HFceil C1 C3; ceil; unfold in_app, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; zone_lia.
- exact HRA.
- intros _. eapply (shadow_hull_vis_of_frame tfibsegs B LAWS ly3 S3 _ _ _ 2 fpos (F + 32) 48 (proj1 HJ3) Hfin3);
[rewrite EFA3; fold F; clear; lia | rewrite EFA3; fold F; change (fs_frame_bytes 2) with 256; clear; lia | clear; lia].
- exact I. }
cbv beta. intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & HP4 & Ha04 & Heff & Hfr4 & Hpres4).
clear Ra0 Ra1 Ra2 Rra Rsp Rgp Rtp ZS HRA.
replace (spZ regs + (sp1 - spZ regs)) with sp1 in Hfr4 by (clear; lia).
clear Kgot3 Kcell3 Kguar3 Kuar3. aconstsF HJ3 Kgot3 Kcell3 Kguar3 Kuar3. aconstsF HJ4 Kgot4 Kcell4 Kguar4 Kuar4.
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos (proj1 HJ4) Hfin3) as (_ & _ & HFpres4 & HFSpres4). change (fs_frame_bytes 2) with 256 in HFpres4, HFSpres4.
change (256 / 8) with 32 in HFSpres4. rewrite !EFA3 in HFpres4, HFSpres4. fold F in HFpres4, HFSpres4.
reseat HS HJ4 HP4 [0; 1; 2; 3; 4; 5; 6; 7]%nat AG
ltac:(idtac; first
[ lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 88%nat) _ _ _ _ _) =>
eapply region_kept_aview; [evalE AG
| intros a Ha; apply Hfr4; [clear - Ha HF8lo HF8hi; unfold SB in *; lia | clear - Ha HF8hi HFhigh HFhigh_img C3; unfold SB in *; zone_lia | clear - Ha HF8hi Hceil Hslo Hsp1 FFS C1; unfold SB, ESTACK in *; lia]
| exact Hpres4] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 75%nat) _ _ _ _ _) =>
eapply region_kept_aview; [evalE AG
| intros a Ha; apply Hfr4; [clear - Ha HF4096 HFceil C1; ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; lia | clear - Ha; lia | clear - Ha HFceil Hceil Hslo Hsp1 FFS C1; ceil; unfold ESTACK, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; lia]
| exact Hpres4] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 70%nat) _ _ _ _ _) =>
eapply region_kept_aview; [evalE AG
| intros a Ha; apply Hfr4; [clear - Ha Hsp1 Hshi H47 Hslo Hstk0 Hceil C1 FFS; lia | clear - Ha HFceil Hceil Hslo Hsp1 FFS C1; ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; lia | clear - Ha; unfold ESTACK; lia]
| exact Hpres4] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 2%nat) _ _ _ _ _) =>
eapply region_kept_aview; [evalE AG
| intros a Ha; apply Hfr4; [clear - Ha Hslo Hstk0 Hshi H47 Hceil C1 FFS; lia | clear - Ha HFceil Hceil Hslo FFS C1; ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; lia | clear - Ha Hsp1; unfold ESTACK; lia]
| exact Hpres4] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion None ?a _ _ _ _) =>
first [ change a with A_GOT_shadow; apply (region_kept_val tfibsegs _ _ _ A_GOT_shadow 8 A_shadow_glob); [exact Kgot3 | exact Kgot4 | clear; lia]
| change a with A_shadow_glob; apply (region_kept_val tfibsegs _ _ _ A_shadow_glob 8 SHADOW_OFF); [exact Kcell3 | exact Kcell4 | clear; lia]
| change a with A_GOT_uar; apply (region_kept_val tfibsegs _ _ _ A_GOT_uar 8 A_uar_glob); [exact Kguar3 | exact Kguar4 | clear; lia]
| change a with A_uar_glob; apply (region_kept_val tfibsegs _ _ _ A_uar_glob 4 1); [exact Kuar3 | exact Kuar4 | clear; lia] ] end
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
relowRT HS AG E10 E11 E32 E10n E11n E32n. norm_ss HS.
assert (VZ : forall off (w : nat), 32 <= off -> off + Z.of_nat w <= 80 -> val_mem tfibsegs (mrestrict (w_H W3) mem4) (F + off) w 0).
{ intros off w Ho Hw. apply rt_val_mem_zero. intros i Hi. replace (F + off + i) with (F + 32 + (off - 32 + i)) by (clear; lia).
rewrite (Heff (off - 32 + i)) by (clear - Ho Hw Hi; lia). reflexivity. }
lazymatch type of HS with st_ok _ ?Ev _ _ =>
pose proof (ast_ok_add_region tfibsegs Ev _ _
(YP09.mkRegion (Some 75%nat) 32 80 32 80
[YP09.mkChunk 32 (CVal 8 (SLit 0)); YP09.mkChunk 40 (CVal 8 (SLit 0)); YP09.mkChunk 48 (CVal 4 (SLit 0)); YP09.mkChunk 52 (CVal 4 (SLit 0));
YP09.mkChunk 56 (CVal 2 (SLit 0)); YP09.mkChunk 58 (CVal 2 (SLit 0)); YP09.mkChunk 60 (CVal 2 (SLit 0)); YP09.mkChunk 62 (CVal 2 (SLit 0));
YP09.mkChunk 64 (CVal 8 (SLit 0)); YP09.mkChunk 72 (CVal 8 (SLit 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
rewrite RF, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split;
[ intros o Ho; apply (apresent_writable tfibsegs); apply (proj1 (HFpres4 (F + o) ltac:(lia)))
| repeat (apply Forall_cons; [eapply (chunk_ok_val tfibsegs Ev _ F); [reflexivity | zside | zside | apply VZ; cbn; lia] |]); apply Forall_nil ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
rewrite RF; evalE AG; unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob, SB;
clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 C3 HF4096 HFceil HFhigh HFhigh_img HF8lo HF8hi HFq HF8 HF8c; repeat split; first [zone_lia | match goal with |- ?g => idtac "DISJ" g; fail end])) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
pose proof (ast_ok_add_region tfibsegs Ev _ _ (YP09.mkRegion (Some 75%nat) 0 32 0 32 []) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
rewrite RF, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable tfibsegs); apply (proj1 (HFpres4 (F + o) ltac:(lia))))
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
rewrite RF; evalE AG; unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob, SB;
clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 C3 HF4096 HFceil HFhigh HFhigh_img HF8lo HF8hi HFq HF8 HF8c; repeat split; first [zone_lia | match goal with |- ?g => idtac "DISJ" g; fail end])) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
rebaseE HS AG HEv. clear HEv. rt_hand RB HS.
split; [exact Hk0 | split; [macc | cbn [c_ly c_S]; exact Eab3]].
Qed.
Lemma rt_A2 : rt_from B MT FP POST ss_B (INV_0 B MT 0) -> rt_from B MT FP POST ss_A2 (INV_0 B MT 0).
Proof. exact rt_A2_aux. Qed.
End c.
End b.
