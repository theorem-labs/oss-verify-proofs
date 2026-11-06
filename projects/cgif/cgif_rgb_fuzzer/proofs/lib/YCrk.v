(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0p YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YC02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI01.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YG0e YCcz YCd0.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI1i YI08 YI0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YCe7 YF9i YCeb YCe8 YCfq YCdy YCfr YCe9 YCfx YChv YChx YChn YCf6 YCft YCey YCe4 YCi1 YCrr YCib YCrn YCrm YCrt YCrs YCru YCro YCrb YChy.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section c.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis AMEMCPY : aintrin_realizes trbsegs B OCpy A_asan_memcpy_tfb.
Let HBcode := tl_code B TL. Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL. Let errno_low := tl_env B TL.
Let HBguar := tl_got_uar B TL. Let HBuar := tl_uar_cell B TL.
Lemma rf_R4 : rf_from B ss_EPI (INV_EPI B) -> rf_from B ss_M (INV_M B) -> rf_from B ss_R4 (INV_R B 302).
Proof.
intros REPI RN. rf_prelude.
destruct HINV as (Hk0 & Eab3 & curi & Ecur & Hcuri).
assert (Hpd3 : In (pdata, nb) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hpdc).
reshok HS.
aj_run_to_tok trbtbl_lib_ok HS HJ3 SHOK RBspan A_readdata.
{ awrRFB AG fpos F EFA3 ltac:(right; exact Hown). }
rfb_after_run AG HJ3.
rf_stream_words2 HS B10 E33 E34 Vp Vn. rf_stream_cur HS B10 302%nat Ecur Vc.
change (N.to_nat 8) with 8%nat in Vp, Vn, Vc.
assert (B88 : bv_unsigned (ew E 88) = SB + F / 8) by (rewrite E88; apply unsigned_lit_small; unfold SB; clear - HF8lo HF8hi; lia).
lazymatch type of HS with st_ok _ _ ?ssx _ =>
let rs := eval vm_compute in (ss_mem ssx) in let i := idx_of_baseA rs 88%nat in let i := eval vm_compute in i in
byte_at HS i 88%nat (SB + F / 8) B88 4 sh4 Vsh4 Rsh4 end.
assert (Hsh4 : sh4 = 1) by (subst sh4; reflexivity).
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msN) =>
assert (RAfmt : range_addressable (aview trbsegs (w_H W3) (ms_mem msN)) SHADOW_OFF (F + 32) 1) end.
{ intros y Hy. assert (y = F + 32) by (clear - Hy; lia). subst y. exists 1.
split; [|right; rewrite HFq; replace (32 * (F / 32) + 32) with ((4 * (F / 32) + 4) * 8) by lia; rewrite Z_mod_mult; clear; lia].
unfold shadow_of_addr. rewrite <- SB_SHADOW_OFF.
assert (HF32 : (F + 32) / 8 = F / 8 + 4) by (rewrite HF8; rewrite HFq at 1; replace (32 * (F / 32) + 32) with ((4 * (F / 32) + 4) * 8) by lia; rewrite Z.div_mul by lia; lia).
rewrite HF32, Z.add_assoc. rewrite Hsh4 in Vsh4. apply (aview_of_val_mem1 trbsegs); [exact Vsh4 | clear; lia]. }
pose proof (sep_block_frame trbsegs B LAWS _ _ _ _ _ pdata nb 0 fpos HAR3 Hpd3 Hfin0) as DPF0. unfold zdisjoint in DPF0. cbn [fst snd] in DPF0. rewrite EFA3 in DPF0. fold F in DPF0. change (fs_frame_bytes 0) with 64 in DPF0.
rfb_drop_cur HS.
lazymatch type of HS with st_ok _ _ ?ssx _ =>
let rs := eval vm_compute in (ss_mem ssx) in let i := idx_of_baseLo rs 75%nat 32 in let i := eval vm_compute in i in rfb_drop_nth HS i end.
aconstsF HJ3 Kgot0 Kcell0 Kguar0 Kuar0.
rreg HS (10%bv : bv 5) Ra0. rreg HS (11%bv : bv 5) Ra1. rreg HS (12%bv : bv 5) Ra2. rreg HS (1%bv : bv 5) Rra.
rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp.
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
change (Z_to_bv 64 531812) with (Z_to_bv 64 A_readdata).
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) _) _ =>
eapply (aj_readdata_at B TL LAWS AMEMCPY _ (ms_regs msX) (ms_mem msX) STK sp0 FP ly S W0 mem0 md0 ((0, fpos) :: own) ly3 S3 _ kk
st (F + 32) 1 pdata nb curi (sp1 - sp0) _);
[ exact HJ3
| rewrite Ra0; evalE AG
| rewrite Ra1; evalE AG
| rewrite Ra2; reflexivity
| rewrite Rgp; evalE AG; rewrite (EE 3%nat 3%bv eq_refl); exact Hgp
| rewrite Rtp; evalE AG; rewrite (EE 4%nat 4%bv eq_refl); exact Htp
| exact Rra
| vm_compute; reflexivity
| unfold spZ; rewrite Rsp; evalE AG
| rewrite <- Zminus_mod_idemp_l, Hsp1al16, <- Zminus_mod_idemp_r, Hsp0al; reflexivity
| clear - Hsp1 Hwhi; lia
| rewrite Hes; clear - Hsp1 Hwlo HTS Has; lia
| exact Hst8
| clear - Hsp1 Hst1; lia
| exact Hst2
| exact HRAst
| exact Vp | exact Vn | exact Vc
| left; split; [exact Hnb | exact Hpd3] | clear - Hcuri Hcur; lia
| lia | clear - HF4096; lia
| intros a Ha; split; [right; right; right; exists 0, fpos; split; [left; reflexivity | left; unfold in_zr; cbn [fst snd]; rewrite ?EFA3; fold F; change (fs_frame_bytes 0) with 64; clear - Ha; lia] | rewrite Hes; clear - Ha HSPB HFceil Hsp1 C1 HTS Has; lia]
| apply amem_range_high; [clear; lia | unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp; clear - HFapp; lia | clear - HFceil; lia]
| exact RAfmt
| intros _; eapply (shadow_hull_vis_of_frame trbsegs B LAWS ly3 S3 W3 _ _ 0 fpos (F + 32) 1 (proj1 HJ3) Hfin0); rewrite ?EFA3; fold F; change (fs_frame_bytes 0) with 64; clear; lia
| right; left; clear - HSTB HFceil; lia
| clear - DPF0 Hrq2; lia ] end. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & r1 & cur1 & -> & HJ2 & HP2 & Ha02 & Hr1 & Vp' & Vn' & Vc' & Hfr2 & Hpres2).
rewrite Hes in Hfr2. replace (sp0 + (sp1 - sp0)) with sp1 in Hfr2 by (clear; lia).
clear Ra0 Ra1 Ra2 Rra Rsp Rgp Rtp Vp Vn Vc RAfmt Vsh4 Hsh4 Rsh4.
assert (Hcb1 : cur <= cur1 <= nb) by (clear - Hr1 Hcuri Hcur Hnb; destruct Hr1 as [(_ & X & -> & _)|(_ & _ & -> & _)]; lia). clear Hr1 Ha02.
aconstsF HJ2 Kgot1 Kcell1 Kguar1 Kuar1.
lazymatch type of HKEPT with rfc_kept _ _ _ ?mN _ _ _ _ _ _ =>
pose proof (rfc_kept_stepE _ _ _ mN mem2 _ _ _ _ _ _ (fun a => (F + 32 <= a < F + 32 + 1) \/ (st + 16 <= a < st + 24) \/ (sp1 - 32 - 4096 <= a < sp1))
(fun a => in_zr a (frame_rng lyc (0, fpos)) \/ in_zr a (shadow_addr (frame_addr lyc 0 fpos), fs_frame_bytes 0 / 8)) HKEPT HSEP
ltac:(intros a Ha Hn; apply Hfr2; [exact Ha | clear - Hn; tauto | clear - Hn; tauto | clear - Hn; tauto])
ltac:(intros a Ha; cbn beta in *; unfold in_zr, frame_rng; cbn [fst snd]; fold F; change (fs_frame_bytes 0) with 64; clear - Ha Hsp1 HTS Has; lia) ltac:(clear - HSPB; lia)
ltac:(intros a Ha; revert Ha; unfold in_zr, frame_rng, shadow_addr; cbn [fst snd]; rewrite <- SB_SHADOW_OFF; change (fs_frame_bytes 0 / 8) with 8; change (fs_frame_bytes 0) with 64; fold F; unfold SB; clear - HFceil HF8hi C1; lia)
HFSB HFSF) as KEPT2 end.
clear HKEPT. rename KEPT2 into HKEPT.
rfb_RA HKEPT HJ2 HRAst HRAdst.
lazymatch type of HS with st_ok _ _ ?ssx _ => let l := eval vm_compute in (seq 0 (length (ss_mem ssx))) in
reseat HS HJ2 HP2 l AG
ltac:(first [ eapply region_kept_aview; [evalE AG | intros a Ha; apply Hfr2;
[ unfold rboxed in DFF, HFimg; unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp; unfold off_img in HFimg;
clear - Ha Hsp1 HSPB HSTB HDSTB DFF HFapp HFimg Hdst1 Hdst2 HF4096 HFceil HF8lo HF8hi HTS Has C1 C3; unfold SB in *; lia
| unfold rboxed in DFF, Hsd, HFimg; unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp; unfold off_img in HFimg;
clear - Ha Hsp1 HSPB HSTB HDSTB DFF Hsd HFapp HFimg Hdst1 Hdst2 HF4096 HFceil HF8lo HF8hi HTS Has C1 C3; unfold SB in *; lia
| clear - Ha Hsp1 HSPB HSTB HDSTB HF4096 HFceil HF8lo HF8hi HTS Has C1 C3; unfold SB in *; lia
| clear - Ha Hsp1 HSPB HSTB HDSTB HF4096 HFceil HF8lo HF8hi HTS Has C1 C3; unfold SB in *; lia ] | exact Hpres2]
| apply (region_kept_val trbsegs _ _ _ A_GOT_shadow 8 A_shadow_glob); [exact Kgot0 | exact Kgot1 | lia]
| apply (region_kept_val trbsegs _ _ _ A_shadow_glob 8 SHADOW_OFF); [exact Kcell0 | exact Kcell1 | lia]
| apply (region_kept_val trbsegs _ _ _ A_GOT_uar 8 A_uar_glob); [exact Kguar0 | exact Kguar1 | lia]
| apply (region_kept_val trbsegs _ _ _ A_uar_glob 4 1); [exact Kuar0 | exact Kuar1 | lia]
| match goal with |- ?g => idtac "KEPTFAIL" g end ]) end.
rfb_add_atom HS 303%nat (Z_to_bv 64 cur1) E303.
rebaseE HS AG HEv; clear HEv.
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
lazymatch type of HS with st_ok _ ?Ev2 _ _ =>
pose proof (ast_ok_add_region trbsegs Ev2 _ _ (cur_region 303) HS eq_refl
ltac:(unfold cur_region, region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst];
evalE AG; split; [clear - HSTB C1; lia|]; split; [clear - HSTB; lia|]; split;
[ intros o Ho; apply (apresent_writable trbsegs); apply HJpres; clear - Ho Hst1 Hst2 Hwlo HTS Has; lia
| apply Forall_cons; [|apply Forall_nil];
apply (chunk_ok_val trbsegs Ev2 _ st 16 8 (SOff 303 0) cur1); [rewrite sv_denot_SOff0; exact E303 | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); clear - Hcb1 Hcur HnbM; lia | clear; cbn; lia | exact Vc'] ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
unfold cur_region; cbn [all_disjoint]; unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]; evalE AG;
unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob; unfold rboxed in Hsd;
clear - Hsd Hsp1 HSPB HSTB HDSTB HF4096 HFceil HF8lo HF8hi C1 C3 HTS Has; unfold SB in *; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.
clear HJpres.
destruct (al_frames _ _ LAWS _ _ _ _ _ 0 fpos (proj1 HJ2) Hfin0) as (_ & _ & HF0pres2 & _). change (fs_frame_bytes 0) with 64 in HF0pres2. rewrite !EFA3 in HF0pres2. fold F in HF0pres2.
set (fmt := abyte (w_H W3) mem2 (F + 32)).
assert (Rfmt : 0 <= fmt < 256) by (subst fmt; apply abyte_range).
rfb_add_atom HS 310%nat (Z_to_bv 64 fmt) E310.
rebaseE HS AG HEv; clear HEv.
lazymatch type of HS with st_ok _ ?Ev2 ?ssx2 ?msx2 =>
pose proof (st_ok_add_fact trbsegs Ev2 ssx2 msx2 310%nat (mkAF 0 255 0) HS
ltac:(clear HS; unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E310; rewrite unsigned_lit_small by (clear - Rfmt; lia); rewrite Z.pow_0_r, Z.mod_1_r; clear - Rfmt; lia)) as HS3;
clear HS; rename HS3 into HS end.
lazymatch type of HS with st_ok _ ?Ev2 _ _ =>
pose proof (ast_ok_add_region trbsegs Ev2 _ _ (YQ0b.mkRegion (Some 75%nat) 32 40 32 40 [YQ0b.mkChunk 32 (CVal 1 (SOff 310 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst];
evalE AG; split; [clear - HF4096; lia|]; split; [clear - HFceil C1; lia|]; split;
[ intros o Ho; apply (apresent_writable trbsegs); apply (proj1 (HF0pres2 (F + o) ltac:(clear - Ho; lia)))
| apply Forall_cons; [|apply Forall_nil];
apply (chunk_ok_val trbsegs Ev2 _ F 32 1 (SOff 310 0) fmt); [rewrite sv_denot_SOff0; exact E310 | clear - Rfmt; cbn; lia | clear; cbn; lia
| subst fmt; apply abyte_val; apply (proj1 (HF0pres2 (F + 32) ltac:(clear; lia)))] ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]; evalE AG;
unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob; unfold rboxed in Hsd, DFF, HFimg; unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp; unfold off_img in HFimg;
clear - Hsd DFF HFimg HFapp Hdst1 Hdst2 Hsp1 HSPB HSTB HDSTB HF4096 HFceil HF8lo HF8hi C1 C3 HTS Has; unfold SB in *; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.
rf_relow HS AG X2 X10 X11 EX32 Usp E10 E11 E32 B10 B11.
reshok HS.
aj_run_tok trbtbl_lib_ok HS HJ2 SHOK RBspan.
{ awrRFB AG fpos F EFA3 ltac:(right; exact Hown). }
rfb_after_run AG HJ2.
srr_branch_tok trbtbl_lib_ok HS SHOK RBspan.
-
lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => clear Hb end.
norm_ss HS.
rebaseE HS AG HEv; clear HEv. rf_relow HS AG X2 X10 X11 EX32 Usp E10 E11 E32 B10 B11.
reshok HS.
aj_run_to_tok trbtbl_lib_ok HS HJ2 SHOK RBspan RRFC_EPI.
{ awrRFB AG fpos F EFA3 ltac:(right; exact Hown). }
rfb_after_run AG HJ2.
rebaseE HS AG HEv; clear HEv. rf_relow HS AG X2 X10 X11 EX32 Usp E10 E11 E32 B10 B11.
rreg HS (10%bv : bv 5) Ra0.
rfb_epi_arrive HS cur1 0 0 ltac:(rfb_old_atom E303) ltac:(reflexivity) ltac:(reflexivity) E390 E391 E392.
rfj_join HS ss_EPI 400%nat rf_EPI_deads_bv.
rf_hand REPI HS.
split; [rewrite Hk0; unfold EV_RRFC; clear; lia|]. exists (2 ^ 64 - 1), cur1, 0, 0.
split; [rewrite (ew_havoc_new _ 400 _ 0 (Z_to_bv 64 0)) by (cbn; lia); cbn [nth]; exact Ra0|].
split; [rewrite ew_havoc_old by (cbn; lia); exact E390|]. split; [rewrite ew_havoc_old by (cbn; lia); exact E391|]. split; [rewrite ew_havoc_old by (cbn; lia); exact E392|].
split; [exact Hcb1|]. left. split; [reflexivity|]. split; [rewrite Eab3; exact HPerm|]. split; reflexivity.
-
lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => first [rename Hb into Hc | idtac] end.
rewrite branch_ltu_U in Hc.
lazymatch type of HS with st_ok _ ?Ex _ _ => rewrite (U_lit Ex 1) in Hc by lia end.
rewrite U_SOff in Hc. rewrite ?ew_ewset_other in Hc by lia. rewrite E310 in Hc. rewrite unsigned_lit_small in Hc by (clear - Rfmt; lia).
assert (Hfmt : fmt = 3 \/ fmt = 4).
{ apply Z.ltb_ge in Hc. unfold zcanon, M64 in Hc. clear - Hc Rfmt. destruct (Z_lt_ge_dec fmt 3) as [Hl|Hg].
- exfalso. replace (fmt + -3) with ((fmt + -3 + 2 ^ 64) + (-1) * 2 ^ 64) in Hc by lia. rewrite Z_mod_plus_full in Hc. rewrite Z.mod_small in Hc by lia. lia.
- rewrite Z.mod_small in Hc by lia. lia. }
clear Hc.
norm_ss HS.
rebaseE HS AG HEv; clear HEv. rf_relow HS AG X2 X10 X11 EX32 Usp E10 E11 E32 B10 B11.
reshok HS.
aj_run_to_tok trbtbl_lib_ok HS HJ2 SHOK RBspan 340936.
all: try (oblsA HJ2 Hpd3 HRAst HRAdst E10 E11 E11 E32).
{ awrRFB AG fpos F EFA3 ltac:(right; exact Hown). }
rfb_after_run AG HJ2.
rebaseE HS AG HEv; clear HEv. rf_relow HS AG X2 X10 X11 EX32 Usp E10 E11 E32 B10 B11.
rf_hand RN HS.
split; [exact Hk0|]. split; [exact Eab3|]. split; [exists cur1; split; [exact E303 | exact Hcb1]|]. exists fmt. split; [exact E310 | exact Hfmt].
Qed.
End c.
End b.
