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
Lemma rf_R1 : rf_from B ss_R2 (INV_R B 300) -> rf_from B ss_R1 (INV_R B 35).
Proof.
intros RN. rf_prelude.
destruct HINV as (Hk0 & Eab3 & curi & Ecur & Hcuri).
assert (Hpd3 : In (pdata, nb) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hpdc).
reshok HS.
aj_run_to_tok trbtbl_lib_ok HS HJ3 SHOK RBspan A_readdata.
{ awrRFB AG fpos F EFA3 ltac:(right; exact Hown). }
rfb_after_run AG HJ3.
rf_stream_words2 HS B10 E33 E34 Vp Vn. rf_stream_cur HS B10 35%nat Ecur Vc.
change (N.to_nat 8) with 8%nat in Vp, Vn, Vc.
rfb_drop_cur HS.
aconstsF HJ3 Kgot0 Kcell0 Kguar0 Kuar0.
rreg HS (10%bv : bv 5) Ra0. rreg HS (11%bv : bv 5) Ra1. rreg HS (12%bv : bv 5) Ra2. rreg HS (1%bv : bv 5) Rra.
rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp.
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
change (Z_to_bv 64 531812) with (Z_to_bv 64 A_readdata).
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) _) _ =>
eapply (aj_readdata_at B TL LAWS AMEMCPY _ (ms_regs msX) (ms_mem msX) STK sp0 FP ly S W0 mem0 md0 ((0, fpos) :: own) ly3 S3 _ kk
st (dst + 12) 2 pdata nb curi (sp1 - sp0) _);
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
| lia | clear - HDSTB; lia
| intros a Ha; split; [right; right; right; exists cid, pos; split; [right; exact Hown | left; unfold in_zr; cbn [fst snd]; rewrite ?EFA3; clear - Ha Hdst1 Hdst2; lia] | rewrite Hes; clear - Ha HSPB HDSTB Hsp1 C1 HTS Has; lia]
| apply amem_range_high; [clear; lia | clear - HDSTB; lia | clear - HDSTB; lia]
| eapply range_addressable_sub; [exact HRAdst | lia | lia]
| intros _; eapply (shadow_hull_vis_of_frame trbsegs B LAWS ly3 S3 W3 _ _ cid pos (dst + 12) 2 (proj1 HJ3) Hfin3); rewrite ?EFA3; clear - Hdst1 Hdst2; lia
| right; left; unfold rboxed in Hsd; clear - Hsd HSTB HDSTB; lia
| unfold rboxed in DPF; clear - DPF Hdst1 Hdst2 Hrq2; lia ] end. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & r1 & cur1 & -> & HJ2 & HP2 & Ha02 & Hr1 & Vp' & Vn' & Vc' & Hfr2 & Hpres2).
rewrite Hes in Hfr2. replace (sp0 + (sp1 - sp0)) with sp1 in Hfr2 by (clear; lia).
clear Ra0 Ra1 Ra2 Rra Rsp Rgp Rtp Vp Vn Vc.
assert (Hcb1 : cur <= cur1 <= nb) by (clear - Hr1 Hcuri Hcur Hnb; destruct Hr1 as [(_ & X & -> & _)|(_ & _ & -> & _)]; lia). clear Hr1 Ha02.
aconstsF HJ2 Kgot1 Kcell1 Kguar1 Kuar1.
lazymatch type of HKEPT with rfc_kept _ _ _ ?mN _ _ _ _ _ _ =>
pose proof (rfc_kept_step _ _ _ mN mem2 _ _ _ _ _ _ (fun a => (dst + 12 <= a < dst + 12 + 2) \/ (st + 16 <= a < st + 24) \/ (sp1 - 32 - 4096 <= a < sp1)) HKEPT HSEP
ltac:(intros a Ha Hn; apply Hfr2; [exact Ha | clear - Hn; tauto | clear - Hn; tauto | clear - Hn; tauto])
ltac:(intros a Ha; cbn beta in *; clear - Ha Hsp1 HTS Has; lia) ltac:(clear - HSPB; lia)) as KEPT2 end.
clear HKEPT. rename KEPT2 into HKEPT.
rfb_RA HKEPT HJ2 HRAst HRAdst.
lazymatch type of HS with st_ok _ _ ?ssx _ => let l := eval vm_compute in (seq 0 (length (ss_mem ssx))) in
reseat HS HJ2 HP2 l AG
ltac:(first [ eapply region_kept_aview; [evalE AG | intros a Ha; apply Hfr2;
[ clear - Ha Hsp1 HSPB HSTB HDSTB HF4096 HFceil HF8lo HF8hi HTS Has C1 C3; unfold SB in *; lia
| unfold rboxed in DFF, Hsd; clear - Ha Hsp1 HSPB HSTB HDSTB DFF Hsd Hdst1 Hdst2 HF4096 HFceil HF8lo HF8hi HTS Has C1 C3; unfold SB in *; lia
| clear - Ha Hsp1 HSPB HSTB HDSTB HF4096 HFceil HF8lo HF8hi HTS Has C1 C3; unfold SB in *; lia
| clear - Ha Hsp1 HSPB HSTB HDSTB HF4096 HFceil HF8lo HF8hi HTS Has C1 C3; unfold SB in *; lia ] | exact Hpres2]
| apply (region_kept_val trbsegs _ _ _ A_GOT_shadow 8 A_shadow_glob); [exact Kgot0 | exact Kgot1 | lia]
| apply (region_kept_val trbsegs _ _ _ A_shadow_glob 8 SHADOW_OFF); [exact Kcell0 | exact Kcell1 | lia]
| apply (region_kept_val trbsegs _ _ _ A_GOT_uar 8 A_uar_glob); [exact Kguar0 | exact Kguar1 | lia]
| apply (region_kept_val trbsegs _ _ _ A_uar_glob 4 1); [exact Kuar0 | exact Kuar1 | lia]
| match goal with |- ?g => idtac "KEPTFAIL" g end ]) end.
rfb_add_atom HS 300%nat (Z_to_bv 64 cur1) E300.
rebaseE HS AG HEv; clear HEv.
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
lazymatch type of HS with st_ok _ ?Ev2 _ _ =>
pose proof (ast_ok_add_region trbsegs Ev2 _ _ (cur_region 300) HS eq_refl
ltac:(unfold cur_region, region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst];
evalE AG; split; [clear - HSTB C1; lia|]; split; [clear - HSTB; lia|]; split;
[ intros o Ho; apply (apresent_writable trbsegs); apply HJpres; clear - Ho Hst1 Hst2 Hwlo HTS Has; lia
| apply Forall_cons; [|apply Forall_nil];
apply (chunk_ok_val trbsegs Ev2 _ st 16 8 (SOff 300 0) cur1); [rewrite sv_denot_SOff0; exact E300 | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); clear - Hcb1 Hcur HnbM; lia | clear; cbn; lia | exact Vc'] ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
unfold cur_region; cbn [all_disjoint]; unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]; evalE AG;
unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob; unfold rboxed in Hsd;
clear - Hsd Hsp1 HSPB HSTB HDSTB HF4096 HFceil HF8lo HF8hi C1 C3 HTS Has; unfold SB in *; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.
clear HJpres.
rf_relow HS AG X2 X10 X11 EX32 Usp E10 E11 E32 B10 B11.
rf_hand RN HS.
split; [exact Hk0|]. split; [exact Eab3|]. exists cur1. split; [exact E300 | exact Hcb1].
Qed.
End c.
End b.
