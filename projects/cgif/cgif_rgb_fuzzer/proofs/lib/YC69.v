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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI04 YI1i YI08.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YC04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YC19 YF8z YC1d YC1a YC2o YC10 YC1b YC2u
YC4u YC4z YC52 YC53 YC51.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK0p YI0c YM01 YG0e YC05.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCaq YC6j YCbj YCas YCbh YCbk YC7e.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section PX.
Variable B : asyms.
Hypothesis TL : TraLib B.
Hypothesis LAWS : AR_laws trasegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis FFL : frame_flag_lawP trasegs B.
Hypothesis ASF7 : astack_free_realizes trasegs B A_stack_free_7 7.
Hypothesis ASSF8 : aset_shadow_realizes trasegs B A_set_shadow_f8 0xf8.
Let HBcode := tl_code B TL. Let errno_low := tl_env B TL.
Lemma rga_EPI : rga_fromF B ss_EPI (INV_X B).
Proof.
rga_prelude.
destruct HINV as (Hk & s' & bef' & beffmt' & cur' & Hobj & Hcg' & Hwf' & HcW' & HcH' & Hattr' & Hraw' & Hbef' & HPerm' & Hcl').
destruct Hk as [Hk Hbud].
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := ga_idx_of_base_lo rs 67%nat 644 in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_region) in
pose proof (ast_ok_set_region trasegs Ex ssx msx i r (set_window r 644 648) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
(region_ok_rewindow trasegs Ex _ r 644 648 (st_ok_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity))
ltac:(cbn [YQ0b.r_base base_val ms_mem restrict mkst]; ga_evalE0 AG;
intros o Ho; apply (apresent_writable trasegs); unfold shadow_addr in HFSpres3; rewrite <- ?SB_SHADOW_OFF in HFSpres3; unfold SB in HFSpres3;
apply (proj1 (HFSpres3 o ltac:(clear - Ho; lia)))))) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.
pose proof HAR3 as HARa.
aj_run_to_sh tratbl_lib_ok HS HJ3 A_set_shadow_f8. { ga_awrR AG fpos F EFA3 54%nat 67%nat. }
assert (KB1 : rga_blocks_kept B ly3 S3 (w_H W3) (ms_mem ms3) (ms_mem ms)).
{ eapply (rga_blocks_kept_run B LAWS _ _ ly3 S3 W3 _ _ _ TRGBADD_STK (spZ regs) [(7, fpos)] HARa HFr);
[ ga_awrR AG fpos F EFA3 54%nat 67%nat | lia | intros c p [Hcp | []]; injection Hcp as <- <-; exact Hfin3 ]. }
clear HF HFr HG HARa.
rreg HS (10%bv : bv 5) Ra0. rreg HS (11%bv : bv 5) Ra1. rreg HS (1%bv : bv 5) Rra.
rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp.
rewrite (st_ok_restrict_mkst trasegs _ _ _ _ HS eq_refl). cbn [ss_pc].
change (Z_to_bv 64 348376) with (Z_to_bv 64 A_set_shadow_f8).
clear Kgot0 Kcell0 Kguar0 Kuar0 Vgr0. ga_aconsts HROD HJ3 Kgot0 Kcell0 Kguar0 Kuar0 Vgr0.
pose proof (proj1 HJ3) as HARb.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_set_shadow_at trasegs B LAWS Hsegs A_set_shadow_f8 0xf8 ASSF8 _ (ms_regs msX) (ms_mem msX) TRGBADD_STK (spZ regs)
(ablocks_fp (trgb_own r g s N bef beffmt)) ly S W mem md [(7, fpos)] ly3 S3 _ _ 7 fpos (SB + F / 8 + 532) 96 (-512) (Z_to_bv 64 0x83b38) HJ3) end.
- left; reflexivity.
- rewrite Ra0. cbn [sv_denot]. ga_evalE0 AG. reflexivity.
- exact Ra1.
- lia.
- rewrite EFA3. fold F. unfold shadow_addr. rewrite <- SB_SHADOW_OFF. unfold SB. lia.
- rewrite EFA3. fold F. unfold shadow_addr. rewrite <- SB_SHADOW_OFF. change (fs_frame_bytes 7 / 8) with 1024. unfold SB. lia.
- unfold spZ at 1. rewrite Rsp. ga_evalE AG.
- reflexivity. - lia. - rewrite FFS. unfold ESTACK. lia.
- rewrite Rgp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 3%nat) by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
- rewrite Rtp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 4%nat) by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
- exact Rra.
- vm_compute. reflexivity. }
cbv beta. intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & HP4 & Heff4 & Hfr4 & Hoff4).
clear Ra0 Ra1 Rra Rsp Rgp Rtp.
assert (KB2 : rga_blocks_kept B ly3 S3 (w_H W3) (ms_mem ms) mem4).
{ eapply (rga_blocks_kept_off B LAWS ly3 S3 W3 _ _ mem4 (fun a => SB + F / 8 + 532 <= a < SB + F / 8 + 532 + 96) HARb Hfr4).
intros a Ha. right. left. unfold SB in Ha. zlia. }
ga_aconsts HROD HJ4 Kgot4 Kcell4 Kguar4 Kuar4 Vgr4.
reseat HS HJ4 HP4 [1; 2; 3]%nat AG
ltac:(idtac; first [ ga_keptV Hfr4 Hoff4 AG Kgot0 Kgot4 Kcell0 Kcell4 Kguar0 Kguar4 Kuar0 Kuar4 Vgr0 Vgr4 | match goal with |- ?g => idtac "KEPTFAIL" g end; fail ]).
clear Kgot0 Kcell0 Kguar0 Kuar0 Vgr0. rename Kgot4 into Kgot0. rename Kcell4 into Kcell0. rename Kguar4 into Kguar0. rename Kuar4 into Kuar0. rename Vgr4 into Vgr0.
pose proof (proj1 HJ4) as HARc.
aj_run_to_sh tratbl_lib_ok HS HJ4 A_stack_free_7. { ga_awrR AG fpos F EFA3 54%nat 67%nat. }
assert (KB3 : rga_blocks_kept B ly3 S3 (w_H W3) mem4 (ms_mem ms0)).
{ eapply (rga_blocks_kept_run B LAWS _ _ ly3 S3 W3 _ _ _ TRGBADD_STK (spZ regs) [(7, fpos)] HARc HFr);
[ ga_awrR AG fpos F EFA3 54%nat 67%nat | lia | intros c p [Hcp | []]; injection Hcp as <- <-; exact Hfin3 ]. }
clear HF HFr HG HARc.
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let idx := ga_idx_of_base_lo rs 54%nat 5184 in let idx := eval vm_compute in idx in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3) msX) idx _ HS eq_refl) as HRfd; cbn [ms_mem restrict] in HRfd;
lazymatch type of HRfd with region_ok _ _ _ (YQ0b.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 54 F cs lo hi wlo whi 8184 8%N (SOff 66 0) FL HRfd
ltac:(ga_evalE AG) ltac:(cbn; tauto) ltac:(cbn [sv_denot]; ga_evalE0 AG; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; reflexivity)
ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); clear - HFLrng C1; lia) ltac:(cbn; lia)) as Vtrail end;
clear HRfd end.
assert (Htrail : rdword (aview trasegs (w_H W3) (ms_mem ms0)) (F + 8192 - 8) = Some FL).
{ replace (F + 8192 - 8) with (F + 8184) by lia. apply (rdword_of_val_mem trasegs _ _ _ _ Vtrail). clear - HFLrng C1. lia. }
rreg HS (10%bv : bv 5) Ra0. rreg HS (11%bv : bv 5) Ra1. rreg HS (1%bv : bv 5) Rra.
rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp.
rewrite (st_ok_restrict_mkst trasegs _ _ _ _ HS eq_refl). cbn [ss_pc].
change (Z_to_bv 64 250708) with (Z_to_bv 64 A_stack_free_7).
clear Kgot0 Kcell0 Kguar0 Kuar0 Vgr0. ga_aconsts HROD HJ4 Kgot0 Kcell0 Kguar0 Kuar0 Vgr0.
pose proof (proj1 HJ4) as HARd.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_stack_free_at trasegs B LAWS Hsegs ML FFL A_stack_free_7 7 ASF7 ltac:(lia) _ (ms_regs msX) (ms_mem msX) TRGBADD_STK (spZ regs)
(ablocks_fp (trgb_own r g s N bef beffmt)) ly S W mem md [] ly3 S3 _ _ fpos 5216 (-512) (Z_to_bv 64 0x83b58) HJ4) end.
- rewrite Ra0. cbn [sv_denot]. ga_evalE0 AG. rewrite EFA3. fold F. first [reflexivity | unfold w64; f_equal; lia].
- exact Ra1.
- change (fs_frame_bytes 7) with 8192. lia.
- reflexivity.
- rewrite EFA3, EFL3. fold F FL. change (fs_frame_bytes 7) with 8192. exact Htrail.
- unfold spZ at 1. rewrite Rsp. ga_evalE AG.
- reflexivity. - lia. - rewrite FFS. unfold ESTACK. lia.
- rewrite Rgp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 3%nat) by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
- rewrite Rtp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 4%nat) by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
- exact Rra.
- vm_compute. reflexivity. }
cbv beta. intros W5 c5 _ (-> & regs5 & mem5 & md5 & -> & HJ5 & HP5 & Heff5 & Hfr5 & Hpres5).
clear Ra0 Ra1 Rra Rsp Rgp Rtp.
assert (KB4 : rga_blocks_kept B ly3 S3 (w_H W3) (ms_mem ms0) mem5).
{ eapply (rga_blocks_kept_off B LAWS ly3 S3 W3 _ _ mem5
(fun a => (shadow_addr (frame_addr ly3 7 fpos) <= a < shadow_addr (frame_addr ly3 7 fpos) + 5216 / 8) \/ a = flag_addr ly3 7 fpos \/
(spZ regs + -512 - ESTACK <= a < spZ regs + -512)) HARd).
- intros a Ha Hna. apply Hfr5; [exact Ha | | | ]; intros Hx; apply Hna; [left | right; left | right; right]; exact Hx.
- intros a [Ha | [-> | Ha]].
+ right. left. rewrite EFA3 in Ha. fold F in Ha. unfold shadow_addr in Ha. rewrite <- SB_SHADOW_OFF in Ha. unfold SB in Ha. change (5216 / 8) with 652 in Ha. zlia.
+ right. right. rewrite EFL3. fold FL. exact HFLown.
+ left. unfold ESTACK in Ha. lia. }
assert (Eab5 : ablocks B ly3 (stack_free_state 7 fpos S3) = ablocks B ly3 S3) by (unfold ablocks; rewrite blocks_stack_free_state; reflexivity).
reseat HS HJ5 HP5 [2]%nat AG
ltac:(idtac; first [
eapply region_kept_aview_w;
[ ga_evalE AG
| let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; apply Hfr5;
[ lia
| rewrite EFA3; fold F; unfold shadow_addr; rewrite <- SB_SHADOW_OFF; unfold SB; change (5216 / 8) with 652; lia
| rewrite EFL3; fold FL; clear - Ha HFLrng Hceil Hslo FFS; lia
| unfold ESTACK; lia ]
| let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha _;
let Pj := fresh "Pj" in pose proof HJ5 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Pj & _); apply Pj; rewrite FFS; lia ]
| match goal with |- ?g => idtac "KEPTFAIL" g end; fail ]).
pose proof (proj1 HJ5) as HARe.
aj_run_to_sh tratbl_lib_ok HS HJ5 0x83ba8. { ga_awrR AG fpos F EFA3 54%nat 67%nat. }
assert (KB5 : rga_blocks_kept B ly3 S3 (w_H W3) mem5 (ms_mem ms1)).
{ unfold rga_blocks_kept. rewrite <- Eab5.
eapply (rga_blocks_kept_run B LAWS _ _ ly3 (stack_free_state 7 fpos S3) W3 _ _ _ TRGBADD_STK (spZ regs) [] HARe HFr);
[ ga_awrR AG fpos F EFA3 54%nat 67%nat | lia | intros c p [] ]. }
clear HF HFr HG HARe.
pose proof (rga_blocks_kept_trans B ly3 S3 _ _ _ _ (rga_blocks_kept_trans B ly3 S3 _ _ _ _ (rga_blocks_kept_trans B ly3 S3 _ _ _ _ (rga_blocks_kept_trans B ly3 S3 _ _ _ _ KB1 KB2) KB3) KB4) KB5) as KB.
clear KB1 KB2 KB3 KB4 KB5.
rreg HS (1%bv : bv 5) R1. rreg HS (10%bv : bv 5) R10.
eapply (SRr_ret_at trasegs tratbl_lib tratbl_lib_ok Hwx_tfa W3 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold rga_post, trgb_addframe_postV, apost_baseF. rga_cbn_cx_goal.
lazymatch goal with |- exists fx' ly' S' regs' mem' md', mkCfg (mkst ?rg _ ?mm _) ?mdx = _ /\ _ => exists fx, ly3, (stack_free_state 7 fpos S3), rg, mm, mdx end.
split; [rewrite R1; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 1%nat) by lia; rewrite (EE 1%nat 1%bv eq_refl), Hra; reflexivity|].
split; [exact Hfrm|].
split; [cbn [ms_mem]; eapply (ajournal_mono_k trasegs _); [apply (ajournal_materialize trasegs _ LAWS tra_segs_low); exact HJ5 | exact Hk]|].
split; [apply aregs_preserved_eqs; ga_creg HS AG EE|].
exists s', bef', beffmt', cur'.
assert (Hin_own : forall b, In b (trgb_own r g s' N bef' beffmt') -> In b (ablocks B ly3 S3)).
{ intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact HPerm'|]. apply in_or_app. left. exact Hb. }
split.
{ eapply (rg_obj_at_blk_kept (w_H W3) (w_H W3) (ms_mem ms3) (ms_mem ms1) r LAY_Rgb _ 64 Hobj lay_inside_Rgb).
change 64 with (req_size 64). apply KB. apply Hin_own. left. reflexivity. }
split.
{ apply (rg_tcgif_at_blocks_kept (w_H W3) (w_H W3) (ms_mem ms3) (ms_mem ms1) g s' N Hcg').
intros b sz Hb. apply KB. apply Hin_own. right. apply in_or_app. left. exact Hb. }
repeat match goal with |- _ /\ _ => split; [assumption|] end.
split; [intros b Hb; destruct (Hcl' b Hb) as [T A]; split; [exact T|]; intros blc i Hbl Hi; apply A; assumption|].
unfold rga_bud in Hbud; cbn [c_S] in Hbud.
eapply bud_le_mono; [eapply bud_le_trans; [exact Hbud | unfold stack_free_state; apply bud_le_set_fs] | clear - Hk; rga_lia ..].
Qed.
End PX.
End d.
