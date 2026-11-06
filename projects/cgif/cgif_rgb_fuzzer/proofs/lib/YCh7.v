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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI01 YI04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YCcz.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YCe7 YF9i YCeb YCe8 YCfq YCdy YCfr YCdv YCe9 YCfx YChv YChx YChw YCgl YChb YChm YChi YChj YChk YChl YChn YChg.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma ra_awr_byte_ly : forall STK sp0 FP bl0 blc ly ly' own a,
(forall cid pos, frame_addr ly' cid pos = frame_addr ly cid pos) ->
awr_byte STK sp0 FP bl0 blc ly own a -> awr_byte STK sp0 FP bl0 blc ly' own a.
Proof.
intros STK sp0 FP bl0 blc ly ly' own a Efa [H | [H | [H | (cid & pos & Hin & H)]]]; [left; exact H | right; left; exact H | right; right; left; exact H |].
right. right. right. exists cid, pos. split; [exact Hin|]. rewrite !Efa. exact H.
Qed.
Ltac aview_kept_rng HFr AG lo hi Hn :=
lazymatch type of HFr with frame_of ?Ef ?rs (mrestrict ?Hh ?m0) (mrestrict _ (ms_mem ?msX)) =>
assert (Hn : forall a, lo <= a < hi -> aview trbsegs Hh (ms_mem msX) a = aview trbsegs Hh m0 a);
[ let a := fresh "a" in let Ha := fresh "Ha" in
intros a Ha; eapply (aview_kept_out Ef rs _ _ _ HFr); [lia|];
let rg := fresh "rg" in let Hin := fresh "Hin" in let Hrg := fresh "Hrg" in
intros (rg & Hin & Hrg);
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In rg rs1) in Hin end; cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin]; [cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val] in Hrg; revert Hrg; evalE AG; intros Hrg; lia|]);
destruct Hin
| ] end.
Section d.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AFREE : afree_realizes trbsegs B.
Let HBcode := tl_code B TL. Let errno_low := tl_env B TL.
Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL. Let HBguar := tl_got_uar B TL. Let HBuar := tl_uar_cell B TL.
Lemma ra_M_aux : ra_from B ss_T0 (INV_T0 B) -> ra_from B ss_Tf (INV_Tf B) -> ra_from B ss_M (INV_M B).
Proof.
intros RT0 RTF. ra_prelude.
pose proof HINV as (Hk3 & (K1 & EK & HK1r & HK1s) & (pI & res & E400 & E504 & HpI4096 & HpI3 & TpI & Hdisj)).
assert (HnP32 : h * w < 2 ^ 32) by (clear - HnP; lia). assert (HnP1 : 1 <= h * w) by (clear - Hw Hh; nia).
assert (Hrq : req_size (h * w) = h * w) by (unfold req_size; destruct (Z.eqb_spec (h * w) 0); [exfalso; clear - HnP1 e; lia | reflexivity]).
assert (HP3 : exists pre, Permutation (ablocks B ly3 S3) (pre ++ (pI, h * w) :: (raw, RAW_SIZE) :: (g, CGIF_SIZE) :: (img, Nimg) :: rest)).
{ destruct Hdisj as [(_ & bb & Lbb & M & HP & _) | (_ & HP)]; [exists [(bb, Lbb)] | exists []]; cbn [app];
(eapply Permutation_trans; [exact HP|]); [apply perm_skip|];
(eapply Permutation_trans; [apply Permutation_sym; apply Permutation_cons_append|]); apply perm_skip; exact HPerm. }
destruct HP3 as (pre & HP3).
assert (Hraw3 : In (raw, RAW_SIZE) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HP3|]; apply in_app_iff; right; right; left; reflexivity).
assert (Hing3 : In (g, CGIF_SIZE) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HP3|]; apply in_app_iff; right; right; right; left; reflexivity).
ra_blocks3 Hraw3 Hing3. fold F in HdFR, HdFG.
destruct (al_blocks _ _ LAWS _ _ _ _ _ pI (h * w) HAR3 HpI3) as (Hp16 & _ & Hpceil & Hph_ia & Hppres & _). pose proof (proj1 Hph_ia) as Hph. rewrite Hrq in Hpceil, Hppres, Hph_ia.
pose proof (blk_off_img _ _ _ _ _ _ _ _ HAR3 HpI3) as Hph_img.
pose proof (sep_blocks_perm trbsegs B LAWS _ _ _ _ _ (pI, h * w) (raw, RAW_SIZE) _ HAR3 ltac:(eapply Permutation_trans; [exact HP3 | apply (Permutation_app_comm pre ((pI, h * w) :: (raw, RAW_SIZE) :: (g, CGIF_SIZE) :: (img, Nimg) :: rest))])) as HdPR.
pose proof (sep_blocks_perm trbsegs B LAWS _ _ _ _ _ (pI, h * w) (g, CGIF_SIZE) _ HAR3
ltac:(eapply Permutation_trans; [exact HP3 | eapply Permutation_trans; [apply (Permutation_app_comm pre ((pI, h * w) :: (raw, RAW_SIZE) :: (g, CGIF_SIZE) :: (img, Nimg) :: rest)) | cbn [app]; apply perm_skip; apply perm_swap]])) as HdPG.
unfold zdisjoint, block_rng in HdPR, HdPG. cbn [fst snd] in HdPR, HdPG. rewrite Hrq in HdPR, HdPG.
change (req_size RAW_SIZE) with 48 in HdPR. change (req_size CGIF_SIZE) with 96 in HdPG.
pose proof (sep_block_frame trbsegs B LAWS ly3 S3 _ _ _ pI (h * w) 1 fpos HAR3 HpI3 Hfin3) as HdPF.
unfold zdisjoint in HdPF. cbn [fst snd] in HdPF. rewrite Hrq in HdPF. change (fs_frame_bytes 1) with 128 in HdPF. rewrite EFA3 in HdPF. fold F in HdPF.
pose proof (sep_block_frame trbsegs B LAWS ly3 S3 _ _ _ pI (h * w) cid pos HAR3 HpI3 HfinS3) as HdPC.
unfold zdisjoint in HdPC. cbn [fst snd] in HdPC. rewrite Hrq in HdPC. rewrite EFA3 in HdPC.
box HdPR. box HdPG. box HdPF. box HdPC.
relowC HS AG E10 E11 E32 E10n E11n E32n.
pose proof HJ3 as (_ & _ & _ & _ & _ & _ & Hnev3 & _ & _ & _ & _ & _ & _ & HJpres & _).
reshok_bx HS 40%nat.
aj_run_tok trbtbl_lib_ok HS HJ3 SHOK RABspan.
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrRA AG fpos F EFA3.
upd_aboveW HUP HFr AG. aview_kept_rng HFr AG (spZ regs - 120) (spZ regs - 108) HR1. clear HF HFr HG.
clear Kgot3 Kcell3 Kguar3 Kuar3 Vgr3. aconstsA HROD HJ3 Kgot3 Kcell3 Kguar3 Kuar3 Vgr3.
rreg HS (1%bv : bv 5) Rra. rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp. rreg HS (8%bv : bv 5) Rs0.
rreg HS (10%bv : bv 5) Ra0. rewrite E400 in Ra0.
assert (Usp3 : bv_unsigned (ew E 2) = spZ regs) by (rewrite (AG 2%nat) by lia; exact Usp).
assert (Hchne : ch <> []) by (intros Hn; rewrite Hn in Hctx; cbn in Hctx; clear - Hctx; intuition discriminate).
pose proof Hch as Hch'. destruct Hch' as [(_ & Hn) | (Qs0lo & Qs0hi & Qs0al & _ & _)]; [exfalso; exact (Hchne Hn)|].
assert (Qtop64 : ly_top ly <= 2 ^ 64) by lia.
assert (Qra : 0 <= raZ regs < 2 ^ 64) by (unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq).
assert (Qs0 : 0 <= s0Z regs < 2 ^ 64) by (unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq).
assert (Qal8 : spZ regs mod 8 = 0) by (pose proof (Z.div_mod (spZ regs) 32 ltac:(lia)) as D; rewrite Hal32, Z.add_0_r in D; rewrite D; replace (32 * (spZ regs / 32)) with ((4 * (spZ regs / 32)) * 8) by lia; apply Z_mod_mult).
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let ih := idx_of_base_lo rs 2%nat (-104) in let ih := eval vm_compute in ih in
let rh := eval vm_compute in (nth ih rs got_region) in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3) msX) ih rh HS ltac:(vm_compute; reflexivity)) as HRstk; cbn [ms_mem restrict] in HRstk;
lazymatch type of HRstk with region_ok _ _ _ (YQ0b.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-8) 8%N (SOff 1 0) (raZ regs) HRstk
Usp3 ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 1%nat) by lia; rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vra;
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-16) 8%N (SOff 8 0) (s0Z regs) HRstk
Usp3 ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 8%nat) by lia; rewrite (EE 8%nat 8%bv eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vs0 end;
clear HRstk;
assert (Hch1 : achain ly3 (aview trbsegs (w_H W3) (ms_mem msX)) (spZ regs - 320) (spZ regs) ((spZ regs, raZ regs, s0Z regs) :: ch));
[ apply (achain_ly_top ly); [pose proof (proj1 (proj2 HJ3)) as LY; destruct LY as (_ & _ & _ & _ & _ & _ & _ & _ & LT & _); exact LT|];
replace (spZ regs + -8) with (spZ regs - 8) in Vra by lia; replace (spZ regs + -16) with (spZ regs - 16) in Vs0 by lia;
exact (achain_push ly _ _ (spZ regs) (s0Z regs) (raZ regs) _ (spZ regs - 320) Hch Qtop64 HUP
(rdword_of_val_mem trbsegs _ _ _ _ Vra Qra) (rdword_of_val_mem trbsegs _ _ _ _ Vs0 Qs0) Hra4 ltac:(clear - Hceil Hslo Hstk0 FFS; lia) Qal8
ltac:(clear - Qs0lo Qs0hi; lia) ltac:(clear; lia))
| ] end.
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
replace 340932 with (pc_wrap_free (as_code B)) by (rewrite HBcode; reflexivity).
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) ?mdX) _ =>
eapply (aj_free_at trbsegs B LAWS Hsegs errno_low ML AFREE W3 (ms_regs msX) (ms_mem msX) TRAWADD_STK (spZ regs) [(raw + 40, raw + 44)] ly S W mem md [(1, fpos)]
ly3 S3 mdX k pI (h * w) (-320) (Z_to_bv 64 0x89db8) ((spZ regs, raZ regs, s0Z regs) :: ch) HJ3 HpI3) end.
- exact Ra0.
- unfold spZ at 1. rewrite Rsp, Usp3, unsigned_lit_small by (clear - Hceil Hslo Hstk0 FFS Hshi H47 C1; lia). clear; lia.
- reflexivity. - clear; lia. - rewrite FFS. unfold ASTACK. clear; lia.
- rewrite Rgp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 3%nat) by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
- rewrite Rtp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 4%nat) by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
- exact Rra.
- apply ret_ok_even. vm_compute. reflexivity.
- rewrite HEV in Hev. clear - Hnev3 Hk3 Hev. lia.
- apply (achain_chain_pre ly3 _ (spZ regs - 320) (spZ regs) _ _ Hch1);
[ unfold spZ at 1 2; rewrite Rsp, Usp3, unsigned_lit_small by (clear - Hceil Hslo Hstk0 FFS Hshi H47 C1; lia); clear - Hceil Hslo Hstk0 FFS C1; lia
| unfold s0Z; rewrite Rs0; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact Usp3
| unfold raZ; rewrite Rra, unsigned_lit_small by (clear; lia); clear; lia ].
- replace (pc_free_ra0 (as_code B)) with 0x53508 by (rewrite HBcode; reflexivity). rewrite (tl_universe B TL).
apply (ra_trace_in 0x53508 0x89db8); [exact Hctx | unfold raZ; rewrite Rra; apply unsigned_lit_small; clear; lia | left; split; reflexivity].
- intros Hin i Hi. exact (TpI Hin i Hi). }
cbv beta. intros W4 c4 _ (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HP4 & (l1 & l2 & Ebl3 & Ebl4) & Hfrs4 & HK).
clear Rra Rsp Rgp Rtp Rs0 Ra0 Vra Vs0 Hch1 Hchne Qs0lo Qs0hi Qs0al Qtop64 Qra Qs0 Qal8.
unfold ASTACK in HK. replace (spZ regs + -320 - 16384) with (spZ regs - 16704) in HK by lia. replace (spZ regs + -320) with (spZ regs - 320) in HK by lia.
pose proof (proj1 HJ4) as HAR4.
assert (HP34 : Permutation (ablocks B ly3 S3) ((pI, h * w) :: ablocks B ly4 S4)) by (rewrite Ebl3, Ebl4; apply Permutation_sym; apply Permutation_middle).
assert (Hraw4 : In (raw, RAW_SIZE) (ablocks B ly4 S4)).
{ pose proof (Permutation_in _ HP34 Hraw3) as [X | X]; [exfalso; injection X as X1 X2; clear - X1 HdPR HnP1; unbox; lia | exact X]. }
assert (Hing4 : In (g, CGIF_SIZE) (ablocks B ly4 S4)).
{ pose proof (Permutation_in _ HP34 Hing3) as [X | X]; [exfalso; injection X as X1 X2; clear - X1 HdPG HnP1; unbox; lia | exact X]. }
destruct (al_layout _ _ LAWS _ _ _ _ _ ly4 HAR (proj1 (proj2 HJ4))) as (_ & EFA4 & _).
assert (Hfin4 : In (1, fpos) (frames S4)) by (rewrite Hfrs4; exact Hfin3).
assert (Hfrs4' : frames S4 = (1, fpos) :: frames S) by (rewrite Hfrs4; exact Hfrs3).
frame_pres HJ4 Hfin4 EFA4 F HFp4 HFSp4.
aconstsA HROD HJ4 Kgot4 Kcell4 Kguar4 Kuar4 Vgr4.
assert (HEr : forall a, F <= a < F + 128 -> ~ (pI <= a < pI + req_size (h * w))) by (rewrite Hrq; intros a Ha; clear - Ha HdPF HnP1; unbox; lia).
assert (HErS : forall a, SB + F / 8 <= a < SB + F / 8 + 16 -> ~ (pI <= a < pI + req_size (h * w))) by (rewrite Hrq; intros a Ha; clear - Ha Hph Hph_ia Hrq HF8lo HFceil HFq HF8 C1 C3; unfold SB in *; zone_lia).
reseat HS HJ4 HP4 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13]%nat AG
ltac:(idtac; first [ lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 11%nat) _ _ _ _ _) =>
eapply (region_kept_frame_aj trbsegs _); [exact HK | evalE AG | exact HfinS3 | rwEFA; lia | rwEFA; lia | lia
| rewrite Hrq; intros a Ha Hn; clear - Ha Hn HdPC Hflo Hfhi; unbox; lia] end
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 32%nat) _ _ _ _ _) =>
eapply (region_kept_block_aj trbsegs _); [exact HK | evalE AG | exact Hing3 | lia | change (req_size CGIF_SIZE) with 96; lia | lia
| rewrite Hrq; intros a Ha Hn; clear - Ha Hn HdPG; unbox; lia] end
| keptRA HK HJ4 AG Usp E11 E32 HfinS3 Hing3 Kgot3 Kgot4 Kcell3 Kcell4 Kguar3 Kguar4 Kuar3 Kuar4 Vgr3 Vgr4
| keptFA2 HK AG RF E70 Hfin3 HFp4 HFSp4 HEr HErS F
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 10%nat) _ _ _ _ _) =>
eapply (region_kept_block_ajw2 trbsegs B LAWS); [exact HK | exact HAR4 | exact Hraw4 | evalE AG | exact Hraw3 | lia | change (req_size RAW_SIZE) with 48; lia | lia | lia
| rewrite Hrq; intros a Ha Hn; clear - Ha Hn HdPR; unbox; lia] end
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
relowC HS AG E10 E11 E32 E10n E11n E32n. norm_ss HS. reshok_bx HS 40%nat.
aj_run_to_tok trbtbl_lib_ok HS HJ4 SHOK RABspan 0x89db8.
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrRA AG fpos F EFA4.
aview_kept_rng HFr AG (spZ regs - 120) (spZ regs - 108) HR2. clear_frames.
lazymatch type of HR2 with forall a, _ -> aview _ _ (ms_mem ?msY) a = _ =>
lazymatch type of HR1 with forall a, _ -> _ = aview _ _ ?m3 a =>
assert (HR : forall a, spZ regs - 120 <= a < spZ regs - 108 -> aview trbsegs (w_H W4) (ms_mem msY) a = aview trbsegs (w_H W3) m3 a)
by (intros a Ha; rewrite (HR2 a Ha); pose proof HK as (HK1 & _); rewrite (HK1 a) by (clear - Ha Hceil Hslo Hstk0 Hshi H47 FFS C1; lia); apply HR1; exact Ha) end end.
clear HR1 HR2.
destruct Hdisj as [(Hres0 & bb & Lbb & M & HPerm3 & Hbb4096 & HM & Abb & Tbb & Vbb & VM) | (Hres25 & HPerm3)].
+
assert (HPerm4 : Permutation (ablocks B ly4 S4) ((bb, Lbb) :: ablocks B ly S)).
{ rewrite Ebl4. rewrite <- (app_nil_r ((bb, Lbb) :: ablocks B ly S)). apply (Permutation_app_inv l1 l2 ((bb, Lbb) :: ablocks B ly S) [] (pI, h * w)). rewrite <- Ebl3. exact HPerm3. }
assert (Hbb4 : In (bb, Lbb) (ablocks B ly4 S4)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm4|]; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bb Lbb HAR4 Hbb4) as (Hbb16 & _ & Hbbceil & Hbbh_ia & Hbbpres & _). pose proof (proj1 Hbbh_ia) as Hbbh.
pose proof (blk_off_img _ _ _ _ _ _ bb Lbb HAR4 Hbb4) as Hbbh_img.
pose proof (req_size_pos Lbb ltac:(clear - HM; lia)) as [_ HLbb].
pose proof (val_mem_kept trbsegs _ _ _ _ (spZ regs - 120) 8 bb ltac:(intros kk Hkk; apply HR; clear - Hkk; lia) Vbb) as Vbb'.
pose proof (val_mem_kept trbsegs _ _ _ _ (spZ regs - 120 + 8) 4 M ltac:(intros kk Hkk; apply HR; clear - Hkk; lia) VM) as VM'.
clear Vbb VM HR.
rreg HS (21%bv : bv 5) Qs5. rewrite E504, Hres0 in Qs5.
lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pin_reg' trbsegs Ev ssv msv (21%bv : bv 5) 0 HS ltac:(cbn [ms_regs restrict mkst]; exact Qs5) eq_refl) as HS3 end.
clear HS Qs5. rename HS3 into HS. norm_ss HS.
lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
pose proof (st_ok_agree trbsegs 600 Ev (havoc Ev 600 [Z_to_bv 64 bb; Z_to_bv 64 (M mod 2 ^ 32)]) ssv msv HS
(env_agree_havoc_ge 600 600 Ev Ev _ ltac:(lia) (env_agree_refl 600 Ev)) ltac:(vm_compute; reflexivity)) as HS3 end.
clear HS. rename HS3 into HS. rebaseE HS AG HEv.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
assert (E600 : ew Ev 600 = Z_to_bv 64 bb) by (rewrite HEv; exact (ew_havoc_new _ 600 [Z_to_bv 64 bb; Z_to_bv 64 (M mod 2 ^ 32)] 0 (Z_to_bv 64 0) ltac:(cbn; lia)));
assert (E601 : ew Ev 601 = Z_to_bv 64 (M mod 2 ^ 32)) by (rewrite HEv; exact (ew_havoc_new _ 600 [Z_to_bv 64 bb; Z_to_bv 64 (M mod 2 ^ 32)] 1 (Z_to_bv 64 0) ltac:(cbn; lia))) end.
clear HEv.
pose proof HJ4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres4' & _).
lazymatch type of HS with st_ok _ ?Ev _ _ =>
pose proof (ast_ok_add_region trbsegs Ev _ _
(YQ0b.mkRegion (Some 2%nat) (-120) (-104) (-120) (-104) [YQ0b.mkChunk (-120) (CVal 8 (SOff 600 0)); YQ0b.mkChunk (-112) (CVal 4 (SOff 601 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst];
evalE AG; split; [lia|]; split; [lia|]; split;
[ intros o Ho; apply (apresent_writable trbsegs); apply Hpres4'; rewrite FFS; lia
| apply Forall_cons; [apply (chunk_ok_val trbsegs Ev _ (spZ regs) (-120) 8 _ bb);
[cbn [sv_denot]; rewrite E600, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | replace (spZ regs + -120) with (spZ regs - 120) by lia; exact Vbb']|];
apply Forall_cons; [apply (chunk_ok_val trbsegs Ev _ (spZ regs) (-112) 4 _ (M mod 2 ^ 32));
[cbn [sv_denot]; rewrite E601, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| pose proof (Z.mod_pos_bound M (2 ^ 32) ltac:(lia)); zside | zside
| replace (spZ regs + -112) with (spZ regs - 120 + 8) by lia; apply val_mem_mod4; exact VM']|];
apply Forall_nil ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
evalE AG; unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob, A_GOT_rawadd, CGIF_SIZE; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS end.
ra_join HS ss_T0 602%nat ra_deads_T0 ltac:(idtac).
ra_hand RT0 HS. split; [clear - Hk3; lia|].
split; [exists K1; split; [rewrite ew_havoc_old by (clear; lia); exact EK | split; [exact HK1r | exact HK1s]]|].
exists bb, Lbb, M. split; [rewrite ew_havoc_old by (clear; lia); exact E600|]. split; [rewrite ew_havoc_old by (clear; lia); exact E601|].
split; [exact HPerm4|]. split; [exact Hbb4096|]. split; [exact HM|].
split; [| exact Tbb].
intros blc i Hb Hi. apply (ra_awr_byte_ly _ _ _ _ _ ly3 ly4); [intros c p; rewrite EFA4, EFA3; reflexivity | exact (Abb blc i Hb Hi)].
+
clear HR.
assert (HPerm4 : Permutation (ablocks B ly4 S4) (ablocks B ly S)).
{ rewrite Ebl4. rewrite <- (app_nil_r (ablocks B ly S)). apply (Permutation_app_inv l1 l2 (ablocks B ly S) [] (pI, h * w)). rewrite <- Ebl3. exact HPerm3. }
rreg HS (21%bv : bv 5) Qs5.
ra_join HS ss_Tf 602%nat ra_deads_Tf
ltac:(idtac; ra_join_val HS 602%nat 16%nat Qs5 Eres;
ra_join_fact HS 618%nat (mkAF 2 5 0) ltac:(rewrite Eres, E504, unsigned_lit_small by (clear - Hres25; lia); rewrite Z.pow_0_r, Z.mod_1_r; clear - Hres25; lia)).
ra_hand RTF HS. split; [clear - Hk3; lia|].
split; [exists K1; split; [rewrite ew_havoc_old by (clear; lia); exact EK | split; [exact HK1r | exact HK1s]]|].
exact HPerm4.
Qed.
Lemma ra_M : ra_from B ss_T0 (INV_T0 B) -> ra_from B ss_Tf (INV_Tf B) -> ra_from B ss_M (INV_M B).
Proof. exact ra_M_aux. Qed.
End d.
End b.
