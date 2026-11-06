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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YCe7 YF9i YCeb YCe8 YCfq YCdy YCfr YCdv YCe9 YCgi YChv YChx YChw YCgl YChb YChm YChi YChj YChk YChl YChn YChg YChc.
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
Hypothesis ML : model_laws (as_universe B).
Hypothesis AMALLOC : amalloc_realizes trbsegs B.
Let HBcode := tl_code B TL. Let errno_low := tl_env B TL.
Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL. Let HBguar := tl_got_uar B TL. Let HBuar := tl_uar_cell B TL.
Lemma ra_I_aux : ra_from B ss_L (INV_L B) -> ra_from B ss_X1 (INV_X B) -> ra_from B ss_I (INV_D B).
Proof.
intros RL RX. ra_prelude.
pose proof HINV as (Hk3 & Eab3 & K1 & EK & HK1r & HK1s).
assert (Hraw3 : In (raw, RAW_SIZE) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hraw_in).
assert (Hing3 : In (g, CGIF_SIZE) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hing).
ra_blocks3 Hraw3 Hing3. fold F in HdFR, HdFG.
relowC HS AG E10 E11 E32 E10n E11n E32n.
reshok_bx HS 40%nat.
aj_run_tok trbtbl_lib_ok HS HJ3 SHOK RABspan.
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrRA AG fpos F EFA3.
upd_aboveW HUP HFr AG. clear HF HFr HG.
clear Kgot3 Kcell3 Kguar3 Kuar3 Vgr3. aconstsA HROD HJ3 Kgot3 Kcell3 Kguar3 Kuar3 Vgr3.
rreg HS (1%bv : bv 5) Rra. rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp. rreg HS (8%bv : bv 5) Rs0.
assert (HnP32 : h * w < 2 ^ 32) by (clear - HnP; lia). assert (HnP1 : 1 <= h * w) by (clear - Hw Hh; nia).
lazymatch type of HS with st_ok _ ?Ev _ _ =>
rreg_by HS (10%bv : bv 5) (Z_to_bv 64 (h * w)) (denot_mul_hw Ev 45 44 h w E45 E44 ltac:(clear - Rh; lia) ltac:(clear - Rw; lia)) Ra0 end.
assert (Usp3 : bv_unsigned (ew E 2) = spZ regs) by (rewrite (AG 2%nat) by lia; exact Usp).
assert (Hchne : ch <> []) by (intros Hn; rewrite Hn in Hctx; cbn in Hctx; clear - Hctx; intuition discriminate).
pose proof Hch as Hch'. destruct Hch' as [(_ & Hn) | (Qs0lo & Qs0hi & Qs0al & _ & _)]; [exfalso; exact (Hchne Hn)|].
assert (Qtop64 : ly_top ly <= 2 ^ 64) by lia.
assert (Qra : 0 <= raZ regs < 2 ^ 64) by (unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq).
assert (Qs0 : 0 <= s0Z regs < 2 ^ 64) by (unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq).
assert (Qal8 : spZ regs mod 8 = 0) by (pose proof (Z.div_mod (spZ regs) 32 ltac:(lia)) as D; rewrite Hal32, Z.add_0_r in D; rewrite D; replace (32 * (spZ regs / 32)) with ((4 * (spZ regs / 32)) * 8) by lia; apply Z_mod_mult).
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let ih := idx_of_base rs 2%nat in let ih := eval vm_compute in ih in
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
replace 340936 with (pc_wrap_malloc (as_code B)) by (rewrite HBcode; reflexivity).
pose proof HJ3 as (_ & _ & _ & _ & _ & _ & Hnev3 & _ & _ & _ & _ & _ & _ & HJpres & _).
assert (HMM : MALLOC_MAX = 2 ^ 28) by reflexivity.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) ?mdX) _ =>
eapply (aj_malloc_at trbsegs B LAWS Hsegs errno_low ML AMALLOC W3 (ms_regs msX) (ms_mem msX) TRAWADD_STK (spZ regs) [(raw + 40, raw + 44)] ly S W mem md [(1, fpos)]
ly3 S3 mdX k (h * w) (-320) (Z_to_bv 64 0x89a34) ((spZ regs, raZ regs, s0Z regs) :: ch) HJ3) end.
- exact Ra0.
- rewrite HMM. clear - HnP HnP1. lia.
- rewrite (blocks_bytes_bsum B ly3 S3), Eab3, <- (blocks_bytes_bsum B ly S). unfold LIVE_RAWADD in Hlive. clear - Hlive HnP. lia.
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
- replace (pc_malloc_ra0 (as_code B)) with 0x53668 by (rewrite HBcode; reflexivity). rewrite (tl_universe B TL).
apply (ra_trace_in 0x53668 0x89a34); [exact Hctx | unfold raZ; rewrite Rra; apply unsigned_lit_small; clear; lia | right; right; split; reflexivity]. }
cbv beta. intros W4 c4 Hwle4 (ly4 & S4 & regs4 & mem4 & md4 & res & -> & HJ4 & HP4 & Ha04 & Hfrs4 & Hres).
clear Rra Rsp Rgp Rtp Rs0 Ra0 Vra Vs0 Hch1 Hchne Qs0lo Qs0hi Qs0al Qtop64 Qra Qs0 Qal8.
unfold ASTACK in Hres. replace (spZ regs + -320 - 16384) with (spZ regs - 16704) in Hres by lia. replace (spZ regs + -320) with (spZ regs - 320) in Hres by lia.
pose proof (proj1 HJ4) as HAR4.
destruct (al_layout _ _ LAWS _ _ _ _ _ ly4 HAR (proj1 (proj2 HJ4))) as (_ & EFA4 & _).
assert (Hfin4 : In (1, fpos) (frames S4)) by (rewrite Hfrs4; exact Hfin3).
assert (Hfrs4' : frames S4 = (1, fpos) :: frames S) by (rewrite Hfrs4; exact Hfrs3).
assert (HfinS4 : In (cid, pos) (frames S4)) by (rewrite Hfrs4; exact HfinS3).
frame_pres HJ4 Hfin4 EFA4 F HFp4 HFSp4.
aconstsA HROD HJ4 Kgot4 Kcell4 Kguar4 Kuar4 Vgr4.
destruct Hres as [(Hres0 & Eab4 & HK) | (Hres4096 & Eab4 & HK)].
-
assert (Hraw4 : In (raw, RAW_SIZE) (ablocks B ly4 S4)) by (rewrite Eab4; exact Hraw3).
assert (Hing4 : In (g, CGIF_SIZE) (ablocks B ly4 S4)) by (rewrite Eab4; exact Hing3).
assert (HEr : forall a, F <= a < F + 128 -> ~ False) by (intros a Ha Hn; exact Hn).
assert (HErS : forall a, SB + F / 8 <= a < SB + F / 8 + 16 -> ~ False) by (intros a Ha Hn; exact Hn).
reseat HS HJ4 HP4 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12]%nat AG
ltac:(idtac; first [ keptRA HK HJ4 AG Usp E11 E32 HfinS3 Hing3 Kgot3 Kgot4 Kcell3 Kcell4 Kguar3 Kguar4 Kuar3 Kuar4 Vgr3 Vgr4
| keptFA2 HK AG RF E70 Hfin3 HFp4 HFSp4 HEr HErS F
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 10%nat) _ _ _ _ _) =>
eapply (region_kept_block_ajw2 trbsegs B LAWS); [exact HK | exact HAR4 | exact Hraw4 | evalE AG | exact Hraw3 | lia | change (req_size RAW_SIZE) with 48; lia | lia | lia
| intros a Ha Hn; exact Hn] end
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
relowC HS AG E10 E11 E32 E10n E11n E32n. norm_ss HS.
rewrite Hres0 in Ha04.
lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pin_reg' trbsegs Ev ssv msv (10%bv : bv 5) 0 HS ltac:(cbn [ms_regs restrict mkst]; rewrite Ha04; reflexivity) eq_refl) as HS3 end.
clear HS. rename HS3 into HS. norm_ss HS. reshok_bx HS 40%nat.
aj_run_to_tok trbtbl_lib_ok HS HJ4 SHOK RABspan 0x8a0ac.
all: try (obl_blk HJ4 E10n E40 Hraw4).
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrRA AG fpos F EFA4.
clear_frames.
rebaseE HS AG HEv. clear HEv.
ra_join HS ss_X1 900%nat ra_deads_X ltac:(idtac).
ra_hand RX HS. split; [rewrite HEV; clear - Hk3; lia | rewrite Eab4, Eab3; apply Permutation_refl].
-
assert (Hrq : req_size (h * w) = h * w) by (unfold req_size; destruct (Z.eqb_spec (h * w) 0); [exfalso; clear - HnP1 e; lia | reflexivity]).
assert (Hres_in : In (res, h * w) (ablocks B ly4 S4)) by (rewrite Eab4; apply in_app_iff; right; left; reflexivity).
assert (Hraw4 : In (raw, RAW_SIZE) (ablocks B ly4 S4)) by (rewrite Eab4; apply in_app_iff; left; exact Hraw3).
assert (Hing4 : In (g, CGIF_SIZE) (ablocks B ly4 S4)) by (rewrite Eab4; apply in_app_iff; left; exact Hing3).
destruct (al_blocks _ _ LAWS _ _ _ _ _ res (h * w) HAR4 Hres_in) as (Hp16 & Hp4096 & Hpceil & Hph_ia & Hppres & _). pose proof (proj1 Hph_ia) as Hph.
pose proof (blk_off_img _ _ _ _ _ _ _ _ HAR4 Hres_in) as Hph_img.
rewrite Hrq in Hpceil, Hppres, Hph_ia.
pose proof (aftok_new_block trbsegs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ res (h * w) HJ3 HAR4 Eab4 ltac:(clear - HnP1; lia)) as Tres.
assert (Ares : forall blc lyq ownq i, In (res, h * w) blc -> 0 <= i < h * w ->
awr_byte TRAWADD_STK (spZ regs) [(raw + 40, raw + 44)] (ablocks B ly S) blc lyq ownq (res + i)).
{ intros blc lyq ownq i Hbl Hi. exact (awr_new_block_any trbsegs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ res (h * w) blc i lyq ownq HJ3 HAR4 Eab4 ltac:(clear - HnP1; lia) Hbl ltac:(rewrite Hrq; exact Hi)). }
pose proof (sep_block_frame trbsegs B LAWS ly4 S4 _ _ _ res (h * w) 1 fpos HAR4 Hres_in Hfin4) as HdPF.
unfold zdisjoint in HdPF. cbn [fst snd] in HdPF. rewrite Hrq in HdPF. change (fs_frame_bytes 1) with 128 in HdPF. rewrite EFA4 in HdPF. fold F in HdPF.
pose proof (sep_block_frame trbsegs B LAWS ly4 S4 _ _ _ res (h * w) cid pos HAR4 Hres_in HfinS4) as HdPC.
unfold zdisjoint in HdPC. cbn [fst snd] in HdPC. rewrite Hrq in HdPC. rewrite EFA4 in HdPC.
assert (HPerm4 : Permutation (ablocks B ly4 S4) ((res, h * w) :: (raw, RAW_SIZE) :: (g, CGIF_SIZE) :: (img, Nimg) :: rest)).
{ rewrite Eab4, Eab3. eapply Permutation_trans; [apply Permutation_sym; apply Permutation_cons_append|]. apply perm_skip. exact HPerm. }
pose proof (sep_blocks_perm trbsegs B LAWS _ _ _ _ _ (res, h * w) (raw, RAW_SIZE) _ HAR4 HPerm4) as HdPR.
pose proof (sep_blocks_perm trbsegs B LAWS _ _ _ _ _ (res, h * w) (g, CGIF_SIZE) _ HAR4 ltac:(eapply Permutation_trans; [exact HPerm4 | apply perm_skip; apply perm_swap])) as HdPG.
unfold zdisjoint, block_rng in HdPR, HdPG. cbn [fst snd] in HdPR, HdPG. rewrite Hrq in HdPR, HdPG.
change (req_size RAW_SIZE) with 48 in HdPR. change (req_size CGIF_SIZE) with 96 in HdPG.
box HdPF. box HdPC. box HdPR. box HdPG.
assert (HEr : forall a, F <= a < F + 128 -> ~ (res <= a < res + req_size (h * w))) by (rewrite Hrq; intros a Ha; clear - Ha HdPF HnP1; unbox; lia).
assert (HErS : forall a, SB + F / 8 <= a < SB + F / 8 + 16 -> ~ (res <= a < res + req_size (h * w))) by (rewrite Hrq; intros a Ha; clear - Ha Hph Hph_ia Hrq HF8lo HFceil HFq HF8 C1 C3; unfold SB in *; zone_lia).
reseat HS HJ4 HP4 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12]%nat AG
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
relowC HS AG E10 E11 E32 E10n E11n E32n. norm_ss HS.
lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
pose proof (st_ok_agree trbsegs 400 Ev (havoc Ev 400 [Z_to_bv 64 res]) ssv msv HS
(env_agree_havoc_ge 400 400 Ev Ev _ ltac:(lia) (env_agree_refl 400 Ev)) ltac:(vm_compute; reflexivity)) as HS3 end.
clear HS. rename HS3 into HS. rebaseE HS AG HEv.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
assert (E400 : ew Ev 400 = Z_to_bv 64 res) by (rewrite HEv; exact (ew_havoc_new _ 400 [Z_to_bv 64 res] 0 (Z_to_bv 64 0) ltac:(cbn; lia))) end.
clear HEv.
lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
pose proof (ast_ok_set_reg_fp trbsegs Ev ssx msx (10%bv : bv 5) (SOff 400 0) HS ltac:(vm_compute; reflexivity)
ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite E400, Z.add_0_r, Ha04; unfold w64; rewrite unsigned_lit_small by (clear - Hp4096 Hpceil C1 HnP1; lia); reflexivity)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
pose proof (st_ok_add_fact trbsegs Ev ssx msx 400%nat (HPTR 4) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite E400, unsigned_lit_small by (clear - Hp4096 Hpceil C1 HnP1; lia); change (2 ^ 4) with 16; clear - Hp16 Hph Hpceil HnP1 C1 C3; lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS. relowC HS AG E10 E11 E32 E10n E11n E32n. reshok_bx HS 40%nat.
aj_run_to_tok trbtbl_lib_ok HS HJ4 SHOK RABspan 0x89a84.
all: try (oblFA HJ4 E11n E40 HRA HAR Hfin Hcid0 Hflo Hfhi Hfal).
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrRA AG fpos F EFA4.
clear_frames.
rebaseE HS AG HEv. clear HEv.
ra_join HS ss_L 402%nat ra_deads_L ltac:(idtac).
ra_hand RL HS. split; [clear - Hk3; lia|].
split; [exists K1; split; [rewrite ew_havoc_old by (clear; lia); exact EK | split; [exact HK1r | exact HK1s]]|].
exists res. split; [rewrite ew_havoc_old by (clear; lia); exact E400|]. split; [exact Hres4096|].
split; [rewrite Eab4, Eab3; reflexivity|]. split; [exact Ares | exact Tres].
Qed.
Lemma ra_I : ra_from B ss_L (INV_L B) -> ra_from B ss_X1 (INV_X B) -> ra_from B ss_I (INV_D B).
Proof. exact ra_I_aux. Qed.
End c.
End b.
