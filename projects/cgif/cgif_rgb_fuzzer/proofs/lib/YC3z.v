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
YG00 YG0a YG01 YG0h YG0u YG0d YC04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YC19 YF8z YC1d YC1a YC2o YC10 YC2p YC0x YC1b YC2u YC4o YC4q YC4p YC3g YC46 YC4g YC4c YC4d YC4e YC4h YC4a.
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
Hypothesis TL : TraLib B.
Hypothesis LAWS : AR_laws trasegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AFREE : afree_realizes trasegs B.
Let HBcode := tl_code B TL. Let errno_low := tl_env B TL.
Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL. Let HBguar := tl_got_uar B TL. Let HBuar := tl_uar_cell B TL.
Lemma ra_H_aux : ra_from B ss_X1 (INV_X B) -> ra_from B ss_G3 (INV_T0 B).
Proof.
intros RX. ra_prelude.
pose proof HINV as (Hk3 & (K1 & EK & HK1r & HK1s) & (bb & Lbb & M & E600 & E601 & HPerm3 & Hbb4096 & HM & Abb & Tbb)).
assert (Hraw3 : In (raw, RAW_SIZE) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm3|]; right; exact Hraw_in).
assert (Hing3 : In (g, CGIF_SIZE) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm3|]; right; exact Hing).
assert (Hbb3 : In (bb, Lbb) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm3|]; left; reflexivity).
ra_blocks3 Hraw3 Hing3. fold F in HdFR, HdFG.
destruct (al_blocks _ _ LAWS _ _ _ _ _ bb Lbb HAR3 Hbb3) as (Hbb16 & _ & Hbbceil & Hbbh_ia & Hbbpres & _). pose proof (proj1 Hbbh_ia) as Hbbh.
pose proof (blk_off_img _ _ _ _ _ _ bb Lbb HAR3 Hbb3) as Hbbh_img.
pose proof (req_size_pos Lbb ltac:(clear - HM; lia)) as [_ HLbb].
pose proof (sep_blocks_perm trasegs B LAWS _ _ _ _ _ (bb, Lbb) (raw, RAW_SIZE) _ HAR3 ltac:(eapply Permutation_trans; [exact HPerm3 | apply perm_skip; exact HPerm])) as HdBR.
pose proof (sep_blocks_perm trasegs B LAWS _ _ _ _ _ (bb, Lbb) (g, CGIF_SIZE) _ HAR3
ltac:(eapply Permutation_trans; [exact HPerm3 | apply perm_skip; eapply Permutation_trans; [exact HPerm | apply perm_swap]])) as HdBG.
unfold zdisjoint, block_rng in HdBR, HdBG. cbn [fst snd] in HdBR, HdBG. change (req_size RAW_SIZE) with 48 in HdBR. change (req_size CGIF_SIZE) with 96 in HdBG.
pose proof (sep_block_frame trasegs _ LAWS ly3 S3 _ _ _ bb Lbb 1 fpos HAR3 Hbb3 Hfin3) as HdBF.
unfold zdisjoint in HdBF. cbn [fst snd] in HdBF. change (fs_frame_bytes 1) with 128 in HdBF. rewrite EFA3 in HdBF. fold F in HdBF.
pose proof (sep_block_frame trasegs _ LAWS ly3 S3 _ _ _ bb Lbb cid pos HAR3 Hbb3 HfinS3) as HdBC.
unfold zdisjoint in HdBC. cbn [fst snd] in HdBC. rewrite EFA3 in HdBC.
box HdBR. box HdBG. box HdBF. box HdBC.
relowC HS AG E10 E11 E32 E10n E11n E32n.
pose proof HJ3 as (_ & _ & _ & _ & _ & _ & Hnev3 & _ & _ & _ & _ & _ & _ & HJpres & _).
lazymatch type of HS with st_ok _ ?Ev _ _ =>
pose proof (ast_ok_add_region trasegs Ev _ _ (YQ0b.mkRegion (Some 2%nat) (-336) (-320) (-336) (-320) []) HS eq_refl
ltac:(unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst];
rewrite (AG 2%nat) by lia; rewrite Usp; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable trasegs); apply HJpres; rewrite FFS; lia)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
evalE AG; unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob, A_GOT_rawadd, CGIF_SIZE; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS. reshok_bx HS 40%nat.
aj_run_tok tratbl_lib_ok HS HJ3 SHOK RABspan.
all: try (obl_blk HJ3 E10n E40 Hraw3).
all: try (obl_blk HJ3 E32n E40 Hing3).
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrRA AG fpos F EFA3.
upd_aboveW HUP HFr AG. clear HF HFr HG.
rreg HS (1%bv : bv 5) Rra. rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp. rreg HS (8%bv : bv 5) Rs0.
rreg HS (10%bv : bv 5) Ra0. rewrite E600 in Ra0.
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
assert (Hch1 : achain ly3 (aview trasegs (w_H W3) (ms_mem msX)) (spZ regs - 320) (spZ regs) ((spZ regs, raZ regs, s0Z regs) :: ch));
[ apply (achain_ly_top ly); [pose proof (proj1 (proj2 HJ3)) as LY; destruct LY as (_ & _ & _ & _ & _ & _ & _ & _ & LT & _); exact LT|];
replace (spZ regs + -8) with (spZ regs - 8) in Vra by lia; replace (spZ regs + -16) with (spZ regs - 16) in Vs0 by lia;
exact (achain_push ly _ _ (spZ regs) (s0Z regs) (raZ regs) _ (spZ regs - 320) Hch Qtop64 HUP
(rdword_of_val_mem trasegs _ _ _ _ Vra Qra) (rdword_of_val_mem trasegs _ _ _ _ Vs0 Qs0) Hra4 ltac:(clear - Hceil Hslo Hstk0 FFS; lia) Qal8
ltac:(clear - Qs0lo Qs0hi; lia) ltac:(clear; lia))
| ] end.
rewrite (st_ok_restrict_mkst trasegs _ _ _ _ HS eq_refl). cbn [ss_pc].
replace 340224 with (pc_wrap_free (as_code B)) by (rewrite HBcode; reflexivity).
clear Kgot3 Kcell3 Kguar3 Kuar3 Vgr3. aconstsA HROD HJ3 Kgot3 Kcell3 Kguar3 Kuar3 Vgr3.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) ?mdX) _ =>
eapply (aj_free_at trasegs B LAWS Hsegs errno_low ML AFREE W3 (ms_regs msX) (ms_mem msX) TRAWADD_STK (spZ regs) [(raw + 40, raw + 44)] ly S W mem md [(1, fpos)]
ly3 S3 mdX k bb Lbb (-320) (Z_to_bv 64 0x89420) ((spZ regs, raZ regs, s0Z regs) :: ch) HJ3 Hbb3) end.
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
- replace (pc_free_ra0 (as_code B)) with 0x53244 by (rewrite HBcode; reflexivity). apply (tl_universe B TL).
apply (ra_trace_in 0x53244 0x89420); [exact Hctx | unfold raZ; rewrite Rra; apply unsigned_lit_small; clear; lia | right; left; split; reflexivity].
- intros Hin i Hi. exact (Tbb Hin i Hi). }
cbv beta. intros W4 c4 _ (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HP4 & (l1 & l2 & Ebl3 & Ebl4) & Hfrs4 & HK).
clear Rra Rsp Rgp Rtp Rs0 Ra0 Vra Vs0 Hch1 Hchne Qs0lo Qs0hi Qs0al Qtop64 Qra Qs0 Qal8.
unfold ASTACK in HK. replace (spZ regs + -320 - 16384) with (spZ regs - 16704) in HK by lia. replace (spZ regs + -320) with (spZ regs - 320) in HK by lia.
pose proof (proj1 HJ4) as HAR4.
assert (HPerm4 : Permutation (ablocks B ly4 S4) (ablocks B ly S)).
{ rewrite Ebl4. apply Permutation_sym. apply (@Permutation_cons_app_inv _ _ l1 l2 (bb, Lbb)). rewrite <- Ebl3. apply Permutation_sym. exact HPerm3. }
assert (Hraw4 : In (raw, RAW_SIZE) (ablocks B ly4 S4)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm4|]; exact Hraw_in).
assert (Hing4 : In (g, CGIF_SIZE) (ablocks B ly4 S4)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm4|]; exact Hing).
destruct (al_layout _ _ LAWS _ _ _ _ _ ly4 HAR (proj1 (proj2 HJ4))) as (_ & EFA4 & _).
assert (Hfin4 : In (1, fpos) (frames S4)) by (rewrite Hfrs4; exact Hfin3).
assert (Hfrs4' : frames S4 = (1, fpos) :: frames S) by (rewrite Hfrs4; exact Hfrs3).
frame_pres HJ4 Hfin4 EFA4 F HFp4 HFSp4.
aconstsA HROD HJ4 Kgot4 Kcell4 Kguar4 Kuar4 Vgr4.
assert (HEr : forall a, F <= a < F + 128 -> ~ (bb <= a < bb + req_size Lbb)) by (intros a Ha; clear - Ha HdBF HLbb; unbox; lia).
assert (HErS : forall a, SB + F / 8 <= a < SB + F / 8 + 16 -> ~ (bb <= a < bb + req_size Lbb)) by (intros a Ha; clear - Ha Hbbh Hbbh_ia HF8lo HFceil HFq HF8 C1 C3; unfold SB in *; zone_lia).
reseat HS HJ4 HP4 [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15]%nat AG
ltac:(idtac; first [ lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 11%nat) _ _ _ _ _) =>
eapply (region_kept_frame_aj trasegs _); [exact HK | evalE AG | exact HfinS3 | rwEFA; lia | rwEFA; lia | lia
| intros a Ha Hn; clear - Ha Hn HdBC Hflo Hfhi; unbox; lia] end
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 32%nat) _ _ _ _ _) =>
eapply (region_kept_block_aj trasegs _); [exact HK | evalE AG | exact Hing3 | lia | change (req_size CGIF_SIZE) with 96; lia | lia
| intros a Ha Hn; clear - Ha Hn HdBG; unbox; lia] end
| keptRA HK HJ4 AG Usp E11 E32 HfinS3 Hing3 Kgot3 Kgot4 Kcell3 Kcell4 Kguar3 Kguar4 Kuar3 Kuar4 Vgr3 Vgr4
| keptFA2 HK AG RF E70 Hfin3 HFp4 HFSp4 HEr HErS F
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 10%nat) _ _ _ _ _) =>
eapply (region_kept_block_ajw2 trasegs B LAWS); [exact HK | exact HAR4 | exact Hraw4 | evalE AG | exact Hraw3 | lia | change (req_size RAW_SIZE) with 48; lia | lia | lia
| intros a Ha Hn; clear - Ha Hn HdBR; unbox; lia] end
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
relowC HS AG E10 E11 E32 E10n E11n E32n. norm_ss HS. reshok_bx HS 40%nat.
aj_run_to_tok tratbl_lib_ok HS HJ4 SHOK RABspan 0x8942c.
all: try (obl_blk HJ4 E10n E40 Hraw4).
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrRA AG fpos F EFA4.
clear_frames.
match type of HS with st_ok _ _ ?ssx _ => idtac "H-X1" ssx end.
rebaseE HS AG HEv. clear HEv.
ra_join HS ss_X1 900%nat ra_deads_X ltac:(idtac).
ra_hand RX HS. split; [rewrite HEV; clear - Hk3; lia | exact HPerm4].
Qed.
Lemma ra_H : ra_from B ss_X1 (INV_X B) -> ra_from B ss_G3 (INV_T0 B).
Proof. exact ra_H_aux. Qed.
End c.
End b.
