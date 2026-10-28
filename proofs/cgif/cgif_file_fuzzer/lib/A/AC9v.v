(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI08 YI0n.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0y YC4a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC80 YC1f YC1g YC1h YC81 YC4b YC44 YC44.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACbk AC8a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC8h AC8j ACbc ACbf ACbd ACab ACam ACai ACaj ACak ACal ACan ACag.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YE00 YE01 YI00 YI0j YI0k.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACah.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC5d YC7z YC7y YC85 YC88.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACb6 ACba AC9z ACa3 ACa4 ACa5 ACa6 ACa7 ACa8.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Context {PI : PAImg lib_asan3_1_listing}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ lib_asan3_1_listing PI) (@pa_relro_lo _ lib_asan3_1_listing PI) (@pa_relro_hi _ lib_asan3_1_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_1_listing PI).
#[local] Notation VAL := (@pa_val _ lib_asan3_1_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_asan3_1_listing PI).
#[local] Notation BASE := (@pa_val _ lib_asan3_1_listing PI A_TEXT).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Lemma ra_awr_byte_ly : forall STK sp0 FP bl0 blc ly ly' own a,
(forall cid pos, frame_addr ly' cid pos = frame_addr ly cid pos) ->
awr_byte STK sp0 FP bl0 blc ly own a -> awr_byte STK sp0 FP bl0 blc ly' own a.
Proof.
intros STK sp0 FP bl0 blc ly ly' own a Efa [H | [H | [H | (cid & pos & Hin & H)]]]; [left; exact H | right; left; exact H | right; right; left; exact H |].
right. right. right. exists cid, pos. split; [exact Hin|]. rewrite !Efa. exact H.
Qed.
Ltac aview_kept_rng HFr AG lo hi Hn :=
lazymatch type of HFr with frame_of ?Ef ?rs (mrestrict ?Hh ?m0) (mrestrict _ (ms_mem ?msX)) =>
assert (Hn : forall a, lo <= a < hi -> aview SEGS Hh (ms_mem msX) a = aview SEGS Hh m0 a);
[ let a := fresh "a" in let Ha := fresh "Ha" in
intros a Ha; eapply (aview_kept_out Ef rs _ _ _ HFr); [lia|];
let rg := fresh "rg" in let Hin := fresh "Hin" in let Hrg := fresh "Hrg" in
intros (rg & Hin & Hrg);
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In rg rs1) in Hin end; cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrg; revert Hrg; evalE AG; intros Hrg; lia|]);
destruct Hin
| ] end.
Section f.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AFREE : afree_realizes SEGS B.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL. Let HBfree := pal_free B TL. Let HBmalloc := pal_malloc B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_asan3_1) (PI := PI).
Let PBASE := @pa_B_ok _ _ PI. Let PBLO := @pa_base_lo _ _ PL_asan3_1 PI.
Hypothesis TLF : PALibF B.
Hypothesis HGOT9 : forall (H : word -> bool) mem, arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS H mem) ->
val_mem SEGS (mrestrict H mem) (VAL (A_OBJ 9)) 8 (BASE + AF_asan3_cgif_raw_addframe).
Variable CTX : list (list Z).
Hypothesis HDEEP : forall c, In c CTX -> (2 <= length c)%nat.
Variable KS : asink_syms.
Hypothesis AIL : asink_img_laws SEGS B KS.
Variable MT : ameter_ops.
Hypothesis MLAW : ameter_laws MT.
Hypothesis MLAWF : ameter_fs_laws MT.
Variable XN : xnums.
Hypothesis HXM : forall N idl, 1 <= N <= 100000000 -> 2 <= idl <= 256 -> mo_malloc MT N + xm_lzw XN N idl + 2 * mo_free MT <= xm_rawadd XN N.
Hypothesis HXN : forall N idl, 1 <= N <= 100000000 -> 2 <= idl <= 256 -> mo_malloc MT N + xn_lzw XN N idl + 2 * mo_free MT <= xn_rawadd XN N.
Hypothesis HXMN : forall N idl, 1 <= N <= 100000000 -> 2 <= idl <= 256 -> 0 <= xn_lzw XN N idl <= xm_lzw XN N idl.
Hypothesis AFREE4 : afree04_rule SEGS B MT.
Hypothesis HTR : forall (pcf ra : Z) (regsT regs : bvmap 5 word) ch,
In (raZ regs :: spine ch) CTX -> raZ regsT = ra ->
((pcf = pc_free_ra0 (as_code B) /\ ra = BASE + 0xda0) \/ (pcf = pc_free_ra0 (as_code B) /\ ra = BASE + 0x10ac) \/
(pcf = pc_malloc_ra0 (as_code B) /\ ra = BASE + 0xb08)) ->
In (call_trace0 pcf regsT ((spZ regs, raZ regs, s0Z regs) :: ch)) (as_universe B).
Let RUNP := SRr_run_pi_AJ B LAWS. Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
Lemma ra_MX_aux : ra_fromX0 KS MT XN B CTX ss_T0X (INV_T0X MT XN B) -> ra_fromX0 KS MT XN B CTX ss_TfX (INV_TfX MT XN B) -> ra_fromX0 KS MT XN B CTX ss_MX (INV_MX MT XN B).
Proof.
intros RT0 RTF. ra_preludeX.
pose proof HINV as ((Hk3 & (K1 & EK & HK1r & HK1s) & (pI & res & E859 & E963 & HpI4096 & HpI3 & TpI & Hdisj)) & HXC & ((E661 & HXK) & EICL) & HXLZ & HMET).
xk1 HXK EK HK1r HK1v.
destruct HXLZ as (resx & E963x & Hres05 & HXok & HXnone).
assert (Eresx : resx = res).
{ rewrite E963 in E963x. apply (f_equal bv_unsigned) in E963x. rewrite !unsigned_lit_small in E963x by (clear - Hres05 Hdisj; lia). symmetry. exact E963x. }
subst resx. clear E963x.
destruct HMET as (acc & MLE3 & Hacc0 & HaccM & HaccN). cbn [c_S c_w c_h] in MLE3, HaccM, HaccN. pose proof (mo_free_nonneg MT MLAW) as Qf.
assert (HnP32 : h * w < 2 ^ 32) by (clear - HnP; lia). assert (HnP1 : 1 <= h * w) by (clear - Hw Hh; nia).
assert (Hrq : req_size (h * w) = h * w) by (unfold req_size; destruct (Z.eqb_spec (h * w) 0); [exfalso; clear - HnP1 e; lia | reflexivity]).
assert (HP3 : exists pre, Permutation (ablocks B ly3 S3) (pre ++ (pI, h * w) :: (raw, RAW_SIZE) :: (g, CGIF_SIZE) :: (img, Nimg) :: rest)).
{ destruct Hdisj as [(_ & bb & Lbb & M & HP & _) | (_ & HP)]; [exists [(bb, Lbb)] | exists []]; cbn [app];
(eapply Permutation_trans; [exact HP|]); [apply perm_skip|];
(eapply Permutation_trans; [apply Permutation_sym; apply Permutation_cons_append|]); apply perm_skip; exact HPerm. }
destruct HP3 as (pre & HP3).
assert (Hraw3 : In (raw, RAW_SIZE) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HP3|]; apply in_app_iff; right; right; left; reflexivity).
assert (Hing3 : In (g, CGIF_SIZE) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HP3|]; apply in_app_iff; right; right; right; left; reflexivity).
assert (Hpf3 : In (pf, FILE_BLOCK) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HP3|]; apply in_app_iff; right; right; right; right; right; exact Hpf_rest).
ra_blocks3X Hraw3 Hing3 Hpf3. fold F in HdFR, HdFG.
destruct (al_blocks _ _ LAWS _ _ _ _ _ pI (h * w) HAR3 HpI3) as (Hn16 & _ & Hnceil & Hnh_ia & Hnpres & _). pose proof (proj1 Hnh_ia) as Hnh. rewrite Hrq in Hnceil, Hnpres, Hnh_ia.
pose proof (blk_off_imgP _ _ _ _ _ _ _ _ HAR3 HpI3) as Hnh_img.
pose proof (sep_blocks_perm SEGS B LAWS _ _ _ _ _ (pI, h * w) (raw, RAW_SIZE) _ HAR3 ltac:(eapply Permutation_trans; [exact HP3 | apply (Permutation_app_comm pre ((pI, h * w) :: (raw, RAW_SIZE) :: (g, CGIF_SIZE) :: (img, Nimg) :: rest))])) as HdPR.
pose proof (sep_blocks_perm SEGS B LAWS _ _ _ _ _ (pI, h * w) (g, CGIF_SIZE) _ HAR3
ltac:(eapply Permutation_trans; [exact HP3 | eapply Permutation_trans; [apply (Permutation_app_comm pre ((pI, h * w) :: (raw, RAW_SIZE) :: (g, CGIF_SIZE) :: (img, Nimg) :: rest)) | cbn [app]; apply perm_skip; apply perm_swap]])) as HdPG.
unfold zdisjoint, block_rng in HdPR, HdPG. cbn [fst snd] in HdPR, HdPG. rewrite Hrq in HdPR, HdPG.
change (req_size RAW_SIZE) with 48 in HdPR. change (req_size CGIF_SIZE) with 96 in HdPG.
pose proof (sep_block_frame SEGS B LAWS ly3 S3 _ _ _ pI (h * w) 1 fpos HAR3 HpI3 Hfin3) as HdPF.
unfold zdisjoint in HdPF. cbn [fst snd] in HdPF. rewrite Hrq in HdPF. change (fs_frame_bytes 1) with 128 in HdPF. rewrite EFA3 in HdPF. fold F in HdPF.
pose proof (sep_block_frame SEGS B LAWS ly3 S3 _ _ _ pI (h * w) cid pos HAR3 HpI3 HfinS3) as HdPC.
unfold zdisjoint in HdPC. cbn [fst snd] in HdPC. rewrite Hrq in HdPC. rewrite EFA3 in HdPC.
box HdPR. box HdPG. box HdPF. box HdPC.
relowC HS AG E10 E11 E32 E10n E11n E32n.
pose proof HJ3 as (_ & _ & _ & _ & _ & _ & Hnev3 & _ & _ & _ & _ & _ & _ & HJpres & _).
reshok_bx HS 40%nat.
paj_run_tok RUN HS HJ3 SHOK RABspan.
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrRA AG fpos F EFA3.
upd_aboveW HUP HFr AG. aview_kept_rng HFr AG (spZ regs - 120) (spZ regs - 108) HR1. xframe_wins HFr AG HRW1. clear HF HFr HG.
clear Kgot3 Kcell3 Kguar3 Kuar3 Vgr3. aconstsA HROD HJ3 Kgot3 Kcell3 Kguar3 Kuar3 Vgr3.
prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp. prreg HS (8%bv : bv 5) Rs0.
prreg HS (10%bv : bv 5) Ra0. rewrite E859 in Ra0.
lazymatch type of AG with forall n, _ -> ew ?Ebase n = _ => assert (Usp3 : bv_unsigned (ew Ebase 2) = spZ regs) by (rewrite (AG 2%nat) by lia; exact Usp) end.
assert (Hchne : ch <> []) by (intros Hn; pose proof (HDEEP _ Hctx) as Hdeep; rewrite Hn in Hdeep; cbn in Hdeep; clear - Hdeep; lia).
pose proof Hch as Hch'. destruct Hch' as [(_ & Hn) | (Qs0lo & Qs0hi & Qs0al & _ & _)]; [exfalso; exact (Hchne Hn)|].
assert (Qtop64 : ly_top ly <= 2 ^ 64) by lia.
assert (Qra : 0 <= raZ regs < 2 ^ 64) by (unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq).
assert (Qs0 : 0 <= s0Z regs < 2 ^ 64) by (unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq).
assert (Qal8 : spZ regs mod 8 = 0) by (pose proof (Z.div_mod (spZ regs) 32 ltac:(lia)) as D; rewrite Hal32, Z.add_0_r in D; rewrite D; replace (32 * (spZ regs / 32)) with ((4 * (spZ regs / 32)) * 8) by lia; apply Z_mod_mult).
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let ih := idx_of_base_lo rs 2%nat (-104) in let ih := eval vm_compute in ih in
let rh := eval vm_compute in (nth ih rs got_regionP) in
pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H W3) msX) ih rh HS ltac:(vm_compute; reflexivity)) as HRstk; cbn [ms_mem restrict] in HRstk;
lazymatch type of HRstk with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-8) 8%N (SOff 1 0) (raZ regs) HRstk
Usp3 ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 1%nat) by lia; rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vra;
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-16) 8%N (SOff 8 0) (s0Z regs) HRstk
Usp3 ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 8%nat) by lia; rewrite (EE 8%nat 8%bv eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vs0 end;
clear HRstk;
assert (Hch1 : achain ly3 (aview SEGS (w_H W3) (ms_mem msX)) (spZ regs - 320) (spZ regs) ((spZ regs, raZ regs, s0Z regs) :: ch));
[ apply (achain_ly_top ly); [pose proof (proj1 (proj2 HJ3)) as LY; destruct LY as (_ & _ & _ & _ & _ & _ & _ & _ & LT & _); exact LT|];
replace (spZ regs + -8) with (spZ regs - 8) in Vra by lia; replace (spZ regs + -16) with (spZ regs - 16) in Vs0 by lia;
exact (achain_push ly _ _ (spZ regs) (s0Z regs) (raZ regs) _ (spZ regs - 320) Hch Qtop64 HUP
(rdword_of_val_mem SEGS _ _ _ _ Vra Qra) (rdword_of_val_mem SEGS _ _ _ _ Vs0 Qs0) Hra4 ltac:(clear - Hceil Hslo Hstk0 FFS; lia) Qal8
ltac:(clear - Qs0lo Qs0hi; lia) ltac:(clear - PBASE PBLO; lia))
| ] | st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let ih := idx_of_base_lo rs 2%nat (-104) in let ih := eval vm_compute in ih in
let rh := eval vm_compute in (nth ih rs got_regionP) in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3) msX) ih rh HS ltac:(vm_compute; reflexivity)) as HRstk; cbn [ms_mem restrict] in HRstk;
lazymatch type of HRstk with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-8) 8%N (SOff 1 0) (raZ regs) HRstk
Usp3 ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 1%nat) by lia; rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vra;
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-16) 8%N (SOff 8 0) (s0Z regs) HRstk
Usp3 ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 8%nat) by lia; rewrite (EE 8%nat 8%bv eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vs0 end;
clear HRstk;
assert (Hch1 : achain ly3 (aview SEGS (w_H W3) (ms_mem msX)) (spZ regs - 320) (spZ regs) ((spZ regs, raZ regs, s0Z regs) :: ch));
[ apply (achain_ly_top ly); [pose proof (proj1 (proj2 HJ3)) as LY; destruct LY as (_ & _ & _ & _ & _ & _ & _ & _ & LT & _); exact LT|];
replace (spZ regs + -8) with (spZ regs - 8) in Vra by lia; replace (spZ regs + -16) with (spZ regs - 16) in Vs0 by lia;
exact (achain_push ly _ _ (spZ regs) (s0Z regs) (raZ regs) _ (spZ regs - 320) Hch Qtop64 HUP
(rdword_of_val_mem SEGS _ _ _ _ Vra Qra) (rdword_of_val_mem SEGS _ _ _ _ Vs0 Qs0) Hra4 ltac:(clear - Hceil Hslo Hstk0 FFS; lia) Qal8
ltac:(clear - Qs0lo Qs0hi; lia) ltac:(clear - PBASE PBLO; lia))
| ]  end.
pmkst HS.
ppcs.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) ?mdX) _ =>
eapply (AFREE4 W3 (ms_regs msX) (ms_mem msX) TRAWADD_STK (spZ regs) [(raw + 40, raw + 44)] ly S W mem md [(1, fpos)]
ly3 S3 mdX k pI (h * w) (-320) (Z_to_bv 64 (BASE + 0xda0)) ((spZ regs, raZ regs, s0Z regs) :: ch) HJ3 HpI3) end.
- exact Ra0.
- unfold spZ at 1. rewrite Rsp, Usp3, unsigned_lit_small by (clear - Hceil Hslo Hstk0 FFS Hshi H47 C1; lia). clear; lia.
- reflexivity. - clear; lia. - rewrite FFS. unfold ASTACK. clear; lia.
- rewrite Rgp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 3%nat) by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
- rewrite Rtp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 4%nat) by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
- exact Rra.
- apply ret_ok_codeptr_v; [lia | reflexivity].
- rewrite HEV in Hev. clear - Hnev3 Hk3 Hev. lia.
- apply (achain_chain_pre ly3 _ (spZ regs - 320) (spZ regs) _ _ Hch1);
[ unfold spZ at 1 2; rewrite Rsp, Usp3, unsigned_lit_small by (clear - Hceil Hslo Hstk0 FFS Hshi H47 C1; lia); clear - Hceil Hslo Hstk0 FFS C1; lia
| unfold s0Z; rewrite Rs0; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact Usp3
| unfold raZ; rewrite Rra, unsigned_lit_small by (clear - PBASE PBLO; lia); clear - PBASE PBLO; lia ].
- apply (HTR (pc_free_ra0 (as_code B)) (BASE + 0xda0)); [exact Hctx | unfold raZ; rewrite Rra; apply unsigned_lit_small; clear - PBASE PBLO; lia | left; split; reflexivity].
- intros Hin i Hi. exact (TpI Hin i Hi).
-
eapply (mok_station MT S S3 _ acc); [exact MLAW | exact HMOK | exact MLE3 | exact Qf | clear - HaccM Qf; lia]. }
cbv beta. intros W4 c4 _ (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HP4 & (l1 & l2 & Ebl3 & Ebl4) & Hfrs4 & HK & MLE4).
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
assert (HErS : forall a, SB + F / 8 <= a < SB + F / 8 + 16 -> ~ (pI <= a < pI + req_size (h * w))) by (rewrite Hrq; intros a Ha; clear - Ha Hnh Hnh_ia Hrq HF8lo HFceil HFq HF8 C1 C3; unfold SB in *; zone_lia).
reseat HS HJ4 HP4 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13]%nat AG
ltac:(idtac; first [ lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 11%nat) _ _ _ _ _) =>
eapply (region_kept_frame_aj SEGS _); [exact HK | evalE AG | exact HfinS3 | rwEFA; lia | rwEFA; lia | lia
| rewrite Hrq; intros a Ha Hn; clear - Ha Hn HdPC Hflo Hfhi; unbox; lia] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 32%nat) _ _ _ _ _) =>
eapply (region_kept_block_aj SEGS _); [exact HK | evalE AG | exact Hing3 | lia | change (req_size CGIF_SIZE) with 96; lia | lia
| rewrite Hrq; intros a Ha Hn; clear - Ha Hn HdPG; unbox; lia] end
| keptRA HK HJ4 AG Usp E11 E32 HfinS3 Hing3 Kgot3 Kgot4 Kcell3 Kcell4 Kguar3 Kguar4 Kuar3 Kuar4 Vgr3 Vgr4
| keptFA2 HK AG RF E529 Hfin3 HFp4 HFSp4 HEr HErS F
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 10%nat) _ _ _ _ _) =>
eapply (region_kept_block_ajw2 SEGS B LAWS); [exact HK | exact HAR4 | exact Hraw4 | evalE AG | exact Hraw3 | lia | change (req_size RAW_SIZE) with 48; lia | lia | lia
| rewrite Hrq; intros a Ha Hn; clear - Ha Hn HdPR; unbox; lia] end
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
relowC HS AG E10 E11 E32 E10n E11n E32n. norm_ss HS. reshok_bx HS 40%nat.
paj_run_to_tok RUNTO HS HJ4 SHOK RABspan 0xdb8.
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrRA AG fpos F EFA4.
aview_kept_rng HFr AG (spZ regs - 120) (spZ regs - 108) HR2. xframe_wins HFr AG HRW2. clear_frames.
lazymatch type of HR2 with forall a, _ -> aview _ _ (ms_mem ?msY) a = _ =>
lazymatch type of HR1 with forall a, _ -> _ = aview _ _ ?m3 a =>
assert (HR : forall a, spZ regs - 120 <= a < spZ regs - 108 -> aview SEGS (w_H W4) (ms_mem msY) a = aview SEGS (w_H W3) m3 a)
by (intros a Ha; rewrite (HR2 a Ha); pose proof HK as (HK1 & _); rewrite (HK1 a) by (clear - Ha Hceil Hslo Hstk0 Hshi H47 FFS C1; lia); apply HR1; exact Ha) end end.
clear HR1 HR2.
destruct Hdisj as [(Hres0 & bb & Lbb & M & HPerm3 & Hbb4096 & HM & Abb & Tbb & Vbb & VM) | (Hres25 & HPerm3)].
2: assert (Hres5 : res = 5) by (clear - Hres25 Hres05; lia).
+
assert (HPerm4 : Permutation (ablocks B ly4 S4) ((bb, Lbb) :: ablocks B ly S)).
{ rewrite Ebl4. rewrite <- (app_nil_r ((bb, Lbb) :: ablocks B ly S)). apply (Permutation_app_inv l1 l2 ((bb, Lbb) :: ablocks B ly S) [] (pI, h * w)). rewrite <- Ebl3. exact HPerm3. }
assert (Hbb4 : In (bb, Lbb) (ablocks B ly4 S4)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm4|]; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bb Lbb HAR4 Hbb4) as (Hbb16 & _ & Hbbceil & Hbbh_ia & Hbbpres & _). pose proof (proj1 Hbbh_ia) as Hbbh.
pose proof (blk_off_imgP _ _ _ _ _ _ bb Lbb HAR4 Hbb4) as Hbbh_img.
pose proof (req_size_pos Lbb ltac:(clear - HM; lia)) as [_ HLbb].
destruct (al_blocks _ _ LAWS _ _ _ _ _ bb Lbb HAR4 Hbb4) as (_ & _ & _ & _ & _ & _ & HLbbmax).
assert (HM32 : 0 <= M < 2 ^ 32) by (clear - HM HLbbmax; unfold MALLOC_MAX in HLbbmax; lia).
pose proof (HXok Hres0 bb M Vbb VM ltac:(clear - Hbb4096 Hbbceil HLbb HM C1; lia) HM32) as [HVOK HM16].
pose proof (sep_block_frame SEGS B LAWS ly4 S4 _ _ _ bb Lbb 1 fpos HAR4 Hbb4 Hfin4) as HdBF.
unfold zdisjoint in HdBF. cbn [fst snd] in HdBF. change (fs_frame_bytes 1) with 128 in HdBF. rewrite EFA4 in HdBF. fold F in HdBF.
pose proof (asep_head B LAWS ly4 S4 _ _ _ (bb, Lbb) (raw, RAW_SIZE) _ HAR4 HPerm4 Hraw_in) as HdBR.
unfold zdisjoint, block_rng in HdBR. cbn [fst snd] in HdBR. change (req_size RAW_SIZE) with 48 in HdBR.
lazymatch type of HRW1 with forall x, _ -> _ -> aview _ _ (ms_mem ?msq) x = aview _ _ (ms_mem ?ms0) x =>
assert (HRb1 : forall a, bb <= a < bb + req_size Lbb -> aview SEGS (w_H W3) (ms_mem msq) a = aview SEGS (w_H W3) (ms_mem ms0) a)
by (intros a Ha; apply HRW1; [clear - Ha Hbb4096 Hbbceil C1; lia | cbn; clear - Ha HdBF HdBR Hbbceil Hceil Hslo Hstk0 FFS C1 PBASE PBLO; unbox; lia]) end.
rename HdBR into HdBR'. clear HRW1.
assert (Hbb3 : In (bb, Lbb) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HP34|]; right; exact Hbb4).
pose proof (sep_blocks_perm SEGS B LAWS _ _ _ _ _ (pI, h * w) (bb, Lbb) _ HAR3 ltac:(eapply Permutation_trans; [exact HP34 | apply perm_skip; exact HPerm4])) as HdPB.
unfold zdisjoint, block_rng in HdPB. cbn [fst snd] in HdPB. rewrite Hrq in HdPB.
lazymatch type of HVOK with lzw_vokA _ ?idlv ?iclv ?pixv (mrestrict _ (ms_mem ?ms3v)) _ _ =>
assert (HGout4 : exists out, YO07.lzw_stream idlv iclv pixv = Some out /\ garr8 SEGS (mrestrict (w_H W4) mem4) bb out /\ M = Z.of_nat (length out));
[ destruct HVOK as (out & Hls & HGout & HMout); exists out; split; [exact Hls|]; split; [| exact HMout];
pose proof HK as (HK1 & (HK2 & _));
apply (garr8_aview_kept SEGS (w_H W3) (w_H W4) (ms_mem ms3v) mem4 bb out); [| exact HGout];
let a := fresh "a" in let Ha := fresh "Ha" in
intros a Ha; rewrite <- HMout in Ha; replace a with (bb + (a - bb)) by (clear; lia);
rewrite (HK2 bb Lbb (a - bb) Hbb3 ltac:(clear - Ha HM HLbb; lia) ltac:(clear - Ha HM HLbb HdPB Hrq; lia));
replace (bb + (a - bb)) with a by (clear; lia); apply HRb1; clear - Ha HM HLbb; lia | ] end.
clear HRb1 HdPB.
pose proof (val_mem_kept SEGS _ _ _ _ (spZ regs - 120) 8 bb ltac:(intros kk Hkk; apply HR; clear - Hkk; lia) Vbb) as Vbb'.
pose proof (val_mem_kept SEGS _ _ _ _ (spZ regs - 120 + 8) 4 M ltac:(intros kk Hkk; apply HR; clear - Hkk; lia) VM) as VM'.
clear Vbb VM HR.
prreg HS (21%bv : bv 5) Qs5. rewrite E963, Hres0 in Qs5.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_pin_reg' Ev ssv msv (21%bv : bv 5) 0 HS ltac:(cbn [ms_regs restrict mkst]; exact Qs5) eq_refl) as HS3 | st_ok _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_pin_reg' Ev ssv msv (21%bv : bv 5) 0 HS ltac:(cbn [ms_regs restrict mkst]; exact Qs5) eq_refl) as HS3  end.
clear HS Qs5. rename HS3 into HS. norm_ss HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_havoc_hi 1059 Ev ssv msv [Z_to_bv 64 bb; Z_to_bv 64 (M mod 2 ^ 32)] HS ltac:(vm_compute; reflexivity)) as HS3 | st_ok _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_havoc_hi 1059 Ev ssv msv [Z_to_bv 64 bb; Z_to_bv 64 (M mod 2 ^ 32)] HS ltac:(vm_compute; reflexivity)) as HS3  end.
clear HS. rename HS3 into HS. rebaseE HS AG HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (E1059 : ew Ev 1059 = Z_to_bv 64 bb) by (rewrite HEv; exact (ew_havoc_new _ 1059 [Z_to_bv 64 bb; Z_to_bv 64 (M mod 2 ^ 32)] 0 (Z_to_bv 64 0) ltac:(cbn; lia)));
assert (E1060 : ew Ev 1060 = Z_to_bv 64 (M mod 2 ^ 32)) by (rewrite HEv; exact (ew_havoc_new _ 1059 [Z_to_bv 64 bb; Z_to_bv 64 (M mod 2 ^ 32)] 1 (Z_to_bv 64 0) ltac:(cbn; lia))) | st_ok _ ?Ev _ _ =>
assert (E1059 : ew Ev 1059 = Z_to_bv 64 bb) by (rewrite HEv; exact (ew_havoc_new _ 1059 [Z_to_bv 64 bb; Z_to_bv 64 (M mod 2 ^ 32)] 0 (Z_to_bv 64 0) ltac:(cbn; lia)));
assert (E1060 : ew Ev 1060 = Z_to_bv 64 (M mod 2 ^ 32)) by (rewrite HEv; exact (ew_havoc_new _ 1059 [Z_to_bv 64 bb; Z_to_bv 64 (M mod 2 ^ 32)] 1 (Z_to_bv 64 0) ltac:(cbn; lia)))  end.
clear HEv.
pose proof HJ4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres4' & _).
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _
(YP09.mkRegion (Some 2%nat) (-120) (-104) (-120) (-104) [YP09.mkChunk (-120) (CVal 8 (SOff 1059 0)); YP09.mkChunk (-112) (CVal 4 (SOff 1060 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
evalE AG; split; [lia|]; split; [lia|]; split;
[ intros o Ho; apply (apresent_writable SEGS); apply Hpres4'; rewrite FFS; lia
| apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ (spZ regs) (-120) 8 _ bb);
[cbn [sv_denot]; rewrite E1059, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | replace (spZ regs + -120) with (spZ regs - 120) by lia; exact Vbb']|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ (spZ regs) (-112) 4 _ (M mod 2 ^ 32));
[cbn [sv_denot]; rewrite E1060, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| pose proof (Z.mod_pos_bound M (2 ^ 32) ltac:(lia)); zside | zside
| replace (spZ regs + -112) with (spZ regs - 120 + 8) by lia; apply val_mem_mod4; exact VM']|];
apply Forall_nil ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
evalE AG; unfold CGIF_SIZE; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS | st_ok _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _
(YP09.mkRegion (Some 2%nat) (-120) (-104) (-120) (-104) [YP09.mkChunk (-120) (CVal 8 (SOff 1059 0)); YP09.mkChunk (-112) (CVal 4 (SOff 1060 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
evalE AG; split; [lia|]; split; [lia|]; split;
[ intros o Ho; apply (apresent_writable SEGS); apply Hpres4'; rewrite FFS; lia
| apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ (spZ regs) (-120) 8 _ bb);
[cbn [sv_denot]; rewrite E1059, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | replace (spZ regs + -120) with (spZ regs - 120) by lia; exact Vbb']|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ (spZ regs) (-112) 4 _ (M mod 2 ^ 32));
[cbn [sv_denot]; rewrite E1060, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| pose proof (Z.mod_pos_bound M (2 ^ 32) ltac:(lia)); zside | zside
| replace (spZ regs + -112) with (spZ regs - 120 + 8) by lia; apply val_mem_mod4; exact VM']|];
apply Forall_nil ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
evalE AG; unfold CGIF_SIZE; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS  end.
ra_join HS ss_T0X 1061%nat ra_deads_T0 ltac:(idtac).
ra_handX RT0 HS.
split; [| split; [exact HXC | split; [| split]]].
{ split; [clear - Hk3; lia|].
split; [exists K1; split; [rewrite !ew_havoc_old by (clear - PBASE PBLO; lia); exact EK | split; [exact HK1r | exact HK1s]]|].
exists bb, Lbb, M. split; [rewrite !ew_havoc_old by (clear - PBASE PBLO; lia); exact E1059|]. split; [rewrite !ew_havoc_old by (clear - PBASE PBLO; lia); exact E1060|].
split; [exact HPerm4|]. split; [exact Hbb4096|]. split; [exact HM|].
split; [| exact Tbb].
intros blc i Hb Hi. apply (ra_awr_byte_ly _ _ _ _ _ ly3 ly4); [intros c p; rewrite EFA4, EFA3; reflexivity | exact (Abb blc i Hb Hi)]. }
{   pose proof HK1v as HK1w; unfold xfacts in HK1w.
split; [split; [rewrite !ew_havoc_old by (clear - PBASE PBLO; lia); exact E661
| intros Hne'; rewrite !ew_havoc_old by (clear - PBASE PBLO; lia); rewrite EK, (HK1w Hne'); reflexivity]
| rewrite !ew_havoc_old by (clear - PBASE PBLO; lia); exact EICL]. }
{
destruct HGout4 as (out & Hls & HGout & HMout). exists out. split; [exact Hls|].
lazymatch goal with |- garr8 _ (mrestrict _ (ms_mem ?msY)) _ _ /\ _ =>
assert (HGout5 : garr8 SEGS (mrestrict (w_H W4) (ms_mem msY)) bb out)
by (apply (garr8_aview_kept SEGS (w_H W4) (w_H W4) mem4 (ms_mem msY) bb out); [| exact HGout];
intros a Ha; rewrite <- HMout in Ha; apply HRW2; [clear - Ha Hbb4096 Hbbceil HLbb HM C1; lia
| cbn; clear - Ha HM HLbb HdBF HdBR' Hbbceil Hceil Hslo Hstk0 FFS C1 PBASE PBLO; lia]) end.
rewrite !ew_havoc_old by (clear - PBASE PBLO; lia). rewrite E1059, E1060. rewrite (Z.mod_small M) by (clear - HM HLbb HLbbmax; unfold MALLOC_MAX in HLbbmax; lia).
rewrite !unsigned_lit_small by (first [clear - HM HLbb HLbbmax; unfold MALLOC_MAX in HLbbmax; lia | clear - Hbb4096 Hbbceil HLbb HM C1; lia]).
split; [exact HGout5 | split; [exact HMout | cbn [c_w c_h] in HM16 |- *; clear - HM16 HMout; lia]]. }
{   exists (acc + mo_free MT). split; [exact (mle_station MT _ _ _ _ _ MLAW MLE3 MLE4)|].
cbn [c_w c_h]. clear - Hacc0 HaccM HaccN Qf. lia. }
+
clear HR.
assert (HPerm4 : Permutation (ablocks B ly4 S4) (ablocks B ly S)).
{ rewrite Ebl4. rewrite <- (app_nil_r (ablocks B ly S)). apply (Permutation_app_inv l1 l2 (ablocks B ly S) [] (pI, h * w)). rewrite <- Ebl3. exact HPerm3. }
prreg HS (21%bv : bv 5) Qs5.
ra_join HS ss_TfX 1061%nat ra_deads_Tf
ltac:(idtac; ra_join_val HS 1061%nat 16%nat Qs5 Eres;
ra_join_fact HS 1077%nat (mkAF 2 5 0) ltac:(rewrite Eres, E963, unsigned_lit_small by (clear - Hres25; lia); rewrite Z.pow_0_r, Z.mod_1_r; clear - Hres25; lia)).
ra_handX RTF HS.
split; [| split; [exact HXC | split; [| split]]].
{ split; [clear - Hk3; lia|].
split; [exists K1; split; [rewrite !ew_havoc_old by (clear - PBASE PBLO; lia); exact EK | split; [exact HK1r | exact HK1s]]|].
exact HPerm4. }
{   rewrite Eres, E963. rewrite Hres5. reflexivity. }
{ exact (HXnone Hres5). }
{   exists (acc + mo_free MT). split; [exact (mle_station MT _ _ _ _ _ MLAW MLE3 MLE4)|].
cbn [c_w c_h]. clear - Hacc0 HaccM HaccN Qf. lia. }
Qed.
Lemma ra_MX : ra_fromX0 KS MT XN B CTX ss_T0X (INV_T0X MT XN B) -> ra_fromX0 KS MT XN B CTX ss_TfX (INV_TfX MT XN B) -> ra_fromX0 KS MT XN B CTX ss_MX (INV_MX MT XN B).
Proof. exact ra_MX_aux. Qed.
End f.
End d.
End b.
