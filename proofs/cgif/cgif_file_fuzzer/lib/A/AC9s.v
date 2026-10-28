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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC8h AC8j ACbc ACbf ACbd ACab ACam ACai ACaj ACak ACan ACag ACap.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YE00 YE01 YI00 YI0j YI0k.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACah.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC5d YC7z YC7y YC85 YC88.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACb6 ACba AC9z ACa3 ACa4 ACa5 ACa6 ACa7 ACa8 ACa9.
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
Section e.
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
Lemma ra_HX_aux : ra_fromX1 KS MT XN B CTX ss_X1X (INV_XX KS MT XN B 1359) -> ra_fromX1 KS MT XN B CTX ss_G3X (INV_G3X KS MT XN B).
Proof.
intros RX. ra_preludeX.
pose proof HINV as ((Hk3 & (K1 & EK & HK1r & HK1s) & (bb & Lbb & M & E1059 & E1060 & HPerm3 & Hbb4096 & HM & Abb & Tbb)) & HXC & ((E661 & HXK) & EICL) & HLZ & HMET & HSINK).
xk1 HXK EK HK1r HK1v.
assert (Hraw3 : In (raw, RAW_SIZE) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm3|]; right; exact Hraw_in).
assert (Hing3 : In (g, CGIF_SIZE) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm3|]; right; exact Hing).
assert (Hbb3 : In (bb, Lbb) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm3|]; left; reflexivity).
assert (Hpf3 : In (pf, FILE_BLOCK) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm3|]; right; exact Hpf_in).
ra_blocks3X Hraw3 Hing3 Hpf3. fold F in HdFR, HdFG.
destruct (al_blocks _ _ LAWS _ _ _ _ _ bb Lbb HAR3 Hbb3) as (Hbb16 & _ & Hbbceil & Hbbh_ia & Hbbpres & _). pose proof (proj1 Hbbh_ia) as Hbbh.
pose proof (blk_off_imgP _ _ _ _ _ _ bb Lbb HAR3 Hbb3) as Hbbh_img.
pose proof (req_size_pos Lbb ltac:(clear - HM; lia)) as [_ HLbb].
pose proof (sep_blocks_perm SEGS B LAWS _ _ _ _ _ (bb, Lbb) (raw, RAW_SIZE) _ HAR3 ltac:(eapply Permutation_trans; [exact HPerm3 | apply perm_skip; exact HPerm])) as HdBR.
pose proof (sep_blocks_perm SEGS B LAWS _ _ _ _ _ (bb, Lbb) (g, CGIF_SIZE) _ HAR3
ltac:(eapply Permutation_trans; [exact HPerm3 | apply perm_skip; eapply Permutation_trans; [exact HPerm | apply perm_swap]])) as HdBG.
unfold zdisjoint, block_rng in HdBR, HdBG. cbn [fst snd] in HdBR, HdBG. change (req_size RAW_SIZE) with 48 in HdBR. change (req_size CGIF_SIZE) with 96 in HdBG.
pose proof (sep_block_frame SEGS _ LAWS ly3 S3 _ _ _ bb Lbb 1 fpos HAR3 Hbb3 Hfin3) as HdBF.
unfold zdisjoint in HdBF. cbn [fst snd] in HdBF. change (fs_frame_bytes 1) with 128 in HdBF. rewrite EFA3 in HdBF. fold F in HdBF.
pose proof (sep_block_frame SEGS _ LAWS ly3 S3 _ _ _ bb Lbb cid pos HAR3 Hbb3 HfinS3) as HdBC.
unfold zdisjoint in HdBC. cbn [fst snd] in HdBC. rewrite EFA3 in HdBC.
box HdBR. box HdBG. box HdBF. box HdBC.
xbb_intro HPerm3 HLZ. xF8.
relowC HS AG E10 E11 E32 E10n E11n E32n.
pose proof HJ3 as (_ & _ & _ & _ & _ & _ & Hnev3 & _ & _ & _ & _ & _ & _ & HJpres & _).
norm_ss HS. reshok_bx HS 40%nat.
paj_run_tok RUN HS HJ3 SHOK RABspan.
all: try (obl_blk HJ3 E10n E40 Hraw3).
all: try (obl_blk HJ3 E32n E40 Hing3).
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrRA AG fpos F EFA3.
xblk_stretch HFr HGout. xsink_stretch HFr HSINK.
clear_frames.
xicl_facts HS.
wcb_siteAX (13%bv : bv 5) HS HWX HGA HRAX HHVX HJ3 HAR3 Hfin3 HfinS3 Hraw3 Hing3 Hfrs3 EFA3 EFL3 HFpres3 HFSpres3 Hrpres3 Hgpres3 HUP Kgot3 Kcell3 Kguar3 Kuar3 Vgr3.
xW3 W3.
reshok_bx HS 40%nat. relowC HS AG E10 E11 E32 E10n E11n E32n.
paj_run_tok RUN HS HJ3 SHOK RABspan.
all: try (obl_blk HJ3 E10n E40 Hraw3).
all: try (obl_blk HJ3 E32n E40 Hing3).
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrRA AG fpos F EFA3.
xblk_stretch HFr HGout. xsink_stretch HFr HSINK.
clear_frames.
xras_facts.
wcb_siteAX (13%bv : bv 5) HS HWX HGA HRAX HHVX HJ3 HAR3 Hfin3 HfinS3 Hraw3 Hing3 Hfrs3 EFA3 EFL3 HFpres3 HFSpres3 Hrpres3 Hgpres3 HUP Kgot3 Kcell3 Kguar3 Kuar3 Vgr3.
xW3 W3.
reshok_bx HS 40%nat. relowC HS AG E10 E11 E32 E10n E11n E32n.
clear Hnev3. pose proof HJ3 as (_ & _ & _ & _ & _ & _ & Hnev3 & _).
paj_run_tok RUN HS HJ3 SHOK RABspan.
all: try (obl_blk HJ3 E10n E40 Hraw3).
all: try (obl_blk HJ3 E32n E40 Hing3).
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrRA AG fpos F EFA3.
xsink_stretch HFr HSINK.
upd_aboveW HUP HFr AG. clear HF HFr HG.
prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp. prreg HS (8%bv : bv 5) Rs0.
prreg HS (10%bv : bv 5) Ra0. rewrite E1059 in Ra0.
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
clear Kgot3 Kcell3 Kguar3 Kuar3 Vgr3. aconstsA HROD HJ3 Kgot3 Kcell3 Kguar3 Kuar3 Vgr3.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) ?mdX) _ =>
eapply (afree04_sub SEGS B LAWS Hsegs MT AFREE4 W3 (ms_regs msX) (ms_mem msX) TRAWADD_STK (spZ regs) ((raw + 40, raw + 44) :: asink_fp pf) ly S W mem md [(1, fpos)]
ly3 S3 mdX k bb Lbb (-320) (Z_to_bv 64 (BASE + 0x10ac)) ((spZ regs, raZ regs, s0Z regs) :: ch) HJ3 Hbb3) end.
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
- apply (HTR (pc_free_ra0 (as_code B)) (BASE + 0x10ac)); [exact Hctx | unfold raZ; rewrite Rra; apply unsigned_lit_small; clear - PBASE PBLO; lia | right; left; split; reflexivity].
- intros Hin i Hi. destruct (Tbb Hin i Hi) as (r & Hr & Hri). exists r. split; [left; destruct Hr as [<- | []]; reflexivity | exact Hri].
-
destruct HMET as (acc & MLE3 & Hacc0 & HaccM & HaccN). cbn [c_S c_w c_h] in MLE3, HaccM, HaccN. pose proof (mo_free_nonneg MT MLAW) as Qf.
eapply (mok_station MT S S3 _ acc); [exact MLAW | exact HMOK | exact MLE3 | exact Qf | clear - HaccM Qf; lia]. }
cbv beta. intros W4 c4 _ (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HP4 & (l1 & l2 & Ebl3 & Ebl4) & Hfrs4 & HK & MLE4 & HJf).
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
ltac:(idtac; first [ lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 11%nat) _ _ _ _ _) =>
eapply (region_kept_frame_aj SEGS _); [exact HK | evalE AG | exact HfinS3 | rwEFA; lia | rwEFA; lia | lia
| intros a Ha Hn; clear - Ha Hn HdBC Hflo Hfhi; unbox; lia] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 32%nat) _ _ _ _ _) =>
eapply (region_kept_block_aj SEGS _); [exact HK | evalE AG | exact Hing3 | lia | change (req_size CGIF_SIZE) with 96; lia | lia
| intros a Ha Hn; clear - Ha Hn HdBG; unbox; lia] end
| keptRA HK HJ4 AG Usp E11 E32 HfinS3 Hing3 Kgot3 Kgot4 Kcell3 Kcell4 Kguar3 Kguar4 Kuar3 Kuar4 Vgr3 Vgr4
| keptFA2 HK AG RF E529 Hfin3 HFp4 HFSp4 HEr HErS F
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 10%nat) _ _ _ _ _) =>
eapply (region_kept_block_ajw2 SEGS B LAWS); [exact HK | exact HAR4 | exact Hraw4 | evalE AG | exact Hraw3 | lia | change (req_size RAW_SIZE) with 48; lia | lia | lia
| intros a Ha Hn; clear - Ha Hn HdBR; unbox; lia] end
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
relowC HS AG E10 E11 E32 E10n E11n E32n. norm_ss HS. reshok_bx HS 40%nat.
assert (Hpf4 : In (pf, FILE_BLOCK) (ablocks B ly4 S4)).
{ rewrite Ebl4. pose proof Hpf3 as Q. rewrite Ebl3 in Q. apply in_app_iff in Q. apply in_app_iff.
destruct Q as [Q | [Q | Q]]; [left; exact Q | | right; exact Q].
exfalso. injection Q as Epf ELbb. pose proof XBB as XBu. unfold xbfacts in XBu. pose proof (req_size_pos Lbb ltac:(clear - HM; lia)) as [_ Hq].
clear - Epf XBu HM. unfold FILE_BLOCK in *. lia. }
lazymatch type of HSINK with asink_at _ _ ?m3 ?md3 _ ?SGv =>
assert (HSINK4 : asink_at SEGS KS (mrestrict (w_H W4) mem4) md4 pf SGv);
[ eapply (asink_at_kept SEGS B KS AIL); [exact HJf | apply sink_closed_ablocks_fp; constructor; [cbn; clear - Hbb4096; lia | constructor] | exact Hpf3 | exact Hpf4 | | exact HSINK];
intros i Hi HFP; destruct (inFP_ablocks_fp_inv _ _ HFP) as (p' & n' & Hpn & Hpa); destruct Hpn as [Hpn | []]; injection Hpn as <- <-;
pose proof XBB as XBu; unfold xbfacts in XBu; unfold FILE_BLOCK in Hi; clear - Hi Hpa XBu; lia
| clear HSINK; rename HSINK4 into HSINK ] end.
paj_run_to_tok RUNTO HS HJ4 SHOK RABspan 0x10b8.
all: try (obl_blk HJ4 E10n E40 Hraw4).
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrRA AG fpos F EFA4.
xsink_stretch HFr HSINK.
clear_frames.
rebaseE HS AG HEv. clear HEv.
prreg HS (21%bv : bv 5) R21.
slot_val HS (Some 10%nat) 0 40 (Z_to_bv 64 0) ltac:(reflexivity) Qrc.
ra_join_slot HS ss_X1X 1359%nat ra_deads_X (Some 10%nat) 0 40 ltac:(idtac; ra_join_val HS 1359%nat 13%nat R21 EnR; ra_join_val HS 1359%nat 23%nat Qrc EnC).
ra_handX RX HS. split; [split; [rewrite HEV; clear - Hk3; lia | exact HPerm4]|].
lazymatch goal with |- exists code bytes, rx_model ?cxv ?xxv = _ /\ _ =>
exists 0, (rx_gce cxv ++ rx_hdr cxv ++ rx_lctb cxv LCT ++ [rx_iclen cxv - 1] ++ out); split;
[rewrite (rx_model_lzw cxv xxv (proj1 HXC) (proj2 (proj2 HXC))); cbn [x_IMG x_LCT]; rewrite Hls; reflexivity|] end.
split; [exact EnR|]. split; [change (1359 + 23)%nat with 1382%nat; rewrite EnC; reflexivity|].
split. { rewrite ?app_assoc. rewrite ?app_assoc in HSINK. exact HSINK. }
split. { pose proof HXC as CX; unfold XC in CX.
lazymatch goal with |- Z.of_nat (length (rx_gce ?cxv ++ _)) <= _ =>
pose proof (rx_gce_length cxv) as Lg; pose proof (rx_hdr_length cxv) as Lh; pose proof (rx_lctb_length cxv LCT (proj2 CX)) as Ll end.
rewrite !length_app. cbn [length c_w c_h]. unfold FRAME_OUT. clear - Lg Lh Ll HM16 Hw Hh. nia. }
destruct HMET as (acc & MLE3 & Hacc0 & HaccM & HaccN). cbn [c_S c_w c_h] in MLE3, HaccN.
eapply (mle_weaken MT); [exact MLAW | exact (mle_station MT _ _ _ _ _ MLAW MLE3 MLE4) | clear - HaccN; lia].
Qed.
Lemma ra_HX : ra_fromX1 KS MT XN B CTX ss_X1X (INV_XX KS MT XN B 1359) -> ra_fromX1 KS MT XN B CTX ss_G3X (INV_G3X KS MT XN B).
Proof. exact ra_HX_aux. Qed.
End e.
End d.
End b.
