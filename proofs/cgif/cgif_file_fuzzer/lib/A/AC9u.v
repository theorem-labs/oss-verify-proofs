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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC8h AC8j ACbc ACbf ACbd ACab ACam ACai ACaj ACak ACal ACan ACag ACac ACad.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YE00 YE01 YI00 YI0j YI0k.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACah.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI0g.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC5d YC7z YC7y YC85 YC88.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACb6 ACba AC9z ACa3 ACa4 ACa5 ACa6 ACa7 ACa1.
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
Section f.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA AS_asan_memcpy).
Variable CTXL : list (list Z).
Hypothesis TLZW : tlzw_spec SEGS B (BASE + AF_asan3_LZW_GenerateStream) CTXL pa_relro_lo pa_relro_hi.
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
Hypothesis TLZWX : tlzw_specX SEGS B MT XN (BASE + AF_asan3_LZW_GenerateStream) CTXL pa_relro_lo pa_relro_hi.
Hypothesis HCTXL1 : forall l, In l CTX -> In ((BASE + 0xaf4) :: l) CTXL.
Hypothesis HCTXL2 : forall l, In l CTX -> In ((BASE + 0xd94) :: l) CTXL.
Let RUNP := SRr_run_pi_AJ B LAWS. Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
Lemma ra_LX_aux : ra_fromX0 KS MT XN B CTX ss_MX (INV_MX MT XN B) -> ra_fromX0 KS MT XN B CTX ss_LX (INV_LX MT XN B).
Proof.
intros RM. ra_preludeX.
pose proof HINV as ((Hk3 & (K1 & EK & HK1r & HK1s) & (pI & E859 & HpI4096 & Eab3 & ApI & TpI)) & HXC & (((E661 & HXK) & EICL) & EIDL & EICL2) & HIL & HMET).
xk1 HXK EK HK1r HK1v.
lazymatch type of EIDL with _ = Z_to_bv 64 ?iv => pose proof (rx_idl_range _ : 4 <= iv <= 2 ^ 17) as Hidlr17 end.
pose proof HIMGlen as HIMGlen'. xunwrap HIMGlen'.
assert (HnP32 : h * w < 2 ^ 32) by (clear - HnP; lia). assert (HnP1 : 1 <= h * w) by (clear - Hw Hh; nia).
assert (Hrq : req_size (h * w) = h * w) by (unfold req_size; destruct (Z.eqb_spec (h * w) 0); [exfalso; clear - HnP1 e; lia | reflexivity]).
assert (HPerm3 : Permutation (ablocks B ly3 S3) ((pI, h * w) :: (raw, RAW_SIZE) :: (g, CGIF_SIZE) :: (img, Nimg) :: rest)).
{ rewrite Eab3. eapply Permutation_trans; [apply Permutation_sym; apply Permutation_cons_append|]. apply perm_skip. exact HPerm. }
assert (HpI3 : In (pI, h * w) (ablocks B ly3 S3)) by (rewrite Eab3; apply in_app_iff; right; left; reflexivity).
assert (Hraw3 : In (raw, RAW_SIZE) (ablocks B ly3 S3)) by (rewrite Eab3; apply in_app_iff; left; exact Hraw_in).
assert (Hing3 : In (g, CGIF_SIZE) (ablocks B ly3 S3)) by (rewrite Eab3; apply in_app_iff; left; exact Hing).
assert (Himg3 : In (img, Nimg) (ablocks B ly3 S3)) by (rewrite Eab3; apply in_app_iff; left; exact Himg_in).
assert (Hpf3 : In (pf, FILE_BLOCK) (ablocks B ly3 S3)) by (rewrite Eab3; apply in_app_iff; left; exact Hpf_in).
ra_blocks3X Hraw3 Hing3 Hpf3. fold F in HdFR, HdFG.
destruct (al_blocks _ _ LAWS _ _ _ _ _ pI (h * w) HAR3 HpI3) as (Hn16 & _ & Hnceil & Hnh_ia & Hnpres & _). pose proof (proj1 Hnh_ia) as Hnh. rewrite Hrq in Hnceil, Hnpres, Hnh_ia.
pose proof (blk_off_imgP _ _ _ _ _ _ _ _ HAR3 HpI3) as Hnh_img.      rewrite Hrq in Hnh_img.
destruct (al_blocks _ _ LAWS _ _ _ _ _ img Nimg HAR3 Himg3) as (Hi16 & Hi4096 & Hiceil & Hih_ia & Hipres & _). pose proof (proj1 Hih_ia) as Hih.
pose proof (blk_off_imgP _ _ _ _ _ _ img Nimg HAR3 Himg3) as Hih_img.
pose proof (sep_blocks_perm SEGS B LAWS _ _ _ _ _ (pI, h * w) (raw, RAW_SIZE) _ HAR3 HPerm3) as HdPR.
pose proof (sep_blocks_perm SEGS B LAWS _ _ _ _ _ (pI, h * w) (g, CGIF_SIZE) _ HAR3 ltac:(eapply Permutation_trans; [exact HPerm3 | apply perm_skip; apply perm_swap])) as HdPG.
pose proof (sep_blocks_perm SEGS B LAWS _ _ _ _ _ (pI, h * w) (img, Nimg) _ HAR3
ltac:(eapply Permutation_trans; [exact HPerm3 | apply perm_skip; eapply Permutation_trans; [apply perm_skip; apply perm_swap | apply perm_swap]])) as HdPI.
unfold zdisjoint, block_rng in HdPR, HdPG, HdPI. cbn [fst snd] in HdPR, HdPG, HdPI. rewrite Hrq in HdPR, HdPG, HdPI.
change (req_size RAW_SIZE) with 48 in HdPR. change (req_size CGIF_SIZE) with 96 in HdPG.
pose proof (sep_block_frame SEGS B LAWS ly3 S3 _ _ _ pI (h * w) 1 fpos HAR3 HpI3 Hfin3) as HdPF.
unfold zdisjoint in HdPF. cbn [fst snd] in HdPF. rewrite Hrq in HdPF. change (fs_frame_bytes 1) with 128 in HdPF. rewrite EFA3 in HdPF. fold F in HdPF.
pose proof (sep_block_frame SEGS B LAWS ly3 S3 _ _ _ pI (h * w) cid pos HAR3 HpI3 HfinS3) as HdPC.
unfold zdisjoint in HdPC. cbn [fst snd] in HdPC. rewrite Hrq in HdPC. rewrite EFA3 in HdPC.
box HdPR. box HdPG. box HdPI. box HdPF. box HdPC.
relowC HS AG E10 E11 E32 E10n E11n E32n.
prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
prreg HS (18%bv : bv 5) R18. prreg HS (27%bv : bv 5) R27. rewrite E859 in R27.
assert (Hcfp47 : 0 <= cfp /\ cfp + 40 < 2 ^ 47) by (clear - Hflo Hfhi Hf4096 Hfceil C1; lia).
prreg HS (25%bv : bv 5) R25. rewrite E11n in R25. rewrite unsigned_lit_small in R25 by (clear - Hcfp47; lia).
prreg HS (21%bv : bv 5) R21. rewrite E11n in R21. rewrite unsigned_lit_small in R21 by (clear - Hcfp47; lia).
prreg HS (22%bv : bv 5) R22. rewrite E11n in R22. rewrite unsigned_lit_small in R22 by (clear - Hcfp47; lia).
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
rreg_by HS (26%bv : bv 5) (Z_to_bv 64 (SB + (cfp + 8) / 8)) (denot_shadow_of Ev 11 40 cfp 8 E11n E40 ltac:(clear - Hcfp47; lia) ltac:(clear - Hcfp47; lia) ltac:(clear - PBASE PBLO; lia)) R26;
rreg_by HS (19%bv : bv 5) (Z_to_bv 64 (SB + (cfp + 20) / 8)) (denot_shadow_of Ev 11 40 cfp 20 E11n E40 ltac:(clear - Hcfp47; lia) ltac:(clear - Hcfp47; lia) ltac:(clear - PBASE PBLO; lia)) R19;
rreg_by HS (24%bv : bv 5) (Z_to_bv 64 (SB + (cfp + 22) / 8)) (denot_shadow_of Ev 11 40 cfp 22 E11n E40 ltac:(clear - Hcfp47; lia) ltac:(clear - Hcfp47; lia) ltac:(clear - PBASE PBLO; lia)) R24 | st_ok _ ?Ev _ _ =>
rreg_by HS (26%bv : bv 5) (Z_to_bv 64 (SB + (cfp + 8) / 8)) (denot_shadow_of Ev 11 40 cfp 8 E11n E40 ltac:(clear - Hcfp47; lia) ltac:(clear - Hcfp47; lia) ltac:(clear - PBASE PBLO; lia)) R26;
rreg_by HS (19%bv : bv 5) (Z_to_bv 64 (SB + (cfp + 20) / 8)) (denot_shadow_of Ev 11 40 cfp 20 E11n E40 ltac:(clear - Hcfp47; lia) ltac:(clear - Hcfp47; lia) ltac:(clear - PBASE PBLO; lia)) R19;
rreg_by HS (24%bv : bv 5) (Z_to_bv 64 (SB + (cfp + 22) / 8)) (denot_shadow_of Ev 11 40 cfp 22 E11n E40 ltac:(clear - Hcfp47; lia) ltac:(clear - Hcfp47; lia) ltac:(clear - PBASE PBLO; lia)) R24  end.
lazymatch type of AG with forall n, _ -> ew ?Ebase n = _ => assert (Usp3 : bv_unsigned (ew Ebase 2) = spZ regs) by (rewrite (AG 2%nat) by lia; exact Usp) end.
lazymatch type of Rsp with getr ?rg 2 = _ =>
assert (EspX : spZ rg = spZ regs - 320) by (unfold spZ at 1; rewrite Rsp, Usp3, unsigned_lit_small by (clear - Hceil Hslo Hstk0 FFS Hshi H47 C1; lia); clear; lia) end.
prreg HS (9%bv : bv 5) R9. rewrite Usp3 in R9. replace (spZ regs + -320) with (spZ regs - 320) in R9 by (clear - PBASE PBLO; lia).
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 11%nat in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H W3) msX) i r HS ltac:(vm_compute; reflexivity)) as HRc; cbn [ms_mem restrict] in HRc;
lazymatch type of HRc with region_ok _ _ _ (YP09.mkRegion (Some 11%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 11 cfp cs lo hi wlo whi 8 8%N (SOff 42 0) img HRc ltac:(evalE AG) ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E42, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(clear - Rimg; cbn; lia) ltac:(cbn; lia)) as Mimg;
pose proof (field_of_region Ex _ 11 cfp cs lo hi wlo whi 20 2%N (SOff 44 0) w HRc ltac:(evalE AG) ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E44, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(clear - Rw; cbn; lia) ltac:(cbn; lia)) as Mw;
pose proof (field_of_region Ex _ 11 cfp cs lo hi wlo whi 22 2%N (SOff 45 0) h HRc ltac:(evalE AG) ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E45, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(clear - Rh; cbn; lia) ltac:(cbn; lia)) as Mh end;
clear HRc | st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 11%nat in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3) msX) i r HS ltac:(vm_compute; reflexivity)) as HRc; cbn [ms_mem restrict] in HRc;
lazymatch type of HRc with region_ok _ _ _ (YP09.mkRegion (Some 11%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 11 cfp cs lo hi wlo whi 8 8%N (SOff 42 0) img HRc ltac:(evalE AG) ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E42, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(clear - Rimg; cbn; lia) ltac:(cbn; lia)) as Mimg;
pose proof (field_of_region Ex _ 11 cfp cs lo hi wlo whi 20 2%N (SOff 44 0) w HRc ltac:(evalE AG) ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E44, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(clear - Rw; cbn; lia) ltac:(cbn; lia)) as Mw;
pose proof (field_of_region Ex _ 11 cfp cs lo hi wlo whi 22 2%N (SOff 45 0) h HRc ltac:(evalE AG) ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E45, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(clear - Rh; cbn; lia) ltac:(cbn; lia)) as Mh end;
clear HRc  end.
pmkst HS.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) ?mdX) _ =>
eapply (ra_il_allX B LAWS AMEMCPY W3 (ms_regs msX) (ms_mem msX) mdX (spZ regs) ly S W mem md ly3 S3 k fpos raw pI (h * w) img Nimg w h cfp cid pos) with (IMG := IMG) end.
- clear - Hw Rw; lia. - clear - Hh Rh; lia. - clear; lia. - exact HnPN. - exact HJ3. - exact HpI3. - exact Himg3.
- intros blc lyq ownq a Hbl Ha. replace a with (pI + (a - pI)) by (clear - PBASE PBLO; lia). apply (ApI blc lyq ownq (a - pI) Hbl). clear - Ha; lia.
- rewrite Hrq. clear - HdPI; unbox; lia.
- rewrite Hrq. clear - HdPC Hflo Hfhi; unbox; lia.
- exact Hrapp.
- exact HAR. - exact Hfin. - exact Hcid0. - exact Hfal. - exact Hflo. - exact Hfhi. - exact Hcal. - exact HRA.
- exact Mimg. - exact Mw. - exact Mh.
- exact EspX. - clear - Hceil Hslo Hstk0 FFS C1; lia. - clear - H47 Hshi; lia.
- rewrite Rgp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 3%nat) by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
- rewrite Rtp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 4%nat) by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
- exact R25. - exact R26. - exact R21. - exact R19. - exact R22. - exact R24. - exact R27. - exact R18. - exact R9.
-
assert (HPi : Permutation (ablocks B ly S) ((raw, RAW_SIZE) :: (img, Nimg) :: (g, CGIF_SIZE) :: rest)) by (eapply Permutation_trans; [exact HPerm|]; apply perm_skip; apply perm_swap).
pose proof (sep_blocks_perm SEGS B LAWS ly S W mem md (raw, RAW_SIZE) (img, Nimg) _ HAR HPi) as Sri.
unfold zdisjoint, block_rng in Sri. cbn [fst snd] in Sri. change (req_size RAW_SIZE) with 48 in Sri.
pose proof (req_size_pos Nimg ltac:(clear - HnPN HnP1; lia)) as [_ Hq].
eapply (garr8_journal_block_x _ B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ img Nimg img IMG HJ3);
[exact Himg_in | exact Himg3 | clear; lia | clear - HIMGlen' HnPN Hq; lia | | exact HIMG].
intros a Ha (r & [<- | []] & Hr). cbn [fst snd] in Hr. clear - Ha Hr Sri HIMGlen' HnPN Hq. lia.
- exact HIMGlen'. }
cbv beta. intros W5 c5 Hwle5 ((-> & regs5 & mem5 & md5 & -> & HJ5 & P27 & P10 & HK5 & Hout5 & Hpres5) & HGPI). cbn [cfg_ms ms_mem mkst] in HGPI.
xbb_facts HpI3 HAR3 Hfin3 EFA3 HpI4096 Hnceil Hnh_ia HdPR XBB Hpf_in.
assert (HML : xfacts (Z.of_nat (length (YO07.interlace w IMG)) <= req_size (h * w))) by (apply xfacts_i; rewrite (interlace_lengthZ IMG w h HIMGlen' ltac:(clear - Hw; lia) ltac:(clear - Hh; lia)), Hrq; clear; lia).
clear Rsp EspX Rgp Rtp R21 R22 R24 R25 R26 R27 R18 R19 R9 Mimg Mw Mh.
assert (HF8c : 8 * (F / 8) <= F) by (apply Z.mul_div_le; clear; lia).
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx (restrict _ ?msX) =>
let kk := eval vm_compute in (run_K A_LIM (SOff 32 0) [] ssx) in
jafter_stretch_keep_hi HS kk regs5 (mrestrict (w_H W3) mem5) IL_CLOB 0xd64 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12]%nat HS2;
lazymatch type of HS2 with _ -> Forall _ ?rs -> _ =>
assert (HRK : Forall (fun r => 0 <= base_val Ev (YP09.r_base r) + YP09.r_lo r /\ base_val Ev (YP09.r_base r) + YP09.r_hi r <= 2 ^ 64 /\
(base_val Ev (YP09.r_base r) + YP09.r_hi r <= pI \/ pI + w * h <= base_val Ev (YP09.r_base r) + YP09.r_lo r) /\
(base_val Ev (YP09.r_base r) + YP09.r_hi r <= spZ regs - 320 - ESTACK \/ spZ regs - 320 <= base_val Ev (YP09.r_base r) + YP09.r_lo r)) rs);
[ repeat apply Forall_cons; try apply Forall_nil; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
rewrite ?E859; evalE AG;
unfold CGIF_SIZE, SB, ESTACK;
clear - Hob241 Hob242 Hob250 Hob253 Huar Huar4 HFceil HFhigh HF8lo HF8hi HF8c Hceil Hslo Hstk0 Hshi H47 Hrh Hrceil Hgh Hgceil Hfceil Hfhigh Hflo Hfhi C1 C2 C3 C4 C5 FFS HpI4096 Hnh Hnh_img Hnh_ia Hnceil HnP1 HdPR HdPG HdPF HdPC;
unbox; first [zone_lia | match goal with |- ?g => idtac "HRK-FAIL" g; fail end]
| specialize (HS2 HK5 (regions_kept_out2 Ev (w_H W3) (ms_mem msX) mem5 pI (pI + w * h) (spZ regs - 320 - ESTACK) (spZ regs - 320) _ Hout5 Hpres5 HRK)) ] end | st_ok _ ?Ev ?ssx (restrict _ ?msX) =>
let kk := eval vm_compute in (run_K A_LIM (SOff 32 0) [] ssx) in
jafter_stretch_keep_hi HS kk regs5 (mrestrict (w_H W3) mem5) IL_CLOB 0xd64 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12]%nat HS2;
lazymatch type of HS2 with _ -> Forall _ ?rs -> _ =>
assert (HRK : Forall (fun r => 0 <= base_val Ev (YP09.r_base r) + YP09.r_lo r /\ base_val Ev (YP09.r_base r) + YP09.r_hi r <= 2 ^ 64 /\
(base_val Ev (YP09.r_base r) + YP09.r_hi r <= pI \/ pI + w * h <= base_val Ev (YP09.r_base r) + YP09.r_lo r) /\
(base_val Ev (YP09.r_base r) + YP09.r_hi r <= spZ regs - 320 - ESTACK \/ spZ regs - 320 <= base_val Ev (YP09.r_base r) + YP09.r_lo r)) rs);
[ repeat apply Forall_cons; try apply Forall_nil; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
rewrite ?E859; evalE AG;
unfold CGIF_SIZE, SB, ESTACK;
clear - Hob241 Hob242 Hob250 Hob253 Huar Huar4 HFceil HFhigh HF8lo HF8hi HF8c Hceil Hslo Hstk0 Hshi H47 Hrh Hrceil Hgh Hgceil Hfceil Hfhigh Hflo Hfhi C1 C2 C3 C4 C5 FFS HpI4096 Hnh Hnh_img Hnh_ia Hnceil HnP1 HdPR HdPG HdPF HdPC;
unbox; first [zone_lia | match goal with |- ?g => idtac "HRK-FAIL" g; fail end]
| specialize (HS2 HK5 (regions_kept_out2 Ev (w_H W3) (ms_mem msX) mem5 pI (pI + w * h) (spZ regs - 320 - ESTACK) (spZ regs - 320) _ Hout5 Hpres5 HRK)) ] end  end.
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS. rebaseE HS AG HEv. clear HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
pose proof (ast_ok_pi_set_reg_fp Ev ssx msx (10%bv : bv 5) (SOff 45 0) HS ltac:(vm_compute; reflexivity)
ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite E45, Z.add_0_r, P10, Z_to_bv_bv_unsigned; reflexivity)) as HS3;
clear HS; rename HS3 into HS | st_ok _ ?Ev ?ssx ?msx =>
pose proof (ast_ok_set_reg_fp SEGS Ev ssx msx (10%bv : bv 5) (SOff 45 0) HS ltac:(vm_compute; reflexivity)
ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite E45, Z.add_0_r, P10, Z_to_bv_bv_unsigned; reflexivity)) as HS3;
clear HS; rename HS3 into HS  end.
norm_ss HS. clear P10.
clear P27.
lazymatch type of HUP with forall a, _ -> aview _ _ ?m3 a = _ =>
assert (HUP5 : forall a, spZ regs <= a < 2 ^ 64 -> aview SEGS (w_H W3) mem5 a = aview SEGS (w_H W) mem a)
by (intros a Ha; rewrite (Hout5 a); [apply HUP; exact Ha | clear - Ha Hbot Hslo Hceil Hstk0 C1 FFS; lia | clear - Ha Hnceil HnP1 C1 Hceil Hslo Hstk0 FFS; lia | clear - Ha; lia]) end.
clear HUP. rename HUP5 into HUP.
relowC HS AG E10 E11 E32 E10n E11n E32n. reshok_bx HS 40%nat.
clear Kgot3 Kcell3 Kguar3 Kuar3 Vgr3. aconstsA HROD HJ5 Kgot3 Kcell3 Kguar3 Kuar3 Vgr3.
paj_run_to_tok RUNTO HS HJ5 SHOK RABspan 0x1444.
all: try (oblFAX HJ5 E11n E40 HRA HAR Hfin Hcid0 Hflo Hfhi Hfal).
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrRA AG fpos F EFA3.
upd_aboveW HUP HFr AG.
xblk_stretch HFr HGPI.
clear HF HFr HG.
rebaseE HS AG HEv. clear HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 2%nat in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H W3) msX) i r HS ltac:(vm_compute; reflexivity)) as HRstk; cbn [ms_mem restrict] in HRstk;
let rs' := eval vm_compute in (trim_stack rs (-104) 0) in
pose proof (st_ok_pi_submem Ex ssx (restrict (w_H W3) msX) rs' HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS | st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 2%nat in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3) msX) i r HS ltac:(vm_compute; reflexivity)) as HRstk; cbn [ms_mem restrict] in HRstk;
let rs' := eval vm_compute in (trim_stack rs (-104) 0) in
pose proof (st_ok_submem SEGS Ex ssx (restrict (w_H W3) msX) rs' HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS  end.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
lazymatch type of HRstk with region_ok _ _ _ ?rfull =>
let rlo := eval vm_compute in (trim_region rfull (-320) (-120)) in
pose proof (st_ok_pi_add_region Ev _ _ rlo HS eq_refl
ltac:(apply (region_ok_sub SEGS Ev _ rfull); [subregion_tac | cbn; lia | exact HRstk])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
evalE AG; unfold CGIF_SIZE; repeat split; zone_lia)) as HS3;
clear HS HRstk; rename HS3 into HS end | st_ok _ ?Ev _ _ =>
lazymatch type of HRstk with region_ok _ _ _ ?rfull =>
let rlo := eval vm_compute in (trim_region rfull (-320) (-120)) in
pose proof (st_ok_pi_add_region Ev _ _ rlo HS eq_refl
ltac:(apply (region_ok_sub SEGS Ev _ rfull); [subregion_tac | cbn; lia | exact HRstk])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
evalE AG; unfold CGIF_SIZE; repeat split; zone_lia)) as HS3;
clear HS HRstk; rename HS3 into HS end  end.
norm_ss HS.
prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp. prreg HS (8%bv : bv 5) Rs0.
prreg HS (10%bv : bv 5) Ra0. prreg HS (12%bv : bv 5) Ra2. prreg HS (13%bv : bv 5) Ra3. prreg HS (14%bv : bv 5) Ra4.
rewrite E859 in Ra2.
fact_of HS 814%nat F355. fact_of HS 815%nat F356.
clear Usp3.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (Usp3 : bv_unsigned (ew Ev 2) = spZ regs) by (rewrite (AG 2%nat) by lia; exact Usp);
set (idl := bv_unsigned (ew Ev 814)) in F355; set (icl := bv_unsigned (ew Ev 815)) in F356;
assert (E814 : ew Ev 814 = Z_to_bv 64 idl) by (symmetry; apply Z_to_bv_bv_unsigned);
assert (E815 : ew Ev 815 = Z_to_bv 64 icl) by (symmetry; apply Z_to_bv_bv_unsigned) | st_ok _ ?Ev _ _ =>
assert (Usp3 : bv_unsigned (ew Ev 2) = spZ regs) by (rewrite (AG 2%nat) by lia; exact Usp);
set (idl := bv_unsigned (ew Ev 814)) in F355; set (icl := bv_unsigned (ew Ev 815)) in F356;
assert (E814 : ew Ev 814 = Z_to_bv 64 idl) by (symmetry; apply Z_to_bv_bv_unsigned);
assert (E815 : ew Ev 815 = Z_to_bv 64 icl) by (symmetry; apply Z_to_bv_bv_unsigned)  end.
rewrite E814 in Ra3. rewrite E815 in Ra4.
lazymatch goal with |- SRr _ _ _ (ra_postX _ _ _ _ ?cxv _) =>
pose proof (rx_iclen_bounds cxv) as Hiclb;
assert (Hicl : icl = rx_iclen cxv) by (subst icl; rewrite ?ew_havoc_old by (clear - PBASE PBLO; lia); rewrite EICL2; apply unsigned_lit_small; clear - Hiclb; lia);
assert (Hidl : idl = rx_idl cxv) by (subst idl; rewrite ?ew_havoc_old by (clear - PBASE PBLO; lia); rewrite EIDL; apply unsigned_lit_small; clear - Hidlr17; lia) end.
assert (HnP31 : h * w < 2 ^ 31) by (clear - HnP; lia).
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
rreg_by HS (11%bv : bv 5) (Z_to_bv 64 (h * w)) (denot_mulw_hw Ev 45 44 h w E45 E44 ltac:(clear - Rh; lia) ltac:(clear - Rw; lia) HnP31) Ra1 | st_ok _ ?Ev _ _ =>
rreg_by HS (11%bv : bv 5) (Z_to_bv 64 (h * w)) (denot_mulw_hw Ev 45 44 h w E45 E44 ltac:(clear - Rh; lia) ltac:(clear - Rw; lia) HnP31) Ra1  end.
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
Usp3 ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; rewrite ?ew_ewset_other by lia; rewrite (AG 1%nat) by lia; rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vra;
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-16) 8%N (SOff 8 0) (s0Z regs) HRstk
Usp3 ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; rewrite ?ew_ewset_other by lia; rewrite (AG 8%nat) by lia; rewrite (EE 8%nat 8%bv eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vs0 end;
clear HRstk;
assert (Hch1 : achain ly3 (aview SEGS (w_H W3) (ms_mem msX)) (spZ regs - 320) (spZ regs) ((spZ regs, raZ regs, s0Z regs) :: ch));
[ apply (achain_ly_top ly); [pose proof (proj1 (proj2 HJ5)) as LY; destruct LY as (_ & _ & _ & _ & _ & _ & _ & _ & LT & _); exact LT|];
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
Usp3 ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; rewrite ?ew_ewset_other by lia; rewrite (AG 1%nat) by lia; rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vra;
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-16) 8%N (SOff 8 0) (s0Z regs) HRstk
Usp3 ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; rewrite ?ew_ewset_other by lia; rewrite (AG 8%nat) by lia; rewrite (EE 8%nat 8%bv eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vs0 end;
clear HRstk;
assert (Hch1 : achain ly3 (aview SEGS (w_H W3) (ms_mem msX)) (spZ regs - 320) (spZ regs) ((spZ regs, raZ regs, s0Z regs) :: ch));
[ apply (achain_ly_top ly); [pose proof (proj1 (proj2 HJ5)) as LY; destruct LY as (_ & _ & _ & _ & _ & _ & _ & _ & LT & _); exact LT|];
replace (spZ regs + -8) with (spZ regs - 8) in Vra by lia; replace (spZ regs + -16) with (spZ regs - 16) in Vs0 by lia;
exact (achain_push ly _ _ (spZ regs) (s0Z regs) (raZ regs) _ (spZ regs - 320) Hch Qtop64 HUP
(rdword_of_val_mem SEGS _ _ _ _ Vra Qra) (rdword_of_val_mem SEGS _ _ _ _ Vs0 Qs0) Hra4 ltac:(clear - Hceil Hslo Hstk0 FFS; lia) Qal8
ltac:(clear - Qs0lo Qs0hi; lia) ltac:(clear - PBASE PBLO; lia))
| ]  end.
pose proof HJ5 as (_ & HLY5 & _ & _ & _ & _ & Hnev5 & _ & _ & _ & _ & _ & _ & Hpres5' & _).
pmkst HS.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) ?mdX) _ =>
pose proof (TLZWX TRAWADD_STK (spZ regs) [(raw + 40, raw + 44)] ly S W mem md [(1, fpos)] ly3 S3 W3 (ms_mem msX) mdX k (ms_regs msX)
(spZ regs - 120) (h * w) pI idl icl pI (h * w) ((spZ regs, raZ regs, s0Z regs) :: ch) (YO07.interlace w IMG) HJ5) as CALL end.
unfold cfg_at in CALL. change (w64 (BASE + AF_asan3_LZW_GenerateStream)) with (Z_to_bv 64 (BASE + 0x1444)) in CALL. apply CALL; clear CALL.
- exact (arodata_ok_journalP _ _ _ pa_relro_img _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ5 HROD).
- rewrite Rra. apply ret_ok_codeptr_v; [lia | reflexivity].
- unfold raZ. rewrite Rra, unsigned_lit_small by (clear - PBASE PBLO; lia). clear - PBASE PBLO; lia.
- rewrite Rgp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 3%nat) by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
- rewrite Rtp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 4%nat) by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
- rewrite Ra0. unfold w64. f_equal. rewrite Usp3. clear; lia.
- exact Ra1.
- exact Ra2.
- exact Ra3.
- exact Ra4.
- unfold spZ at 1. unfold s0Z. rewrite Rsp, Rs0. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia.
rewrite Usp3, !unsigned_lit_small by (clear - Hceil Hslo Hstk0 FFS Hshi H47 C1; lia). replace (spZ regs + -320) with (spZ regs - 320) by (clear - PBASE PBLO; lia). exact Hch1.
- unfold raZ at 1. rewrite Rra, unsigned_lit_small by (clear - PBASE PBLO; lia). cbn [spine map fst snd]. apply HCTXL2. exact Hctx.
- unfold spZ at 1. rewrite Rsp, Usp3, unsigned_lit_small by (clear - Hceil Hslo Hstk0 FFS Hshi H47 C1; lia).
pose proof (Z.div_mod (spZ regs) 32 ltac:(clear - PBASE PBLO; lia)) as D. rewrite Hal32, Z.add_0_r in D. rewrite D.
replace (32 * (spZ regs / 32) + -320) with ((2 * (spZ regs / 32) - 20) * 16) by (clear - PBASE PBLO; lia). apply Z_mod_mult.
- unfold spZ at 2. rewrite Rsp, Usp3, unsigned_lit_small by (clear - Hceil Hslo Hstk0 FFS Hshi H47 C1; lia). rewrite FFS. unfold LZW_TSTK, ASTACK. clear; lia.
- unfold spZ at 1. rewrite Rsp, Usp3, unsigned_lit_small by (clear - Hceil Hslo Hstk0 FFS Hshi H47 C1; lia). clear; lia.
- pose proof (Z.div_mod (spZ regs) 32 ltac:(clear - PBASE PBLO; lia)) as D. rewrite Hal32, Z.add_0_r in D. rewrite D.
replace (32 * (spZ regs / 32) - 120) with ((4 * (spZ regs / 32) - 15) * 8) by (clear - PBASE PBLO; lia). apply Z_mod_mult.
- left. unfold spZ at 1. rewrite Rsp, Usp3, unsigned_lit_small by (clear - Hceil Hslo Hstk0 FFS Hshi H47 C1; lia). clear; lia.
- clear - Hceil Hslo Hstk0 FFS C1. lia.
- clear - Hshi H47. lia.
- intros a Ha. split; [left; rewrite FFS; clear - Ha; lia | apply Hpres5'; rewrite FFS; clear - Ha; lia].
- right. destruct HLY5 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & SL & SH & _). rewrite SL, SH. clear - Hslo Hshi FFS. lia.
- clear - HnP HnP1. lia.
- clear - F355. lia.
- clear - F356. lia.
- exact HpI3.
- clear; lia.
- rewrite Hrq. clear; lia.
-   exact HGPI.
- rewrite (interlace_lengthZ IMG w h HIMGlen' ltac:(clear - Hw; lia) ltac:(clear - Hh; lia)). clear; lia.
- rewrite HEV in Hev. unfold LZW_EV. clear - Hnev5 Hk3 Hev. lia.
- rewrite (blocks_bytes_bsum B ly3 S3), Eab3, bsum_app, <- (blocks_bytes_bsum B ly S). cbn [bsum fold_right snd]. unfold LIVE_RAWADD in Hlive. clear - Hlive HnP. lia.
-
destruct HMET as (acc & MLE3 & Hacc0 & HaccM & HaccN). cbn [c_S c_w c_h] in MLE3, HaccM, HaccN. rewrite <- Hidl in HaccM, HaccN.
pose proof (mo_free_nonneg MT MLAW) as Qf.
eapply (mok_station MT S S3 _ acc); [exact MLAW | exact HMOK | exact MLE3 | | rewrite (Z.mul_comm h w); clear - HaccM Qf; lia].
assert (Hidlr : 2 <= idl <= 256) by (clear - F355; lia).
pose proof (HXMN (w * h) idl ltac:(clear - HnP Hw Hh; nia) Hidlr) as Q1. rewrite (Z.mul_comm h w). clear - Q1; lia. }
cbv beta. intros W6 c6 Hwle6 (ly6 & S6 & regs6 & mem6 & md6 & res & -> & HJ6 & HP6 & Ha06 & Hfrs6 & MLE6 & Hres).
lazymatch type of Rsp with getr ?rg 2 = _ =>
assert (EspY : spZ rg = spZ regs - 320) by (unfold spZ at 1; rewrite Rsp, Usp3, unsigned_lit_small by (clear - Hceil Hslo Hstk0 FFS Hshi H47 C1; lia); clear; lia) end.
rewrite EspY in Hres. rewrite Rra.
clear Rra Rsp Rgp Rtp Rs0 Ra0 Ra1 Ra2 Ra3 Ra4 Vra Vs0 Hch1 Hchne Qs0lo Qs0hi Qs0al Qtop64 Qra Qs0 Qal8 HLY5 Hnev5 Hpres5'.
pose proof (proj1 HJ6) as HAR6.
pose proof HJ6 as (_ & HLY6 & _ & _ & _ & _ & Hnev6 & _ & _ & _ & _ & _ & _ & Hpres6' & _).
destruct (al_layout _ _ LAWS _ _ _ _ _ ly6 HAR HLY6) as (_ & EFA6 & _).
assert (EFL6 : forall c p, flag_addr ly6 c p = flag_addr ly c p) by (intros c p; unfold flag_addr; pose proof (EFA6 c p) as X; unfold frame_addr in X; lia).
assert (Hfin6 : In (1, fpos) (frames S6)) by (rewrite Hfrs6; exact Hfin3).
assert (Hfrs6' : frames S6 = (1, fpos) :: frames S) by (rewrite Hfrs6; exact Hfrs3).
assert (HfinS6 : In (cid, pos) (frames S6)) by (rewrite Hfrs6; exact HfinS3).
frame_pres HJ6 Hfin6 EFA6 F HFpres6 HFSpres6.
clear Kgot3 Kcell3 Kguar3 Kuar3 Vgr3. aconstsA HROD HJ5 Kgot3 Kcell3 Kguar3 Kuar3 Vgr3. aconstsA HROD HJ6 Kgot6 Kcell6 Kguar6 Kuar6 Vgr6.
destruct Hres as [(Hres0 & bb & Lbb & M & HPerm6 & Hbb4096 & HM & HM2 & Abb & Tbb & Vbb & VM & HVOK & HK) | (Hres5 & HPerm6 & HVNONE & HK & HpR)].
+
assert (Hraw6 : In (raw, RAW_SIZE) (ablocks B ly6 S6)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm6|]; right; exact Hraw3).
assert (Hing6 : In (g, CGIF_SIZE) (ablocks B ly6 S6)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm6|]; right; exact Hing3).
assert (HpI6 : In (pI, h * w) (ablocks B ly6 S6)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm6|]; right; exact HpI3).
assert (Hbb6 : In (bb, Lbb) (ablocks B ly6 S6)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm6|]; left; reflexivity).
pose proof (sep_blocks_perm SEGS B LAWS _ _ _ _ _ (bb, Lbb) (raw, RAW_SIZE) _ HAR6 ltac:(eapply Permutation_trans; [exact HPerm6 | apply perm_skip; eapply Permutation_trans; [exact HPerm3 | apply perm_swap]])) as HdBR.
pose proof (sep_blocks_perm SEGS B LAWS _ _ _ _ _ (bb, Lbb) (g, CGIF_SIZE) _ HAR6
ltac:(eapply Permutation_trans; [exact HPerm6 | apply perm_skip; eapply Permutation_trans; [exact HPerm3 | eapply Permutation_trans; [apply perm_skip; apply perm_swap | apply perm_swap]]])) as HdBG.
unfold zdisjoint, block_rng in HdBR, HdBG. cbn [fst snd] in HdBR, HdBG. change (req_size RAW_SIZE) with 48 in HdBR. change (req_size CGIF_SIZE) with 96 in HdBG.
box HdBR. box HdBG.
destruct (al_blocks _ _ LAWS _ _ _ _ _ raw RAW_SIZE HAR6 Hraw6) as (_ & _ & _ & _ & Hrpres6 & _). change (req_size RAW_SIZE) with 48 in Hrpres6.
destruct (al_blocks _ _ LAWS _ _ _ _ _ bb Lbb HAR6 Hbb6) as (Hbb16 & _ & Hbbceil & Hbbh_ia & Hbbpres & _). pose proof (proj1 Hbbh_ia) as Hbbh.
pose proof (blk_off_imgP _ _ _ _ _ _ bb Lbb HAR6 Hbb6) as Hbbh_img.
pose proof (req_size_pos Lbb ltac:(clear - HM; lia)) as [_ HLbb].
reseat HS HJ6 HP6 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13]%nat AG
ltac:(idtac; first [ keptLZW HK AG Hpres6' Hfin3 HfinS3 EFA3 F HFpres6 Hraw3 Hing3 Hrpres6
ltac:(intros a Ha Hx; clear - Ha Hx HdBR; unbox; lia) ltac:(intros a Ha Hx; clear - Ha Hx HdBG; unbox; lia)
Kgot3 Kgot6 Kcell3 Kcell6 Kguar3 Kguar6 Kuar3 Kuar6 Vgr3 Vgr6
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
relowC HS AG E10 E11 E32 E10n E11n E32n. norm_ss HS.
prreg HS (10%bv : bv 5) Qa0.
lazymatch type of Qa0 with _ = ?v => assert (Hv504 : v = Z_to_bv 64 0) by (rewrite <- Qa0; cbn [ms_regs]; rewrite Ha06, Hres0; reflexivity) end.
ra_join HS ss_MX 959%nat ra_deads_M ltac:(idtac; ra_join_val HS 959%nat 4%nat Qa0 Eres). rewrite Hv504 in Eres.
ra_handX RM HS.
split; [| split; [exact HXC | split; [| split]]].
{ split; [unfold LZW_EV; clear - Hk3; lia|].
split; [exists K1; split; [rewrite !ew_havoc_old by (clear - PBASE PBLO; lia); exact EK | split; [exact HK1r | exact HK1s]]|].
exists pI, 0. split; [rewrite !ew_havoc_old by (clear - PBASE PBLO; lia); exact E859|]. split; [exact Eres|]. split; [exact HpI4096|].
split; [exact HpI6|]. split; [exact TpI|].
left. split; [reflexivity|]. exists bb, Lbb, M. split; [rewrite <- Eab3; exact HPerm6|]. split; [exact Hbb4096|]. split; [exact HM|].
split; [exact Abb|]. split; [exact Tbb|]. split; [exact Vbb | exact VM]. }
{   pose proof HK1v as HK1w; unfold xfacts in HK1w.
split; [split; [rewrite !ew_havoc_old by (clear - PBASE PBLO; lia); exact E661
| intros Hne'; rewrite !ew_havoc_old by (clear - PBASE PBLO; lia); rewrite EK, (HK1w Hne'); reflexivity]
| rewrite !ew_havoc_old by (clear - PBASE PBLO; lia); exact EICL]. }
{   exists 0. split; [exact Eres|]. split; [left; reflexivity|]. split; [| intros X5; exfalso; clear - X5; lia].
intros _ bb' M' Vbb' VM' Rbb' RM'. cbn [c_regs] in Vbb', VM'.
assert (bb' = bb) as ->.
{ apply (val_mem8_inj SEGS _ _ _ _ _ Vbb' Vbb Rbb'). pose proof (req_size_pos Lbb ltac:(clear - HM; lia)) as [_ HLbb']. clear - Hbb4096 Hbbceil HLbb' HM C1. lia. }
assert (M' = M) as ->.
{ apply (val_mem4_inj SEGS _ _ _ _ VM' VM RM'). clear - HM HM2 HnP. lia. }
unfold rx_pix. cbn [c_fattr c_w c_h]. rewrite HIL, <- Hidl, <- Hicl. split; [exact HVOK | clear - HM2; nia]. }
{   destruct HMET as (acc & MLE3 & Hacc0 & HaccM & HaccN). cbn [c_S c_w c_h] in MLE3, HaccM, HaccN |- *. rewrite <- Hidl in HaccM, HaccN.
exists (acc + xn_lzw XN (h * w) idl). split; [exact (mle_station MT _ _ _ _ _ MLAW MLE3 MLE6)|].
assert (Hidlr : 2 <= idl <= 256) by (clear - F355; lia).
pose proof (HXMN (w * h) idl ltac:(clear - HnP Hw Hh; nia) Hidlr) as Q1. rewrite (Z.mul_comm h w). clear - Q1 Hacc0 HaccM HaccN. lia. }
+
assert (Hraw6 : In (raw, RAW_SIZE) (ablocks B ly6 S6)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm6|]; exact Hraw3).
assert (Hing6 : In (g, CGIF_SIZE) (ablocks B ly6 S6)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm6|]; exact Hing3).
assert (HpI6 : In (pI, h * w) (ablocks B ly6 S6)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm6|]; exact HpI3).
destruct (al_blocks _ _ LAWS _ _ _ _ _ raw RAW_SIZE HAR6 Hraw6) as (_ & _ & _ & _ & Hrpres6 & _). change (req_size RAW_SIZE) with 48 in Hrpres6.
reseat HS HJ6 HP6 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13]%nat AG
ltac:(idtac; first [ keptLZW HK AG Hpres6' Hfin3 HfinS3 EFA3 F HFpres6 Hraw3 Hing3 Hrpres6
ltac:(intros a Ha Hx; exact Hx) ltac:(intros a Ha Hx; exact Hx)
Kgot3 Kgot6 Kcell3 Kcell6 Kguar3 Kguar6 Kuar3 Kuar6 Vgr3 Vgr6
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
relowC HS AG E10 E11 E32 E10n E11n E32n. norm_ss HS.
prreg HS (10%bv : bv 5) Qa0.
lazymatch type of Qa0 with _ = ?v => assert (Hv504 : v = Z_to_bv 64 res) by (rewrite <- Qa0; cbn [ms_regs]; rewrite Ha06; reflexivity) end.
ra_join HS ss_MX 959%nat ra_deads_M ltac:(idtac; ra_join_val HS 959%nat 4%nat Qa0 Eres). rewrite Hv504 in Eres.
ra_handX RM HS.
split; [| split; [exact HXC | split; [| split]]].
{ split; [unfold LZW_EV; clear - Hk3; lia|].
split; [exists K1; split; [rewrite !ew_havoc_old by (clear - PBASE PBLO; lia); exact EK | split; [exact HK1r | exact HK1s]]|].
exists pI, res. split; [rewrite !ew_havoc_old by (clear - PBASE PBLO; lia); exact E859|]. split; [exact Eres|]. split; [exact HpI4096|].
split; [exact HpI6|]. split; [exact TpI|].
right. split; [clear - Hres5; lia|]. rewrite <- Eab3. exact HPerm6. }
{   pose proof HK1v as HK1w; unfold xfacts in HK1w.
split; [split; [rewrite !ew_havoc_old by (clear - PBASE PBLO; lia); exact E661
| intros Hne'; rewrite !ew_havoc_old by (clear - PBASE PBLO; lia); rewrite EK, (HK1w Hne'); reflexivity]
| rewrite !ew_havoc_old by (clear - PBASE PBLO; lia); exact EICL]. }
{   exists res. split; [exact Eres|]. split; [right; exact Hres5|]. split; [intros X0; exfalso; clear - X0 Hres5; lia|].
intros _. unfold rx_pix. cbn [c_fattr c_w]. rewrite HIL, <- Hidl, <- Hicl. exact HVNONE. }
{   destruct HMET as (acc & MLE3 & Hacc0 & HaccM & HaccN). cbn [c_S c_w c_h] in MLE3, HaccM, HaccN |- *. rewrite <- Hidl in HaccM, HaccN.
exists (acc + xn_lzw XN (h * w) idl). split; [exact (mle_station MT _ _ _ _ _ MLAW MLE3 MLE6)|].
assert (Hidlr : 2 <= idl <= 256) by (clear - F355; lia).
pose proof (HXMN (w * h) idl ltac:(clear - HnP Hw Hh; nia) Hidlr) as Q1. rewrite (Z.mul_comm h w). clear - Q1 Hacc0 HaccM HaccN. lia. }
Qed.
Lemma ra_LX : ra_fromX0 KS MT XN B CTX ss_MX (INV_MX MT XN B) -> ra_fromX0 KS MT XN B CTX ss_LX (INV_LX MT XN B).
Proof. exact ra_LX_aux. Qed.
End f.
End d.
End b.
