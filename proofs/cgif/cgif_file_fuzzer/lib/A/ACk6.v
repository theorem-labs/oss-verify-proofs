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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC8h AC8j ACbc ACbf ACbd ACab ACam ACai ACaj ACak ACan ACae ACao ACap.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YE00 YE01 YI00 YI0j YI0k.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACah.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC5d YC7z YC7y YC85 YC88.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACb6 ACba AC9z ACa3 ACa4 ACa5 ACa6 ACa7 ACa8 ACaa ACk8.
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
Let RUNP := SRr_run_pi_AJ B LAWS. Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
Lemma ra_GDX : ra_fromX1 KS MT XN B CTX ss_G3X (INV_G3X KS MT XN B) -> ra_fromX1 KS MT XN B CTX ss_GDX (INV_GDX KS MT XN B).
Proof.
intros RG3. ra_preludeX.
pose proof HINV as ((Hk3 & (K1 & EK & HK1r & HK1s) & (bb & Lbb & M & E1059 & E1060 & HPerm3 & Hbb4096 & HM & Abb & Tbb)) & HXC & ((E661 & HXK) & EICL) & HLZ & HMET & HSINK & Hc & Hnz). cbn [c_slct] in Hc, Hnz.
xk1 HXK EK HK1r HK1v.
assert (Hraw3 : In (raw, RAW_SIZE) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm3|]; right; exact Hraw_in).
assert (Hing3 : In (g, CGIF_SIZE) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm3|]; right; exact Hing).
assert (Hpf3 : In (pf, FILE_BLOCK) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm3|]; right; exact Hpf_in).
ra_blocks3X Hraw3 Hing3 Hpf3. fold F in HdFR, HdFG.
relowC HS AG E10 E11 E32 E10n E11n E32n.
pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
xbb_intro HPerm3 HLZ. xF8.
reshok_bx HS 40%nat.
destruct (HK1s Hc) as [HK11 HKs1].
assert (Hp2 : 2 <= 2 ^ K1 <= 256) by (clear - HK11 HK1r; split; [change 2 with (2 ^ 1) | change 256 with (2 ^ 8)]; apply Z.pow_le_mono_r; lia).
Local Ltac tailG3X HS HJx AG E529 Hfin3 EFA3 F fpos RG3 E10 E11 E32 E10n E11n E32n :=
let HFp := fresh "HFp" in let HFSp := fresh "HFSp" in let HEv := fresh "HEv" in
frame_pres HJx Hfin3 EFA3 F HFp HFSp;
fs_rwA HS E529 HFSp;
paj_run_to_sh RUNTOP HS HJx 0x1018; [awrRA AG fpos F EFA3|];
lazymatch goal with XBB : xbfacts (4096 <= ?bbv /\ _) |- _ => lazymatch goal with HFr : frame_of _ _ _ _, HG : garr8 _ _ bbv _, HSK : asink_at _ _ _ _ _ _ |- _ => xblk_stretch HFr HG; xsink_stretch HFr HSK end end; clear_frames;
fs_roA HS; rebaseE HS AG HEv; clear HEv; relowC HS AG E10 E11 E32 E10n E11n E32n; reshok_bx HS 40%nat;
lazymatch goal with SHOK : sh_ok _ _ _ _ _ |- _ =>
paj_run_to_tok RUNTO HS HJx SHOK RABspan 0x102c; [awrRA AG fpos F EFA3|] end;
lazymatch goal with XBB : xbfacts (4096 <= ?bbv /\ _) |- _ => lazymatch goal with HFr : frame_of _ _ _ _, HG : garr8 _ _ bbv _, HSK : asink_at _ _ _ _ _ _ |- _ => xblk_stretch HFr HG; xsink_stretch HFr HSK end end; clear_frames;
rebaseE HS AG HEv; clear HEv;
ra_join HS ss_G3X 1209%nat ra_deads_G3 ltac:(idtac);
ra_handX RG3 HS.
assert (Hc1 : 3 * (2 ^ K1 - slct) <> 0) by (pose proof (Hnz K1 EK HK1r) as Hq; clear - Hq; lia).
paj_run_to_tok RUNTO HS HJ3 SHOK RABspan 0xfe8; [awrRA AG fpos F EFA3|]. xblk_stretch HFr HGout. xsink_stretch HFr HSINK. clear_frames.
assert (Hn : 3 <= 3 * (2 ^ K1 - slct) <= 765) by (clear - Hp2 Hc1 Hc HKs1 Rslct; lia).
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (Usp3 : bv_unsigned (ew Ev 2) = spZ regs) by (cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 2%nat) by lia; exact Usp) | st_ok _ ?Ev _ _ =>
assert (Usp3 : bv_unsigned (ew Ev 2) = spZ regs) by (cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 2%nat) by lia; exact Usp)  end.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 32%nat in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H W3) msX) i r HS ltac:(vm_compute; reflexivity)) as HRg; cbn [ms_mem restrict] in HRg;
lazymatch type of HRg with region_ok _ _ _ (YP09.mkRegion (Some 32%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 32 g cs lo hi wlo whi 56 8%N (SOff 54 0) hw HRg ltac:(evalE AG) ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E54, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(clear - Rhw; cbn; lia) ltac:(cbn; lia)) as M56;
pose proof (field_of_region Ex _ 32 g cs lo hi wlo whi 80 8%N (SOff 56 0) pf HRg ltac:(evalE AG) ltac:(cbn; tauto)
ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E56E, Z.add_0_r, unsigned_lit_small by (clear - XF; unfold xfacts in XF; lia); reflexivity)
ltac:(cbn; clear - XF; unfold xfacts in XF; lia) ltac:(cbn; lia)) as M80;
pose proof (field_of_region Ex _ 32 g cs lo hi wlo whi 64 8%N (SOff 52 0) ctx HRg ltac:(evalE AG) ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E52, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(clear - Rctx; cbn; lia) ltac:(cbn; lia)) as M64 end;
clear HRg | st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 32%nat in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3) msX) i r HS ltac:(vm_compute; reflexivity)) as HRg; cbn [ms_mem restrict] in HRg;
lazymatch type of HRg with region_ok _ _ _ (YP09.mkRegion (Some 32%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 32 g cs lo hi wlo whi 56 8%N (SOff 54 0) hw HRg ltac:(evalE AG) ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E54, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(clear - Rhw; cbn; lia) ltac:(cbn; lia)) as M56;
pose proof (field_of_region Ex _ 32 g cs lo hi wlo whi 80 8%N (SOff 56 0) pf HRg ltac:(evalE AG) ltac:(cbn; tauto)
ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E56E, Z.add_0_r, unsigned_lit_small by (clear - XF; unfold xfacts in XF; lia); reflexivity)
ltac:(cbn; clear - XF; unfold xfacts in XF; lia) ltac:(cbn; lia)) as M80;
pose proof (field_of_region Ex _ 32 g cs lo hi wlo whi 64 8%N (SOff 52 0) ctx HRg ltac:(evalE AG) ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E52, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(clear - Rctx; cbn; lia) ltac:(cbn; lia)) as M64 end;
clear HRg  end.
prreg HS (2%bv : bv 5) Q2. prreg HS (26%bv : bv 5) Q18.
prreg HS (18%bv : bv 5) Q20. prreg HS (23%bv : bv 5) Q22. prreg HS (24%bv : bv 5) Q24.
xdummy_factsA HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx (restrict _ ?msX) =>
let e := eval vm_compute in (sr_get (ss_regs ssx) 27%bv) in
assert (Q19 : getr (ms_regs msX) 27%bv = Z_to_bv 64 (3 * (2 ^ K1 - slct)));
[ rewrite (st_ok_restrict_reg SEGS _ _ _ _ 27%bv HS); change (sv_denot Ev e = Z_to_bv 64 (3 * (2 ^ K1 - slct)));
apply bv_eq; rewrite unsigned_lit_small by (clear - Hn; lia); change (bv_unsigned (sv_denot Ev e)) with (U Ev e);
apply (U_ra_ndummy Ev 662 49 K1 slct EK ltac:(clear - HK11 HK1r; lia) E49); clear - Hc1 Hc HKs1 Rslct; lia | ] end.
assert (Qal : (spZ regs - 320) mod 16 = 0).
{ pose proof (Z.div_mod (spZ regs) 32 ltac:(lia)) as D. rewrite Hal32, Z.add_0_r in D. rewrite D.
replace (32 * (spZ regs / 32) - 320) with ((2 * (spZ regs / 32) - 20) * 16) by lia. apply Z_mod_mult. }
clear Kgot3 Kcell3 Kguar3 Kuar3 Vgr3. aconstsA HROD HJ3 Kgot3 Kcell3 Kguar3 Kuar3 Vgr3.
prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
assert (Hchne : ch <> []) by (intros Hnil0; pose proof (HDEEP _ Hctx) as Hdeep0; rewrite Hnil0 in Hdeep0; cbn in Hdeep0; clear - Hdeep0; lia).
assert (Qtop : spZ regs < ly_top ly - 16) by (destruct Hch as [[_ Hnil] | (Qa & Qb & _)]; [exfalso; exact (Hchne Hnil) | lia]).
assert (Qtop64 : ly_top ly <= 2 ^ 64) by lia. assert (Qceil : alloc_ceiling <= spZ regs) by lia.
assert (Qal8 : spZ regs mod 8 = 0) by (pose proof (Z.div_mod (spZ regs) 32 ltac:(lia)) as D; rewrite Hal32, Z.add_0_r in D; rewrite D; replace (32 * (spZ regs / 32)) with ((4 * (spZ regs / 32)) * 8) by lia; apply Z_mod_mult).
assert (Qra : 0 <= raZ regs < 2 ^ 64) by (unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq).
assert (Qs0 : 0 <= s0Z regs < 2 ^ 64) by (unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq).
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msX) =>
let rsm := eval vm_compute in (ss_mem ssx) in
let i := match rsm with _ => idx_of_base_lo rsm 2%nat (-104) | _ => idx_of_base rsm 2%nat end in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rsm got_regionP) in
pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H W3) msX) i r HS ltac:(vm_compute; reflexivity)) as HRr; cbn [ms_mem restrict] in HRr;
lazymatch type of HRr with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-8) 8%N (SOff 1 0) (raZ regs) HRr ltac:(evalE AG) ltac:(cbn; tauto)
ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 1%nat) by lia; rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vra;
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-16) 8%N (SOff 8 0) (s0Z regs) HRr ltac:(evalE AG) ltac:(cbn; tauto)
ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 8%nat) by lia; rewrite (EE 8%nat 8%bv eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vs0;
clear HRr;
assert (Hch1 : achain ly3 (aview SEGS (w_H W3) (ms_mem msX)) (spZ regs - 320) (spZ regs) ((spZ regs, raZ regs, s0Z regs) :: ch));
[ replace (spZ regs - 8) with (spZ regs + -8) in Vra by lia; replace (spZ regs - 16) with (spZ regs + -16) in Vs0 by lia;
pose proof HJ3 as (_ & (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _) & _);
apply (achain_ly_top ly ly3); [exact Etop|];
exact (achain_push ly _ _ (spZ regs) (s0Z regs) (raZ regs) _ (spZ regs - 320) Hch Qtop64 (aview_above_of_journal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3)
(rdword_of_val_mem SEGS _ _ _ _ Vra Qra) (rdword_of_val_mem SEGS _ _ _ _ Vs0 Qs0) Hra4 Qceil Qal8 Qtop ltac:(lia))
| ] end end.
pmkst HS.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) ?mdX) _ =>
lazymatch type of HSINK with asink_at _ _ _ _ _ ?SG =>
eapply (ra_wdbX B LAWS wfn hw Rwfn Rhw KS AIL WFNX (Z.to_nat (3 * (2 ^ K1 - slct))) (3 * (2 ^ K1 - slct)) W3 (ms_regs msX) (ms_mem msX) mdX
(spZ regs - 320) ly3 S3 g ctx ((spZ regs, raZ regs, s0Z regs) :: ch) pf (F + 32) fpos SG ltac:(clear - Hn; lia)) end;
[ eapply (ajournal_sub_init SEGS B TRAWADD_STK (spZ regs) ((raw + 40, raw + 44) :: asink_fp pf) ly S W mem md [(1, fpos)] ly3 S3 W3 _ _ k RAWDBX_STK (spZ regs - 320) (asink_fp pf) (-320));
[exact HJ3 | clear; lia | reflexivity | clear; lia | unfold RAWDBX_STK, WCBF_STK, YC20.WCB_STK, AFWRITE_STK; clear; lia | rewrite FFS; unfold RAWDBX_STK, WCBF_STK, YC20.WCB_STK, AFWRITE_STK; clear; lia]
| rewrite Q2; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 2%nat) by lia; rewrite Usp; f_equal; clear; lia
| exact Qal
| rewrite Q3; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 3%nat) by lia; rewrite (EE 3%nat 3%bv eq_refl); exact Hgp
| rewrite Q4; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 4%nat) by lia; rewrite (EE 4%nat 4%bv eq_refl); exact Htp
| unfold s0Z at 1; rewrite Q8; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 2%nat) by lia; rewrite Usp; exact Hch1
| exact Q19 | clear - Hn; lia | exact Q20
| rewrite Q18; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E53
| rewrite Q22; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 32%nat) by lia; exact E32
| exact Hing3 | exact M56 | exact M80 | exact M64 | exact Rctx
| rewrite Q24; cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; evalE AG
| exact Vpd | exact Hfin3 | exact Hpf3 | exact Hp_ia
| rewrite !EFA3; fold F; apply xfacts_i; clear - XF HdFG HFq; unbox; unfold xfacts in XF; unfold RAWDBX_STK, WCBF_STK, YC20.WCB_STK, AFWRITE_STK, TRAWADD_STK in *;
repeat split; first [lia | rewrite HFq at 1; rewrite Z.mul_comm; apply Z_mod_mult]
| exact HRApd | exact HSINK
| pose proof HLCT as HLl; unfold xfacts in HLl; pose proof HXC as CX; unfold XC in CX; cbn [c_slct] in CX; destruct (HLl ltac:(clear - Hc CX; lia)) as [_ HLlen2];
clear - HSmax Hp2 HLlen2 Hc Hw Hh Hn; unfold xfacts in HSmax; unfold rx_gce, rx_hdr, FRAME_OUT in *;
rewrite !length_app, ?length_firstn in *; cbn [length YO07.u16le app] in *; destruct (_ || _); cbn [length app] in *; nia ] end. }
cbv beta. intros W6 c6 Hwle6 (ly6 & S6 & regs6 & mem6 & md6 & -> & HJw & (Ely6 & ES6) & HK19 & HK20 & HSINKw & Hrg6). subst ly6 S6.
pose proof (Permutation_refl (ablocks B ly3 S3)) as HPb6. clear HSINK Vpd HRApd. rename HSINKw into HSINK.
clear Q2 Q18 Q19 Q20 Q22 M56 M80 M64 Q3 Q4 Q8 Vra Vs0 Hch1.
pose proof (ajournal_sub_tok SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3 HJw ltac:(rewrite FFS; unfold RAWDBX_STK, WCBF_STK, YC20.WCB_STK, AFWRITE_STK; clear; lia) ltac:(clear; lia)
ltac:(intros aa (r0 & Hr1 & Hr2); left; exists r0; split; [right; exact Hr1 | exact Hr2])) as HJ6.
cbn [app] in HJ6. replace (k + 0) with k in HJ6 by lia.
pose proof (proj1 HJ6) as HAR6.
pose proof Hfrs3 as Hfrs6. pose proof Hfin3 as Hfin6. pose proof HfinS3 as HfinS6. pose proof HPerm3 as HPerm6.
pose proof Hraw3 as Hraw6. pose proof Hing3 as Hing6. pose proof EFA3 as EFA6. pose proof EFL3 as EFL6.
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR6 Hfin6) as (_ & _ & HFpres6 & HFSpres6). change (fs_frame_bytes 1) with 128 in HFpres6, HFSpres6.
change (128 / 8) with 16 in HFSpres6. rewrite !EFA6 in HFpres6, HFSpres6. fold F in HFpres6, HFSpres6.
destruct (al_blocks _ _ LAWS _ _ _ _ _ raw RAW_SIZE HAR6 Hraw6) as (_ & _ & _ & _ & Hrpres6 & _). change (req_size RAW_SIZE) with 48 in Hrpres6.
destruct (al_blocks _ _ LAWS _ _ _ _ _ g CGIF_SIZE HAR6 Hing6) as (_ & _ & _ & _ & Hgpres6 & _). change (req_size CGIF_SIZE) with 96 in Hgpres6.
assert (HUP6 : forall a, spZ regs <= a < 2 ^ 64 -> aview SEGS (w_H W6) mem6 a = aview SEGS (w_H W) mem a)
by (intros a Ha; pose proof HJ6 as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _); apply F1; [clear - Ha Qceil; lia | clear - Ha; lia]).
pose proof Abb as Abb6.
aconstsA HROD HJ6 Kgot6 Kcell6 Kguar6 Kuar6 Vgr6.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx (restrict _ ?msX) =>
let kk := eval vm_compute in (run_K A_LIM (SOff 32 0) [] ssx) in
let n := eval vm_compute in (length (ss_mem ssx)) in let idxs := eval vm_compute in (seq 0 n) in
jafter_stretch_keep_hi HS kk regs6 (mrestrict (w_H W6) mem6) RAWDB_CLOB 0x1004 idxs HS2;
specialize (HS2 Hrg6);
match type of HS2 with ?tq -> _ => assert (HRK : tq) end;
[ cbn [ms_mem restrict]; repeat apply Forall_cons; try apply Forall_nil;
lazymatch goal with
| |- region_kept _ ?Ey _ _ (YP09.mkRegion (Some 516%nat) ?lo ?hi ?wlo ?whi _) =>
eapply (region_kept_frame_sub (segs:=SEGS) B Ey _ _ _ _ _ _ _ _ _ _ _ _ _ _ 516%nat F lo hi wlo whi _ 1 fpos HJw);
[ evalE AG | exact Hfin3 | rewrite EFA3; fold F; lia | rewrite EFA3; fold F; change (fs_frame_bytes 1) with 128; lia
| xFP | intros aa Haa; apply (fun H => proj1 (HFpres6 aa H)); lia ]
| |- region_kept _ ?Ey _ _ (YP09.mkRegion (Some 529%nat) ?lo ?hi ?wlo ?whi _) =>
eapply (region_kept_fshadow_sub (segs:=SEGS) B Ey _ _ _ _ _ _ _ _ _ _ _ _ _ _ 529%nat (SB + F / 8) lo hi wlo whi _ 1 fpos HJw);
[ evalE AG | exact Hfin3 | rewrite EFA3; fold F; unfold shadow_addr; rewrite <- SB_SHADOW_OFF; lia
| rewrite EFA3; fold F; unfold shadow_addr; rewrite <- SB_SHADOW_OFF; change (fs_frame_bytes 1 / 8) with 16; lia
| xFP | intros aa Haa; lia ]
| |- region_kept _ ?Ey _ _ (YP09.mkRegion (Some 10%nat) ?lo ?hi ?wlo ?whi _) =>
eapply (region_kept_block_subw (segs:=SEGS) B Ey _ _ _ _ _ _ _ _ _ _ _ _ _ _ 10%nat lo hi wlo whi _ raw RAW_SIZE HJw);
[ evalE AG | exact Hraw3 | exact Hraw6 | lia | change (req_size RAW_SIZE) with 48; lia
| xFP | intros aa Haa; apply (fun H => proj1 (Hrpres6 aa H)); lia ]
| |- region_kept _ ?Ey _ _ (YP09.mkRegion (Some 2%nat) _ _ _ _ _) =>
eapply (region_kept_stack_sub SEGS B); [exact HJw | exact HJ6 | evalE AG | lia | rewrite FFS; lia | lia | cbn; lia | cbn; lia]
| |- region_kept _ ?Ey _ _ (YP09.mkRegion (Some 11%nat) ?lo ?hi ?wlo ?whi _) =>
eapply (region_kept_frame_sub (segs:=SEGS) B Ey _ _ _ _ _ _ _ _ _ _ _ _ _ _ 11%nat cfp lo hi wlo whi _ cid pos HJw);
[ evalE AG | exact HfinS3 | rewrite EFA3; lia | rewrite EFA3; lia | xFP | intros aa Haa; lia ]
| |- region_kept _ ?Ey _ _ (YP09.mkRegion (Some 32%nat) ?lo ?hi ?wlo ?whi _) =>
eapply (region_kept_block_sub SEGS B); [exact HJw | evalE AG | exact Hing3 | exact Hing6 | lia | change (req_size CGIF_SIZE) with 96; unfold CGIF_SIZE; lia | lia
| xFP ]
| |- _ => keptIA I I AG Kgot3 Kgot6 Kcell3 Kcell6 Kguar3 Kguar6 Kuar3 Kuar6 Vgr3 Vgr6
end
| specialize (HS2 HRK); clear HRK ] end.
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS. rebaseE HS AG HEv. clear HEv.
pose proof (st_ok_pi_pin_reg' _ _ _ 27%bv 0 HS ltac:(cbn [ms_regs restrict mkst]; exact HK19) eq_refl) as HS3. clear HS. rename HS3 into HS.
pose proof (st_ok_pi_pin_reg' _ _ _ 18%bv 0 HS ltac:(cbn [ms_regs restrict mkst]; exact HK20) eq_refl) as HS3. clear HS. rename HS3 into HS.
norm_ss HS.
xblk_station HJw.
clear HJ3 HAR3 Hfin3 HfinS3 Hing3 Hraw3 Abb Hfrs3 HFpres3 HFSpres3 Hrpres3 Hgpres3 HUP Kgot3 Kcell3 Kguar3 Kuar3 Vgr3 HJw HPb6 Hwle6 Hrg6 HK19 HK20.
clear Hchne Qtop Qtop64 Qceil Qal8 Qra Qs0.
clear EFA3 EFL3 HPerm3.
rename HAR6 into HAR3. rename Hfin6 into Hfin3. rename HfinS6 into HfinS3. rename Hing6 into Hing3. rename Hraw6 into Hraw3. rename HPerm6 into HPerm3. rename Abb6 into Abb.
rename Hfrs6 into Hfrs3. rename EFA6 into EFA3. rename EFL6 into EFL3. rename HFpres6 into HFpres3. rename HFSpres6 into HFSpres3. rename HUP6 into HUP.
rename Hrpres6 into Hrpres3. rename Hgpres6 into Hgpres3. rename Kgot6 into Kgot3. rename Kcell6 into Kcell3. rename Kguar6 into Kguar3. rename Kuar6 into Kuar3. rename Vgr6 into Vgr3.
try clear md3. repeat match goal with H : context [W3] |- _ => first [clear H | fail 2 "W3 still used in" H] end. try clear W3. rename W6 into W3.
relowC HS AG E10 E11 E32 E10n E11n E32n. reshok_bx HS 40%nat.
paj_run_to_tok RUNTO HS HJ6 SHOK RABspan 0x1014; [awrRA AG fpos F EFA3|]. xblk_stretch HFr HGout. xsink_stretch HFr HSINK. clear_frames.
tailG3X HS HJ6 AG E529 Hfin3 EFA3 F fpos RG3 E10 E11 E32 E10n E11n E32n.
split; [| split; [exact HXC | split; [| split; [| split]]]].
{ solve_INV_T0 Hk3 EK HK1r HK1s E1059 E1060 HPerm3 Hbb4096 HM Abb Tbb. }
{ pose proof HK1v as HK1w; unfold xfacts in HK1w.
split; [split; [rewrite !ew_havoc_old by (clear - PBASE PBLO; lia); exact E661
| intros Hne'; rewrite !ew_havoc_old by (clear - PBASE PBLO; lia); rewrite EK, (HK1w Hne'); reflexivity]
| rewrite !ew_havoc_old by (clear - PBASE PBLO; lia); exact EICL]. }
{ exists out. split; [exact Hls|]. rewrite !ew_havoc_old by (clear - PBASE PBLO; lia).
rewrite E1059, E1060. rewrite (Z.mod_small M) by (clear - HM HLbbmax; unfold MALLOC_MAX in HLbbmax; lia).
rewrite !unsigned_lit_small by (first [clear - HM HLbbmax; unfold MALLOC_MAX in HLbbmax; lia | clear - XBB XF HML; unfold xbfacts in XBB; unfold xfacts in XF, HML; lia]).
split; [exact HGout | split; [exact HMo | exact HM16]]. }
{ exact HMET. }
{
unfold rx_lctb; cbn [c_slct]. rewrite (proj2 (Z.eqb_neq slct 0) Hc). cbn [negb].
pose proof HK1v as HK1w; unfold xfacts in HK1w. rewrite <- (HK1w Hc).
rewrite (Z.mod_small ((2 ^ K1 - slct) * 3) 65536) by (clear - Hp2 Rslct HKs1; lia).
unfold YO07.zeros. replace (Z.to_nat ((2 ^ K1 - slct) * 3)) with (Z.to_nat (3 * (2 ^ K1 - slct))) by (clear; f_equal; lia).
rewrite ?app_assoc. rewrite ?app_assoc in HSINK. exact HSINK. }
Qed.
End f.
End d.
End b.
