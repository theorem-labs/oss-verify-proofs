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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI03 YI04 YI1i YI20.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YCcz.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YCe7 YF9i YCeb YCe8 YCfq YCdy YCfr YCfu YCe9 YCgu YCgv.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Lemma ngK_land_low_mod : forall x m k, 0 <= k -> 0 <= m < 2 ^ k -> Z.land (x mod 2 ^ k) m = Z.land x m.
Proof.
intros x m k Hk Hm. rewrite <- (Z.land_ones x k) by lia. rewrite <- Z.land_assoc. f_equal.
rewrite Z.land_comm, Z.land_ones by lia. apply Z.mod_small. lia.
Qed.
Ltac ng_attr4_hc Hc E33 attr LM :=
rewrite branch_ne_U, U_and_lit in Hc by lia;
first [ lazymatch type of Hc with context [U ?Ex (SExt false 32 (SOff 33 0))] =>
rewrite (U_zext Ex 32 (SOff 33 0)), (U_atom Ex 33 attr ltac:(cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E33) ltac:(lia)) in Hc;
replace (U Ex (SLit 0)) with 0 in Hc by reflexivity;
change (Z.of_N 32) with 32 in Hc; rewrite (LM attr 4 32) in Hc by (first [lia | change (2 ^ 32) with 4294967296; lia]) end
| lazymatch type of Hc with context [U ?Ex (SOff 33 0)] =>
rewrite (U_atom Ex 33 attr ltac:(cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E33) ltac:(lia)) in Hc;
replace (U Ex (SLit 0)) with 0 in Hc by reflexivity end ].
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section d.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AMALLOC : amalloc_realizes trbsegs B.
Hypothesis AFREE : afree_realizes trbsegs B.
Hypothesis AMEMSET : aintrin_realizes trbsegs B OSet A_asan_memset.
Hypothesis AMEMCPY : aintrin_realizes trbsegs B OCpy A_asan_memcpy.
Hypothesis ASF : astack_free_law trbsegs B.
Hypothesis FFL : frame_flag_lawP trbsegs B.
Let HBcode := tl_code B TL. Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL.
Let HBguar := tl_got_uar B TL. Let HBuar := tl_uar_cell B TL. Let errno_low := tl_env B TL.
Local Notation code := (as_code B).
Lemma ng_K : NG_P0_stmt B -> NG_G_stmt B -> NG_K_stmt B.
Proof.
intros NGP0 NGG ly S W regs mem md ch cfgp pal0 pala attr gen Wd Hd ngp loops rest cid pos E0 E W3 ly3 S3 ms3 md3 k fpos g HCTX HCFG HE0 HE Rg HNOW HW0 HH0 HS.
ng_facts HCTX HCFG HE0 HE.
destruct HNOW as (HJ3 & Hk3 & Hfrs3 & Eab3 & Hg4096 & Tg & Ag).
ng_frame HJ3 Hfrs3.
assert (Hg_in : In (g, 96) (ablocks B ly3 S3)) by (rewrite Eab3; apply in_app_iff; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ g 96 HAR3 Hg_in) as (Hg16 & _ & Hgceil & Hgh_ia & Hgpres3 & _). pose proof (proj1 Hgh_ia) as Hgh.
pose proof (blk_off_img _ _ _ _ _ _ g 96 HAR3 Hg_in) as Hgh_img.
change (req_size 96) with 96 in Hgceil, Hgpres3, Hgh_img.
pose proof (sep_block_frame trbsegs B LAWS ly3 S3 _ _ _ g 96 1 fpos HAR3 Hg_in Hfin3) as HdGF.
unfold zdisjoint in HdGF. cbn [fst snd] in HdGF. change (req_size 96) with 96 in HdGF. change (fs_frame_bytes 1) with 128 in HdGF. rewrite EFA3 in HdGF. fold F in HdGF.
pose proof (sep_block_frame trbsegs B LAWS ly3 S3 _ _ _ g 96 cid pos HAR3 Hg_in HfinS3) as HdGC.
unfold zdisjoint in HdGC. cbn [fst snd] in HdGC. change (req_size 96) with 96 in HdGC. rewrite EFA3 in HdGC.
nbox_seps.
aconsts HROD HJ3 Kgot3 Kcell3 Kguar3 Kuar3 Vgr3.
assert (E10' : ew E 10 = Z_to_bv 64 cfgp) by (rewrite (AG 10%nat) by lia; exact E10).
reshok_bx HS 35%nat.
aj_run_tok trbtbl_lib_ok HS HJ3 SHOK NBspan; [slim; oblF HJ3 E10' E35 HRA HAR Hfin Hcid0 Hflo Hfhi Hfal | slim; awrR AG fpos F EFA3 |]. clear_frames.
srr_branch_tok trbtbl_lib_ok HS SHOK NBspan.
-
aj_run_to_tok trbtbl_lib_ok HS HJ3 SHOK NBspan 0x85fcc.
all: try (slim; oblF HJ3 E10' E35 HRA HAR Hfin Hcid0 Hflo Hfhi Hfal).
all: try (slim; awrR AG fpos F EFA3).
clear_frames.
rewrite branch_ne_U, U_and_lit in Hc by lia.
lazymatch type of Hc with context [U ?Ex (SExt false 8 (SOff 33 0))] =>
rewrite (U_zext Ex 8 (SOff 33 0)), (U_atom Ex 33 attr ltac:(cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E33) ltac:(lia)) in Hc;
replace (U Ex (SLit 0)) with 0 in Hc by reflexivity end.
change (Z.of_N 8) with 8 in Hc. rewrite (ngK_land_low_mod attr 4 8) in Hc by (first [lia | change (2 ^ 8) with 256; lia]).
assert (Ha4 : Z.land attr 4 <> 0) by (intros Hz; rewrite Hz in Hc; cbn in Hc; discriminate Hc).
clear Hc.
srr_branch_tok trbtbl_lib_ok HS SHOK NBspan.
2: { exfalso. ng_attr4_hc Hc E33 attr ngK_land_low_mod. destruct (Z.eqb_spec (Z.land attr 4) 0) as [Hz|Hz]; [exact (Ha4 Hz) | cbn in Hc; discriminate Hc]. }
clear Hc.
aj_run_to_tok trbtbl_lib_ok HS HJ3 SHOK NBspan 0x85fcc.
all: try (slim; oblF HJ3 E10' E35 HRA HAR Hfin Hcid0 Hflo Hfhi Hfal).
all: try (slim; awrR AG fpos F EFA3).
clear_frames.
lazymatch type of HS with st_ok _ ?Ev ?ssx (restrict _ ?msv) =>
change ssx with ss_NP0 in HS;
eapply (NGP0 ly S W regs mem md ch cfgp pal0 pala attr gen Wd Hd ngp loops rest cid pos E0 Ev W3 ly3 S3 msv _ k fpos g);
[ split; [exact HPRE | split; [exact Hal32 | split; [| split; [exact Hroom | split; [exact Htop32 | split; [exact HROD | split; [exact Hcfg | split; [exact HWH | split; [exact Hpala | split; [exact HPerm | split; [exact Hev | exact Hlive]]]]]]]]]]]
| split; [exact Hfin | split; [exact Hcid0 | split; [exact Hfal | split; [exact Hflo | split; [exact Hfhi | split; [exact Hcal | exact HRA]]]]]]
| split; [exact EE | split; [exact E10 | split; [exact E32 | exact Usp]]]
| split; [intros n Hn; rewrite !ew_ewset_other by lia; apply AG; exact Hn | repeat split; rewrite !ew_ewset_other by lia; assumption]
| rewrite !ew_ewset_other by lia; exact Rg
| split; [exact HJ3 | split; [exact Hk3 | split; [exact Hfrs3 | split; [exact Eab3 | split; [exact Hg4096 | split; [exact Tg | exact Ag]]]]]]
| exact HW0 | exact HH0 | exact Ha4
| exact HS ] end.
rewrite <- Hra88. destruct Hspine as [Hs | Hs]; rewrite Hs; cbn; tauto.
-
rewrite branch_ne_U, U_and_lit in Hc by lia.
lazymatch type of Hc with context [U ?Ex (SExt false 8 (SOff 33 0))] =>
rewrite (U_zext Ex 8 (SOff 33 0)), (U_atom Ex 33 attr ltac:(cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E33) ltac:(lia)) in Hc;
replace (U Ex (SLit 0)) with 0 in Hc by reflexivity end.
change (Z.of_N 8) with 8 in Hc. rewrite (ngK_land_low_mod attr 4 8) in Hc by (first [lia | change (2 ^ 8) with 256; lia]).
assert (Ha4 : Z.land attr 4 = 0) by (destruct (Z.eqb_spec (Z.land attr 4) 0) as [Hz|Hz]; [exact Hz | cbn in Hc; discriminate Hc]). clear Hc.
rewrite Ha4 in HPerm. cbn [Z.eqb app] in HPerm.
assert (Hpala_in : In (pala, 3 * ngp) (ablocks B ly S)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm|]; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ pala (3 * ngp) HAR Hpala_in) as (_ & Hpala4096 & Hpalaceil & _ & _ & _).
pose proof (req_size_pos (3 * ngp) ltac:(clear - CR28; lia)) as [Hrq1 Hrq2].
assert (Epala : pala = pal0).
{ apply (f_equal bv_unsigned) in Hpala. rewrite !unsigned_lit_small in Hpala by lia. exact Hpala. }
aj_run_tok trbtbl_lib_ok HS HJ3 SHOK NBspan; [slim; oblF HJ3 E10' E35 HRA HAR Hfin Hcid0 Hflo Hfhi Hfal | slim; awrR AG fpos F EFA3 |]. clear_frames.
assert (HMM : MALLOC_MAX = 2 ^ 28) by reflexivity.
clear Kgot3 Kcell3 Kguar3 Kuar3 Vgr3. aconsts HROD HJ3 KgotB KcellB KguarB KuarB VgrB.
rreg HS (10%bv : bv 5) Ra0. rreg HS (1%bv : bv 5) Rra. rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp.
rreg HS (4%bv : bv 5) Rtp. rreg HS (8%bv : bv 5) Rs0.
assert (Qceil : alloc_ceiling <= spZ regs) by lia. assert (Qal8 : spZ regs mod 8 = 0) by (pose proof (Z.div_mod (spZ regs) 32 ltac:(lia)) as D; rewrite Hal32, Z.add_0_r in D; rewrite D; replace (32 * (spZ regs / 32)) with ((4 * (spZ regs / 32)) * 8) by lia; apply Z_mod_mult).
assert (Qtop : spZ regs < ly_top ly - 16) by lia. assert (Qtop64 : ly_top ly <= 2 ^ 64) by lia. assert (Qsp : spZ regs - 192 + 16 <= spZ regs) by lia.
assert (Qra : 0 <= raZ regs < 2 ^ 64) by (unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq).
assert (Qs0 : 0 <= s0Z regs < 2 ^ 64) by (unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq).
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
assert (HUP : forall a, spZ regs <= a < 2 ^ 64 -> aview trbsegs (w_H W3) (ms_mem msX) a = aview trbsegs (w_H W) mem a)
by (intros a Ha; pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _); apply F1; [clear - Ha Qceil; lia | clear - Ha; lia]) end.
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 2%nat in let i := eval vm_compute in i in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3) msX) i _ HS eq_refl) as HRstk; cbn [ms_mem restrict] in HRstk;
lazymatch type of HRstk with region_ok _ _ _ (YQ0b.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-8) 8%N (SOff 1 0) (raZ regs) HRstk
ltac:(evalE AG) ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 1%nat) by lia; rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vra;
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-16) 8%N (SOff 8 0) (s0Z regs) HRstk
ltac:(evalE AG) ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 8%nat) by lia; rewrite (EE 8%nat 8%bv eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vs0 end;
clear HRstk;
assert (Hch1 : achain ly (aview trbsegs (w_H W3) (ms_mem msX)) (spZ regs - 192) (spZ regs) ((spZ regs, raZ regs, s0Z regs) :: ch));
[ replace (spZ regs - 8) with (spZ regs + -8) in Vra by lia; replace (spZ regs - 16) with (spZ regs + -16) in Vs0 by lia;
exact (achain_push ly _ _ (spZ regs) (s0Z regs) (raZ regs) _ (spZ regs - 192) Hch Qtop64 HUP
(rdword_of_val_mem trbsegs _ _ _ _ Vra Qra) (rdword_of_val_mem trbsegs _ _ _ _ Vs0 Qs0) Hra4 Qceil Qal8 Qtop Qsp)
| ] end.
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
replace (Z_to_bv 64 340936) with (Z_to_bv 64 (pc_wrap_malloc (as_code B))) by (rewrite HBcode; vm_compute; reflexivity).
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_malloc_at trbsegs B LAWS Hsegs errno_low ML AMALLOC _ (ms_regs msX) (ms_mem msX) TNEWGIF_STK (spZ regs) [] ly S W mem md [(1, fpos)]
ly3 S3 _ k (3 * ngp) (-192) (Z_to_bv 64 0x85f2c) ((spZ regs, raZ regs, s0Z regs) :: ch) HJ3) end.
- rewrite Ra0. lazymatch type of HS with st_ok _ ?Ex _ _ =>
transitivity (sv_denot Ex (SMd M_MUL (SOff 38 0) (SLit 3)));
[ cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; reflexivity
| exact (denot_mul3 Ex 38 ngp ltac:(cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E38) ltac:(clear - CR28; lia)) ] end.
- rewrite HMM. lia.
- rewrite (blocks_bytes_bsum B ly3 S3), Eab3, bsum_app, <- (blocks_bytes_bsum B ly S). cbn [bsum fold_right snd]. unfold LIVE_NEWGIF, LIVE_MAX in *. lia.
- unfold spZ. rewrite Rsp. evalE AG.
- reflexivity.
- lia.
- rewrite FFS. unfold ASTACK. lia.
- rewrite Rgp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 3%nat) by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
- rewrite Rtp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 4%nat) by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
- exact Rra.
- vm_compute. reflexivity.
- pose proof HJ3 as (_ & _ & _ & _ & _ & _ & Hnev3 & _). rewrite HEV in Hev. unfold VEV_MAX in *. lia.
- pose proof (proj1 (proj2 HJ3)) as HLY3. pose proof HLY3 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop3 & _).
apply (achain_chain_pre ly3 _ (spZ regs - 192) (spZ regs) _ _ (achain_ly_top ly ly3 _ _ _ _ Etop3 Hch1));
[ unfold spZ at 1 2; rewrite Rsp; evalE AG
| unfold s0Z; rewrite Rs0; evalE AG
| unfold raZ; rewrite Rra, unsigned_lit_small by lia; lia ].
- rewrite call_trace_of_spine. cbn [spine map fst snd]. fold (spine ch). unfold raZ at 1. rewrite Rra, unsigned_lit_small by lia. rewrite <- Hra88.
rewrite HBcode, (tl_universe B TL). apply TRACES_cgif_newgif_U. apply memZL_In.
destruct Hspine as [Hsp | Hsp]; rewrite Hsp; vm_compute; reflexivity. }
cbv beta. intros W4 c4 Hwle4 (ly4 & S4 & regs4 & mem4 & md4 & pal & -> & HJ4 & HP4 & Ha04 & Hfrs4 & Hres4).
clear Ra0 Rra Rsp Rgp Rtp Rs0 Hch1 HUP Vra Vs0 Qceil Qal8 Qtop Qtop64 Qsp Qra Qs0.
unfold ASTACK in Hres4. replace (spZ regs + -192 - 16384) with (spZ regs - 16576) in Hres4 by lia. replace (spZ regs + -192) with (spZ regs - 192) in Hres4 by lia.
pose proof (proj1 HJ4) as HAR4. aconsts HROD HJ4 Kgot4 Kcell4 Kguar4 Kuar4 Vgr4.
destruct (al_layout _ _ LAWS _ _ _ _ _ ly4 HAR (proj1 (proj2 HJ4))) as (_ & EFA4 & _).
assert (EFL4 : forall c p, flag_addr ly4 c p = flag_addr ly c p) by (intros c p; unfold flag_addr; pose proof (EFA4 c p) as X; unfold frame_addr in X; lia).
assert (Hfin4 : In (1, fpos) (frames S4)) by (rewrite Hfrs4; exact Hfin3).
assert (HfinS4 : In (cid, pos) (frames S4)) by (rewrite Hfrs4; exact HfinS3).
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR4 Hfin4) as (_ & _ & HFpres4 & HFSpres4). change (fs_frame_bytes 1) with 128 in HFpres4, HFSpres4.
change (128 / 8) with 16 in HFSpres4. rewrite !EFA4 in HFpres4, HFSpres4. fold F in HFpres4, HFSpres4.
destruct Hres4 as [(Hres0 & Eab4 & HK4) | (Hp4096 & Eab4 & HK4)].
+
assert (Hg_in4 : In (g, 96) (ablocks B ly4 S4)) by (rewrite Eab4; exact Hg_in).
assert (HErF : forall a, F <= a < F + 128 -> ~ False) by (intros a Ha Hn; exact Hn).
nunbox HdGC.
reseat HS HJ4 HP4 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11]%nat AG
ltac:(idtac; first [ keptR HK4 HJ4 AG Usp E10 E32 HfinS3 I KgotB Kgot4 KcellB Kcell4 KguarB Kguar4 KuarB Kuar4 VgrB Vgr4 EFA3
| keptF HK4 AG RF E58 Hfin3 HFpres4 HFSpres4 HErF F EFA3
| eapply (region_kept_block_ajw2 trbsegs _ LAWS); [exact HK4 | exact HAR4 | exact Hg_in4
| cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite Rg; apply unsigned_lit_small; lia
| exact Hg_in | lia | change (req_size 96) with 96; lia | lia | lia | intros a Ha Hn; exact Hn]
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
pose proof (st_ok_pin_reg' trbsegs _ _ _ (10%bv : bv 5) 0 HS ltac:(cbn [ms_regs restrict mkst]; rewrite Ha04, Hres0; reflexivity) eq_refl) as HS3.
clear HS. rename HS3 into HS. norm_ss HS. reshok_bx HS 35%nat.
nbox HdGC.
aj_run_tok trbtbl_lib_ok HS HJ4 SHOK NBspan.
all: try (slim; obl_blk HJ4 Rg E35 Hg_in4).
all: try (slim; awrR AG fpos F EFA4).
clear_frames.
clear KgotB KcellB KguarB KuarB VgrB. aconsts HROD HJ4 KgotB KcellB KguarB KuarB VgrB.
rreg HS (10%bv : bv 5) Ra0. rreg HS (1%bv : bv 5) Rra. rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp.
rreg HS (4%bv : bv 5) Rtp. rreg HS (8%bv : bv 5) Rs0.
ng_chain HS HJ4 AG EE.
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
replace (Z_to_bv 64 340932) with (Z_to_bv 64 (pc_wrap_free (as_code B))) by (rewrite HBcode; vm_compute; reflexivity).
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_free_at trbsegs B LAWS Hsegs errno_low ML AFREE _ (ms_regs msX) (ms_mem msX) TNEWGIF_STK (spZ regs) [] ly S W mem md [(1, fpos)]
ly4 S4 _ (k + 1) g 96 (-192) (Z_to_bv 64 0x860bc) ((spZ regs, raZ regs, s0Z regs) :: ch) HJ4 Hg_in4) end.
- rewrite Ra0. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite Rg. reflexivity.
- unfold spZ. rewrite Rsp. evalE AG.
- reflexivity.
- lia.
- rewrite FFS. unfold ASTACK. lia.
- rewrite Rgp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 3%nat) by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
- rewrite Rtp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 4%nat) by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
- exact Rra.
- vm_compute. reflexivity.
- pose proof HJ4 as (_ & _ & _ & _ & _ & _ & Hnev4 & _). rewrite HEV in Hev. unfold VEV_MAX in *. lia.
- pose proof (proj1 (proj2 HJ4)) as HLY4. pose proof HLY4 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop4 & _).
apply (achain_chain_pre ly4 _ (spZ regs - 192) (spZ regs) _ _ (achain_ly_top ly ly4 _ _ _ _ Etop4 Hch1));
[ unfold spZ at 1 2; rewrite Rsp; evalE AG
| unfold s0Z; rewrite Rs0; evalE AG
| unfold raZ; rewrite Rra, unsigned_lit_small by lia; lia ].
- rewrite call_trace_of_spine. cbn [spine map fst snd]. fold (spine ch). unfold raZ at 1. rewrite Rra, unsigned_lit_small by lia. rewrite <- Hra88.
rewrite HBcode, (tl_universe B TL). apply TRACES_cgif_newgif_U. apply memZL_In.
destruct Hspine as [Hsp | Hsp]; rewrite Hsp; vm_compute; reflexivity.
- exact Tg. }
cbv beta. intros W5 c5 Hwle5 (ly5 & S5 & regs5 & mem5 & md5 & -> & HJ5 & HP5 & (l1 & l2 & El1 & Eab5) & Hfrs5 & HK5).
clear Ra0 Rra Rsp Rgp Rtp Rs0 Hch1 HUP Vra Vs0.
unfold ASTACK in HK5. replace (spZ regs + -192 - 16384) with (spZ regs - 16576) in HK5 by lia. replace (spZ regs + -192) with (spZ regs - 192) in HK5 by lia.
pose proof (proj1 HJ5) as HAR5. aconsts HROD HJ5 Kgot5 Kcell5 Kguar5 Kuar5 Vgr5.
destruct (al_layout _ _ LAWS _ _ _ _ _ ly5 HAR (proj1 (proj2 HJ5))) as (_ & EFA5 & _).
assert (EFL5 : forall c p, flag_addr ly5 c p = flag_addr ly c p) by (intros c p; unfold flag_addr; pose proof (EFA5 c p) as X; unfold frame_addr in X; lia).
assert (Hfin5 : In (1, fpos) (frames S5)) by (rewrite Hfrs5; exact Hfin4).
assert (HfinS5 : In (cid, pos) (frames S5)) by (rewrite Hfrs5; exact HfinS4).
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR5 Hfin5) as (_ & _ & HFpres5 & HFSpres5). change (fs_frame_bytes 1) with 128 in HFpres5, HFSpres5.
change (128 / 8) with 16 in HFSpres5. rewrite !EFA5 in HFpres5, HFSpres5. fold F in HFpres5, HFSpres5.
assert (HPerm5 : Permutation (ablocks B ly5 S5) (ablocks B ly S)).
{ rewrite Eab5, <- (app_nil_r (ablocks B ly S)). apply (Permutation_app_inv l1 l2 (ablocks B ly S) [] (g, 96)). rewrite <- El1, Eab4, Eab3. apply Permutation_refl. }
assert (HErF5 : forall a, F <= a < F + 128 -> ~ (g <= a < g + req_size 96)) by (change (req_size 96) with 96; intros a Ha; clear - Ha HdGF; nunbox HdGF; lia).
nunbox HdGC.
reseat HS HJ5 HP5 [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11]%nat AG
ltac:(idtac; first [ keptR HK5 HJ5 AG Usp E10 E32 HfinS4 I KgotB Kgot5 KcellB Kcell5 KguarB Kguar5 KuarB Kuar5 VgrB Vgr5 EFA4
| keptF HK5 AG RF E58 Hfin4 HFpres5 HFSpres5 HErF5 F EFA4
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
nbox HdGC. reshok_bx HS 35%nat.
aj_run_to_tok trbtbl_lib_ok HS HJ5 SHOK NBspan 0x860c0; [slim; awrR AG fpos F EFA5|]. clear_frames.
exitN HS HJ5 AG fpos F cfgp E57 E58 Hfin5 HfinS5 EE Hra HEV EFA5 EFL5.
exists 0. split; [reflexivity|]. left. split; [reflexivity|].
unfold ablocks. rewrite blocks_stack_free_state. fold (ablocks B ly5 S5). exact HPerm5.
+
assert (Hp_in : In (pal, 3 * ngp) (ablocks B ly4 S4)) by (rewrite Eab4; apply in_app_iff; right; left; reflexivity).
assert (Hg_in4 : In (g, 96) (ablocks B ly4 S4)) by (rewrite Eab4; apply in_app_iff; left; exact Hg_in).
assert (Hpala4 : In (pala, 3 * ngp) (ablocks B ly4 S4)) by (rewrite Eab4; apply in_app_iff; left; rewrite Eab3; apply in_app_iff; left; exact Hpala_in).
destruct (al_blocks _ _ LAWS _ _ _ _ _ pal (3 * ngp) HAR4 Hp_in) as (Hp16 & _ & Hpceil & Hph_ia & Hppres4 & _). pose proof (proj1 Hph_ia) as Hph.
pose proof (blk_off_img _ _ _ _ _ _ _ _ HAR4 Hp_in) as Hph_img.
pose proof (aftok_new_block trbsegs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ pal (3 * ngp) HJ3 HAR4 ltac:(rewrite Eab4; reflexivity) ltac:(lia)) as Tp.
assert (Ap : forall blc lyq ownq i, In (pal, 3 * ngp) blc -> 0 <= i < req_size (3 * ngp) -> awr_byte TNEWGIF_STK (spZ regs) [] (ablocks B ly S) blc lyq ownq (pal + i)).
{ intros blc lyq ownq i Hbl Hi. exact (awr_new_block_any trbsegs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ pal (3 * ngp) blc i lyq ownq HJ3 HAR4 ltac:(rewrite Eab4; reflexivity) ltac:(lia) Hbl Hi). }
pose proof (sep_block_frame trbsegs B LAWS ly4 S4 _ _ _ pal (3 * ngp) 1 fpos HAR4 Hp_in Hfin4) as HdPF.
unfold zdisjoint in HdPF. cbn [fst snd] in HdPF. change (fs_frame_bytes 1) with 128 in HdPF. rewrite EFA4 in HdPF. fold F in HdPF.
pose proof (sep_block_frame trbsegs B LAWS ly4 S4 _ _ _ pal (3 * ngp) cid pos HAR4 Hp_in HfinS4) as HdPC.
unfold zdisjoint in HdPC. cbn [fst snd] in HdPC. rewrite EFA4 in HdPC.
assert (HPerm4 : Permutation (ablocks B ly4 S4) ((pal, 3 * ngp) :: (g, 96) :: ablocks B ly S)).
{ rewrite Eab4, Eab3, <- app_assoc. cbn [app]. apply Permutation_sym.
apply (Permutation_trans (perm_swap (g, 96) (pal, 3 * ngp) (ablocks B ly S))).
change ((g, 96) :: (pal, 3 * ngp) :: ablocks B ly S) with ([(g, 96); (pal, 3 * ngp)] ++ ablocks B ly S). apply Permutation_app_comm. }
pose proof (sep_blocks_perm trbsegs B LAWS ly4 S4 _ _ _ (pal, 3 * ngp) (g, 96) _ HAR4 HPerm4) as HdPG.
unfold zdisjoint, block_rng in HdPG. cbn [fst snd] in HdPG. change (req_size 96) with 96 in HdPG.
assert (HErF : forall a, F <= a < F + 128 -> ~ (pal <= a < pal + req_size (3 * ngp))) by (intros a Ha; clear - Ha HdPF; lia).
nbox HdPF. nbox HdPG.
reseat HS HJ4 HP4 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11]%nat AG
ltac:(idtac; first [ keptR HK4 HJ4 AG Usp E10 E32 HfinS3 I KgotB Kgot4 KcellB Kcell4 KguarB Kguar4 KuarB Kuar4 VgrB Vgr4 EFA3
| keptF HK4 AG RF E58 Hfin3 HFpres4 HFSpres4 HErF F EFA3
| eapply (region_kept_block_ajw2 trbsegs _ LAWS); [exact HK4 | exact HAR4 | exact Hg_in4
| cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite Rg; apply unsigned_lit_small; lia
| exact Hg_in | lia | change (req_size 96) with 96; lia | lia | lia | intros a Ha Hn; clear - Ha Hn HdPG; nunbox HdPG; lia]
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
nbox HdPC.
rreg HS (10%bv : bv 5) Rp. cbn [ms_regs] in Rp. rewrite Ha04 in Rp. symmetry in Rp. unfold w64 in Rp.
lazymatch type of Rp with ew ?Ex ?nx = _ =>
pose proof (st_ok_add_fact trbsegs Ex _ _ nx (HPTR 4) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite Rp, unsigned_lit_small by lia; change (2 ^ 4) with 16; lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS. reshok_bx HS 35%nat.
lazymatch type of HS with st_ok _ ?Ev ?ssx (restrict _ ?msv) =>
change ssx with ss_NG1 in HS;
eapply (NGG ly S W regs mem md ch cfgp pal0 pala attr gen Wd Hd ngp loops rest cid pos E0 Ev W4 ly4 S4 msv _ (k + 1) fpos g pal);
[ split; [exact HPRE | split; [exact Hal32 | split; [| split; [exact Hroom | split; [exact Htop32 | split; [exact HROD | split; [exact Hcfg | split; [exact HWH | split; [exact Hpala | split; [rewrite Ha4; cbn [Z.eqb app]; exact HPerm | split; [exact Hev | exact Hlive]]]]]]]]]]]
| split; [exact Hfin | split; [exact Hcid0 | split; [exact Hfal | split; [exact Hflo | split; [exact Hfhi | split; [exact Hcal | exact HRA]]]]]]
| split; [exact EE | split; [exact E10 | split; [exact E32 | exact Usp]]]
| split; [exact AG | repeat (split; [eassumption|]); eassumption]
| exact Rg | exact Rp
| split; [exact HJ4 | split; [clear - Hk3; lia | split; [rewrite Hfrs4; exact Hfrs3 | split; [rewrite Eab4, Eab3; reflexivity | split; [exact Hg4096 | split; [exact Hp4096 | split; [exact Tg | split; [exact Ag | split; [exact Tp | exact Ap]]]]]]]]]
| exact HW0 | exact HH0 | exact Ha4 | exact Epala
| exact HS ] end.
rewrite <- Hra88. destruct Hspine as [Hs | Hs]; rewrite Hs; cbn; tauto.
Qed.
End d. End b.
