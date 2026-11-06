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
YG00 YG0a YG01 YG0h YG0u YG0d YC04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YC19 YF8z YC1d YC1a YC2o YC10 YC2p YC0x YC1b YC2u YC3p YC3q.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Lemma ngG_land_low_mod : forall x m k, 0 <= k -> 0 <= m < 2 ^ k -> Z.land (x mod 2 ^ k) m = Z.land x m.
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
Section c.
Variable B : asyms.
Hypothesis TL : TraLib B.
Hypothesis LAWS : AR_laws trasegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AMALLOC : amalloc_realizes trasegs B.
Hypothesis AFREE : afree_realizes trasegs B.
Hypothesis AMEMSET : aintrin_realizes trasegs B OSet A_asan_memset.
Hypothesis AMEMCPY : aintrin_realizes trasegs B OCpy A_asan_memcpy.
Hypothesis ASF : astack_free_law trasegs B.
Hypothesis FFL : frame_flag_lawP trasegs B.
Let HBcode := tl_code B TL. Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL.
Let HBguar := tl_got_uar B TL. Let HBuar := tl_uar_cell B TL. Let errno_low := tl_env B TL.
Local Notation code := (as_code B).
Lemma ng_G : NG_P1_stmt B -> NG_G_stmt B.
Proof.
intros NGP1 ly S W regs mem md ch cfgp pal0 pala attr gen Wd Hd ngp loops rest cid pos E0 E W3 ly3 S3 ms3 md3 k fpos g pal HCTX HCFG HE0 HE Rg Rp HNOW HW0 HH0 Ha4 Epala HS.
ng_facts HCTX HCFG HE0 HE.
destruct HNOW as (HJ3 & Hk3 & Hfrs3 & Eab3 & Hg4096 & Hp4096 & Tg & Ag & Tp & Ap).
ng_frame HJ3 Hfrs3.
pose proof (req_size_pos (3 * ngp) ltac:(clear - CR28; lia)) as [Hrq1 Hrq2].
rewrite Ha4 in HPerm. cbn [Z.eqb app] in HPerm.
assert (HPerm3 : Permutation (ablocks B ly3 S3) ((pal, 3 * ngp) :: (g, 96) :: (pala, 3 * ngp) :: rest)).
{ rewrite Eab3, <- app_assoc. cbn [app]. apply Permutation_sym.
apply (Permutation_trans (perm_swap (g, 96) (pal, 3 * ngp) _)).
change ((g, 96) :: (pal, 3 * ngp) :: (pala, 3 * ngp) :: rest) with ([(g, 96); (pal, 3 * ngp)] ++ ((pala, 3 * ngp) :: rest)).
eapply Permutation_trans; [apply Permutation_app_comm|]. apply Permutation_app; [apply Permutation_sym; exact HPerm | apply Permutation_refl]. }
assert (Hp_in : In (pal, 3 * ngp) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm3|]; left; reflexivity).
assert (Hg_in : In (g, 96) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm3|]; right; left; reflexivity).
assert (Hpala3 : In (pala, 3 * ngp) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm3|]; right; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ g 96 HAR3 Hg_in) as (Hg16 & _ & Hgceil & Hgh_ia & Hgpres3 & _). pose proof (proj1 Hgh_ia) as Hgh. change (req_size 96) with 96 in Hgceil, Hgpres3.
pose proof (blk_off_img _ _ _ _ _ _ g 96 HAR3 Hg_in) as Hgh_img.
destruct (al_blocks _ _ LAWS _ _ _ _ _ pal (3 * ngp) HAR3 Hp_in) as (Hp16 & _ & Hpceil & Hph_ia & Hppres3 & _). pose proof (proj1 Hph_ia) as Hph.
pose proof (blk_off_img _ _ _ _ _ _ _ _ HAR3 Hp_in) as Hph_img.
destruct (al_blocks _ _ LAWS _ _ _ _ _ pala (3 * ngp) HAR3 Hpala3) as (_ & Hpala4096 & Hpalaceil & Hpalah_ia & Hpalapres3 & _). pose proof (proj1 Hpalah_ia) as Hpalah.
pose proof (blk_off_img _ _ _ _ _ _ _ _ HAR3 Hpala3) as Hpalah_img.
pose proof (sep_block_frame trasegs B LAWS ly3 S3 _ _ _ g 96 1 fpos HAR3 Hg_in Hfin3) as HdGF.
unfold zdisjoint in HdGF. cbn [fst snd] in HdGF. change (req_size 96) with 96 in HdGF. change (fs_frame_bytes 1) with 128 in HdGF. rewrite EFA3 in HdGF. fold F in HdGF.
pose proof (sep_block_frame trasegs B LAWS ly3 S3 _ _ _ g 96 cid pos HAR3 Hg_in HfinS3) as HdGC.
unfold zdisjoint in HdGC. cbn [fst snd] in HdGC. change (req_size 96) with 96 in HdGC. rewrite EFA3 in HdGC.
pose proof (sep_block_frame trasegs B LAWS ly3 S3 _ _ _ pal (3 * ngp) 1 fpos HAR3 Hp_in Hfin3) as HdPF.
unfold zdisjoint in HdPF. cbn [fst snd] in HdPF. change (fs_frame_bytes 1) with 128 in HdPF. rewrite EFA3 in HdPF. fold F in HdPF.
pose proof (sep_block_frame trasegs B LAWS ly3 S3 _ _ _ pal (3 * ngp) cid pos HAR3 Hp_in HfinS3) as HdPC.
unfold zdisjoint in HdPC. cbn [fst snd] in HdPC. rewrite EFA3 in HdPC.
pose proof (sep_blocks_perm trasegs B LAWS ly3 S3 _ _ _ (pal, 3 * ngp) (g, 96) _ HAR3 HPerm3) as HdPG.
unfold zdisjoint, block_rng in HdPG. cbn [fst snd] in HdPG. change (req_size 96) with 96 in HdPG.
pose proof (sep_blocks_perm trasegs B LAWS ly3 S3 _ _ _ (pal, 3 * ngp) (pala, 3 * ngp) _ HAR3 (Permutation_trans HPerm3 (perm_skip _ (perm_swap _ _ _)))) as HdPP.
unfold zdisjoint, block_rng in HdPP. cbn [fst snd] in HdPP.
nbox_seps.
aconsts HROD HJ3 Kgot3 Kcell3 Kguar3 Kuar3 Vgr3.
assert (E10' : ew E 10 = Z_to_bv 64 cfgp) by (rewrite (AG 10%nat) by lia; exact E10).
reshok_bx HS 35%nat.
aj_run_tok tratbl_lib_ok HS HJ3 SHOK NBspan.
all: try (slim; obl_blk HJ3 Rg E35 Hg_in).
all: try (slim; oblF HJ3 E10' E35 HRA HAR Hfin Hcid0 Hflo Hfhi Hfal).
all: try (slim; awrR AG fpos F EFA3).
clear_frames.
rreg HS (10%bv : bv 5) Ra0. rreg HS (11%bv : bv 5) Ra1. rreg HS (12%bv : bv 5) Ra2. rreg HS (1%bv : bv 5) Rra.
rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp.
rewrite (st_ok_restrict_mkst trasegs _ _ _ _ HS eq_refl). cbn [ss_pc].
change (Z_to_bv 64 335280) with (Z_to_bv 64 A_asan_memcpy).
assert (Qps : pala + 3 * ngp <= spZ regs - 192 - ESTACK) by (unfold ESTACK; clear - Hpalaceil Hrq2 Hslo Hceil FFS; lia).
clear Kgot3 Kcell3 Kguar3 Kuar3 Vgr3. aconsts HROD HJ3 Kgot3 Kcell3 Kguar3 Kuar3 Vgr3.
destruct (al_blocks _ _ LAWS _ _ _ _ _ pala (3 * ngp) (proj1 HJ3) Hpala3) as (_ & _ & _ & _ & HpalapresX & _).
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_intrin_at trasegs B LAWS Hsegs OCpy A_asan_memcpy AMEMCPY _ (ms_regs msX) (ms_mem msX) TNEWGIF_STK (spZ regs) [] ly S W mem md [(1, fpos)]
ly3 S3 _ _ pal pala (3 * ngp) (-192) (Z_to_bv 64 0x858a0) HJ3) end.
- rewrite Ra0. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite Rp. reflexivity.
- rewrite Ra1. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 32%nat) by lia. rewrite E32, Epala. reflexivity.
- rewrite Ra2. lazymatch type of HS with st_ok _ ?Ex _ _ =>
transitivity (sv_denot Ex (SMd M_MUL (SOff 38 0) (SLit 3)));
[ cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; reflexivity
| exact (denot_mul3 Ex 38 ngp ltac:(cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E38) ltac:(clear - CR28; lia)) ] end.
- clear - CR28; lia. - clear - Hp4096; lia. - clear - Hpceil Hrq2 C1; lia.
- unfold spZ at 1. rewrite Rsp. evalE AG.
- reflexivity. - lia. - rewrite FFS. unfold ESTACK. lia.
- rewrite Rgp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 3%nat) by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
- rewrite Rtp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 4%nat) by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
- exact Rra.
- vm_compute. reflexivity.
- intros a Ha. split; [replace a with (pal + (a - pal)) by lia; apply Ap; [exact Hp_in | clear - Ha Hrq2; lia] | unfold ESTACK; clear - Ha Hpceil Hrq2 Hslo Hceil FFS; lia].
- apply (amem_range_of_block trasegs B LAWS ly3 S3 _ _ _ pal (3 * ngp) _ _ (proj1 HJ3) Hp_in); clear - Hrq2; lia.
- apply (range_addressable_of_block trasegs B LAWS ly3 S3 _ _ _ pal (3 * ngp) _ _ (proj1 HJ3) Hp_in); clear - Hrq2; lia.
- intros Hn0. apply (shadow_hull_vis_of_block trasegs B LAWS ly3 S3 _ _ _ pal (3 * ngp) _ _ (proj1 HJ3) Hp_in); clear - Hrq2 Hn0; lia.
- split; [clear - Hpala4096; lia|]. split; [clear - Hpalaceil Hrq2 C1; lia|]. split.
{ intros a Ha. split; [| unfold spZ; rewrite Rsp; evalE AG].
apply (aview_some_of_apresent trasegs). apply (proj1 (HpalapresX a ltac:(clear - Ha Hrq2; lia))). }
split; [nunbox HdPP; clear - HdPP Hrq2; lia|].
split; [apply (amem_range_of_block trasegs B LAWS ly3 S3 _ _ _ pala (3 * ngp) _ _ (proj1 HJ3) Hpala3); clear - Hrq2; lia|]. split.
+ apply (range_addressable_of_block trasegs B LAWS ly3 S3 _ _ _ pala (3 * ngp) _ _ (proj1 HJ3) Hpala3); clear - Hrq2; lia.
+ intros Hn0. apply (shadow_hull_vis_of_block trasegs B LAWS ly3 S3 _ _ _ pala (3 * ngp) _ _ (proj1 HJ3) Hpala3); clear - Hrq2 Hn0; lia. }
cbv beta. intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & HP4 & Ha04 & Heff & Hfr4 & Hpres4).
clear Ra0 Ra1 Ra2 Rra Rsp Rgp Rtp.
aconsts HROD HJ4 Kgot4 Kcell4 Kguar4 Kuar4 Vgr4.
nunbox HdPG. nunbox HdPF. nunbox HdPC.
reseat HS HJ4 HP4 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11]%nat AG
ltac:(idtac; first [ keptI Hfr4 Hpres4 AG Kgot3 Kgot4 Kcell3 Kcell4 Kguar3 Kguar4 Kuar3 Kuar4 Vgr3 Vgr4
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
nbox HdPG. nbox HdPF. nbox HdPC.
reshok_bx HS 35%nat. clear_frames.
clear E10'. lazymatch type of HS with st_ok _ ?Ex _ _ => assert (E10' : ew Ex 10 = Z_to_bv 64 cfgp) by (rewrite (AG 10%nat) by lia; exact E10) end.
aj_run_to_tok tratbl_lib_ok HS HJ4 SHOK NBspan 0x858f4.
all: try (slim; oblF HJ4 E10' E35 HRA HAR Hfin Hcid0 Hflo Hfhi Hfal).
all: try (slim; awrR AG fpos F EFA3).
clear_frames.
srr_branch_tok tratbl_lib_ok HS SHOK NBspan.
1: { exfalso. ng_attr4_hc Hc E33 attr ngG_land_low_mod. rewrite Ha4 in Hc. cbn in Hc. discriminate Hc. }
clear Hc.
aj_run_to_tok tratbl_lib_ok HS HJ4 SHOK NBspan 0x858f4.
all: try (slim; oblF HJ4 E10' E35 HRA HAR Hfin Hcid0 Hflo Hfhi Hfal).
all: try (slim; awrR AG fpos F EFA3).
clear_frames.
lazymatch type of HS with st_ok _ ?Ev ?ssx (restrict _ ?msv) =>
change ssx with ss_NP1 in HS;
eapply (NGP1 ly S W regs mem md ch cfgp pal0 pala attr gen Wd Hd ngp loops rest cid pos E0 Ev W3 ly3 S3 msv _ k fpos g pal);
[ split; [exact HPRE | split; [exact Hal32 | split; [| split; [exact Hroom | split; [exact Htop32 | split; [exact HROD | split; [exact Hcfg | split; [exact HWH | split; [exact Hpala | split; [rewrite Ha4; cbn [Z.eqb app]; exact HPerm | split; [exact Hev | exact Hlive]]]]]]]]]]]
| split; [exact Hfin | split; [exact Hcid0 | split; [exact Hfal | split; [exact Hflo | split; [exact Hfhi | split; [exact Hcal | exact HRA]]]]]]
| split; [exact EE | split; [exact E10 | split; [exact E32 | exact Usp]]]
| split; [intros n Hn; rewrite !ew_ewset_other by lia; apply AG; exact Hn | repeat split; rewrite !ew_ewset_other by lia; assumption]
| rewrite !ew_ewset_other by lia; exact Rg | rewrite !ew_ewset_other by lia; exact Rp
| split; [exact HJ4 | split; [exact Hk3 | split; [exact Hfrs3 | split; [exact Eab3 | split; [exact Hg4096 | split; [exact Hp4096 | split; [exact Tg | split; [exact Ag | split; [exact Tp | exact Ap]]]]]]]]]
| exact HW0 | exact HH0 | exact Ha4 | exact Epala
| exact HS ] end.
rewrite <- Hra88. destruct Hspine as [Hs | Hs]; rewrite Hs; cbn; tauto.
Qed.
End c. End b.
