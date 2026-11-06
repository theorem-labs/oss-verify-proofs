(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI0m YI0n YI5w YI5z.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0z YC4a YC8i YC80 YC1f YC81 YC4b.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC8g.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCjp.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC8h.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCh9 YChc.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section e.
Context {PI : PAImg lib_both3_0_listing}.
Context {RO : YC8g.ro_below_ofl (@pa_segs _ lib_both3_0_listing PI) (@pa_relro_lo _ lib_both3_0_listing PI) (@pa_relro_hi _ lib_both3_0_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
#[local] Notation WFN_ADDR := (BASE + WFN_OFF).
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AFREE : afree_realizes SEGS B.
Variable hw : Z.
Variable CTX : list (list Z).
Hypothesis HUfc : In [pc_free_ra0 (as_code B); BASE + 0x76c] (as_universe B).
Hypothesis HUff1 : In [pc_free_ra0 (as_code B); BASE + 0x2e1c] (as_universe B).
Hypothesis HUff2 : In [pc_free_ra0 (as_code B); BASE + 0x2e54] (as_universe B).
Hypothesis HUrfc : In [pc_free_ra0 (as_code B); BASE + CL_RET_FREECGIF] (as_universe B).
Hypothesis HUrff : In [pc_free_ra0 (as_code B); BASE + CL_RET_FREEFRAME] (as_universe B).
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_both3_0) (PI := PI).
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL.
Lemma regsFR_ok : forall (i : Z) (regs regs1 : bvmap 5 word) g s1,
cl_regs_at B regs regs1 g ->
getr regs1 21 = w64 (8 * i) -> getr regs1 22 = w64 24 ->
4096 <= g -> g + 96 <= alloc_ceiling ->     0 <= i <= 2 ->
regs_ok (Eimg (Ereg regs1 (cl_extra regs g s1))) (regsFR i) regs1.
Proof.
intros i regs regs1 g s1 (R2 & R3 & R4 & R8 & R9 & R19 & R18 & R20' & _) R21 R22 Hlo Hhi Hi.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (E := Eimg (Ereg regs1 (cl_extra regs g s1))). assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r) by (intros n r Hn; subst E; pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 g) by (subst E; change 32%nat with (32 + 0)%nat; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_extra regs1 _ 0); reflexivity).
assert (E38 : ew E 38 = Z_to_bv 64 SB) by (subst E; change 38%nat with (32 + 6)%nat; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_extra regs1 _ 6); reflexivity).
apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<- | Hr];
[ lazymatch goal with |- getr _ _ = sv_denot _ (sr_get ?a ?rr2) => let v := eval cbv -[Z.mul Z.add Z.sub Z.opp] in (sr_get a rr2) in change (sr_get a rr2) with v end;
first [ rewrite (denot_shx E 32 38 _ g SB E32 E38) by (unfold SB; lia); exact R19
| cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
first [ symmetry; apply EE; reflexivity | symmetry; apply getr_zero | reflexivity
| rewrite E32; exact R8
| rewrite E38; exact R18
| rewrite E32, unsigned_lit_small by lia; exact R9
| first [exact R21 | exact R22] ] ]
| ]); try (destruct Hr; fail).
Qed.
Lemma cl_alu64_addw : forall a b, alu64 ALU_ADD (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
Proof.
intros a b. rewrite alu_add. unfold v_add. apply Z_to_bv64_eq_mod.
rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite <- Zplus_mod. reflexivity.
Qed.
Lemma cl_AFT2_ok : CL_AFTER_stmt B hw CTX 2.
Proof.
intros ly S W regs mem md ch g s N rest lyc Sc Wc regs1 memc mdc k s1 CX MID Hk HR R21 R22.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof CX as (HPRE & Hctx & Hfr7 & HROD & H10 & HT & HWF & HPerm & Hev & Hlive).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof MID as (HJ & Hk0 & HFR & HT1 & HOK & HPerm1).
pose proof HOK as (HWF1 & Hraw1 & Hattr1 & Hpal1 & Hngp1 & Hfrm1).
pose proof HR as (Rsp & Rgp & Rtp & R8 & R9 & R19 & R18 & R20 & Rhi).
pose proof (proj1 HJ) as HAR. pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & Hnev & _ & _ & _ & _ & _ & _ & Hpres & _).
assert (HTS : TCLOSE_STK = 17520) by reflexivity.
set (sp0 := spZ regs) in *.
assert (Hing : In (g, CGIF_SIZE) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]. left. reflexivity. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ g CGIF_SIZE HAR Hing) as (Hg16 & Hg4096 & Hgceil & Hgh_ia & _ & _). pose proof (proj1 Hgh_ia) as Hgh.
pose proof (blk_off_imgP _ _ _ _ _ _ g CGIF_SIZE HAR Hing) as Hgh_img.
change (req_size CGIF_SIZE) with 96 in Hgceil, Hgh, Hgh_img.
destruct (cl_seed B LAWS TL hw CL_RET_FREEFRAME (regsFR 2) true Wc regs regs1 memc lyc Sc mdc ly sp0 g s1 HAR Hing Hstk Hpres
ltac:(unfold spZ in Rsp |- *; rewrite Rsp; rewrite unsigned_lit_small by lia; lia)
(regsFR_ok 2 regs regs1 g s1 HR R21 R22 Hgh Hgceil ltac:(lia)) (fun _ => HFR) (fun _ => R20) (proj1 HT1)) as [HS SHOK].
set (E := Eimg (Ereg regs1 (cl_extra regs g s1))) in *. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (Usp : bv_unsigned (ew E 2) = sp0 - 80) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs1 _ 2 2%bv eq_refl); unfold spZ in Rsp |- *; rewrite Rsp; apply unsigned_lit_small; lia).
assert (E32u : bv_unsigned (ew E 32) = g) by (subst E; change 32%nat with (32 + 0)%nat; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_extra regs1 _ 0); cbn [nth cl_extra map app]; apply unsigned_lit_small; lia).
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros n rr Hn; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
assert (EXo : forall j, (j < 100)%nat -> ew E (32 + j) = nth j (cl_extra regs g s1) (Z_to_bv 64 0)) by (intros j Hj; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (E37 : ew E 37 = Z_to_bv 64 (cg_cur s1)) by (change 37%nat with (32 + 5)%nat; rewrite EXo by (clear; lia); reflexivity).
assert (E38 : ew E 38 = Z_to_bv 64 SB) by (change 38%nat with (32 + 6)%nat; rewrite EXo by (clear; lia); reflexivity).
assert (E39 : ew E 39 = Z_to_bv 64 (cg_pal s1)) by (change 39%nat with (32 + 7)%nat; rewrite EXo by (clear; lia); reflexivity).
assert (E40 : ew E 40 = Z_to_bv 64 (cg_attr s1)) by (change 40%nat with (32 + 8)%nat; rewrite EXo by (clear; lia); reflexivity).
pose proof (obj_at_nth SEGS _ _ _ _ 3 (24, 8%N) (cg_pal s1) (proj1 HT1) eq_refl eq_refl) as [_ Rpal].
pose proof (obj_at_nth SEGS _ _ _ _ 5 (40, 4%N) (cg_attr s1) (proj1 HT1) eq_refl eq_refl) as [_ Rattr].
pose proof (obj_at_nth SEGS _ _ _ _ 9 (52, 2%N) (cg_ngp s1) (proj1 HT1) eq_refl eq_refl) as [_ Rngp].
pose proof (obj_at_nth SEGS _ _ _ _ 15 (88, 4%N) (cg_cur s1) (proj1 HT1) eq_refl eq_refl) as [_ Rcur]. cbn [snd] in Rpal, Rattr, Rngp, Rcur.
paj_run_to_tok RUNTO HS HJ SHOK RBspanC A_freeCGIF.
{ awr_cl Usp E32u Hing HTS. }
pmkst HS.
prreg HS (2%bv : bv 5) P2; prreg HS (10%bv : bv 5) P10; prreg HS (3%bv : bv 5) P3; prreg HS (4%bv : bv 5) P4; prreg HS (1%bv : bv 5) P1; prreg HS (8%bv : bv 5) P8; prreg HS (9%bv : bv 5) P9.
lazymatch type of HS with
| st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
let r := eval vm_compute in (nth 3 (ss_mem ssx) got_regionP) in
pose proof (st_ok_pi_region_nth E ssx (restrict _ msx) 3 r HS ltac:(vm_compute; reflexivity)) as HRg; cbn [ms_mem restrict mkst] in HRg
| st_ok _ _ ?ssx (restrict _ ?msx) =>
let r := eval vm_compute in (nth 3 (ss_mem ssx) got_regionP) in
pose proof (st_ok_region_nth E ssx (restrict _ msx) 3 r HS ltac:(vm_compute; reflexivity)) as HRg; cbn [ms_mem restrict mkst] in HRg end.
pose proof (field_of_region E _ 32 g _ _ _ _ _ 24 8 (SOff 39 0) (cg_pal s1) HRg E32u ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite E39, unsigned_lit_small, Z.add_0_r by lia; reflexivity) ltac:(clear - Rpal; cbn; lia) ltac:(cbn; lia)) as Vpal.
pose proof (field_of_region E _ 32 g _ _ _ _ _ 40 4 (SOff 40 0) (cg_attr s1) HRg E32u ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite E40, unsigned_lit_small, Z.add_0_r by lia; reflexivity) ltac:(clear - Rattr; cbn; lia) ltac:(cbn; lia)) as Vattr.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
assert (P3' : getr rg 3 = w64 (as_gp B)) by (rewrite P3, (EEo 3%nat 3%bv eq_refl); exact Rgp);
assert (P4' : getr rg 4 = w64 (as_tp B)) by (rewrite P4, (EEo 4%nat 4%bv eq_refl); exact Rtp);
assert (Psp : spZ rg = sp0 + -80) by (unfold spZ; rewrite P2, Usp; lia);
assert (P10' : getr rg 10 = w64 g) by (rewrite P10, <- E32u; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity) end.
pose proof HJ as (_ & HLYc & _). pose proof HLYc as (_ & _ & _ & _ & _ & _ & _ & _ & Etopc & _).
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
assert (Ps0 : achain lyc (aview SEGS (w_H Wc) mm) (sp0 + -80) (s0Z rg) []) end.
{   apply achain_low. unfold s0Z. rewrite P8. cbn [sv_denot]. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned, E32u. clear - Hgceil. lia. }
assert (HEVc : st_nev Sc + 2 <= EV_MAX).
{ pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev2 & _). clear - Hnev2 Hk Hev Hk0. lia. }
pose proof HUfc as HU1.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
assert (HU3 : In (call_trace0 (pc_free_ra0 (as_code B)) rg []) (as_universe B))
by (unfold call_trace0, unwind_of_chain, raZ; rewrite P1, unsigned_lit_small by lia; cbn; rewrite (proj2 (Z.eqb_neq _ _)) by (pose proof (proj1 (pal_rt_below B TL)); lia); cbn; first [exact HUrfc | exact HUrff]) end.
assert (HPc : Permutation (ablocks B lyc Sc) (fc_blocks g (cg_pal s) (cg_attr s) (cg_ngp s) ++ rest)).
{ eapply Permutation_trans; [exact HPerm1|]. unfold fr_blocks. change (Datatypes.S (Z.to_nat 2)) with 3%nat.
rewrite (skipn_all2 (cg_frames s)) by (rewrite (proj1 HWF); lia). cbn [frames_blocks flat_map app]. rewrite app_nil_r.
unfold fc_blocks, pal_blocks. change CGIF_OBJ with CGIF_SIZE. apply Permutation_refl. }
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
eapply SRr_bind;
[ eapply (cl_call B LAWS Wc rg mm _ TCLOSE_STK sp0 (FPc g s N) ly S W mem md [] lyc Sc mdq k FC_STK
(ablocks_fp (fc_blocks g (cg_pal s) (cg_attr s) (cg_ngp s))) 2 (-80) (Z_to_bv 64 (BASE + 0x301c)) []
(fun ly3 S3 W3 regs3 mem3 md3 => Permutation (ablocks B ly3 S3) rest) HJ Psp);
[ reflexivity | lia | unfold FC_STK, ASTACK; lia | rewrite HTS; unfold FC_STK, ASTACK; lia
| exact P3' | exact P4' | exact P1 | apply ret_ok_codeptr_v; [cbv; split; [congruence | reflexivity] | reflexivity] | rewrite unsigned_lit_small by lia; lia
| exact Ps0
| intros HPRE1; eapply SRr_mono;
[ eapply (pb_freeCGIF B LAWS TL ML AFREE Wc lyc Sc rg mm _ [] g (cg_pal s) (cg_attr s) (cg_ngp s) rest HPRE1 HEVc P10');
[ rewrite <- Hpal1; exact Vpal | rewrite <- Hattr1; exact Vattr | rewrite <- Hpal1; exact Rpal | rewrite <- Hattr1; exact Rattr
| rewrite <- Hngp1; clear - Rngp; lia | exact HPc | exact HU1 | exact HU3 ]
| cbv beta; unfold fc_post; intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ1 & HP & HK);
exists ly3, S3, regs3, mem3, md3; split; [rewrite P1; reflexivity | split; [exact HJ1 | split; [exact HP | exact HK]]] ]
| intros a (r & Hr & Ha); left; split;
[ unfold FPc, cgif_blocks; unfold fc_blocks in Hr; exists r; split; [|exact Ha];
cbn [ablocks_fp map app] in Hr |- *; destruct Hr as [<- | Hr]; [left; reflexivity | right; right];
unfold pal_blocks; destruct (Z.land (cg_attr s) 4 =? 0); [destruct Hr as [<- | []]; left; reflexivity | destruct Hr]
| unfold fc_blocks in Hr; cbn [ablocks_fp map app] in Hr;
destruct Hr as [<- | Hr];
[ exists g, CGIF_OBJ; split; [exact Hing | cbn [fst snd] in Ha; exact Ha]
| destruct (Z.land (cg_attr s) 4 =? 0) eqn:Ha4; [destruct Hr as [<- | []] | destruct Hr];
exists (cg_pal s), (3 * cg_ngp s); split; [| cbn [fst snd] in Ha; exact Ha];
eapply Permutation_in; [apply Permutation_sym; exact HPc|]; unfold fc_blocks; rewrite Ha4; right; left; reflexivity ] ] ]
| ] end.
cbv beta. intros W3 c3 Hwle3 (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HJc3 & HP3 & HPerm3).
pose proof (proj1 HJ3) as HAR3.
destruct (al_const _ _ LAWS _ _ _ _ _ (proj1 HJ)) as (Kcellb & _ & Kgotb & _). rewrite HBgot, HBcell in Kgotb. rewrite HBcell in Kcellb.
destruct (al_const _ _ LAWS _ _ _ _ _ HAR3) as (Kcellc & _ & Kgotc & _). rewrite HBgot, HBcell in Kgotc. rewrite HBcell in Kcellc.
jafter_call_keep_pi HS 51%nat regs3 (mrestrict (w_H W3) mem3) HP3 [0; 1; 2]%nat HS3.
match type of HS3 with ?t -> _ => assert (HRK : t); [|specialize (HS3 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| | | apply Forall_nil].
- eapply (region_kept_stack_sub SEGS B); [exact HJc3 | exact HJ3 | exact Usp | lia | rewrite HTS; lia | lia | cbn; lia | cbn; lia].
- apply (region_kept_val_at E _ _ (A_OBJ 0) (VAL (A_OBJ 0)) 8 (VAL (A_OBJ 12)));
[exact (HEI (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact (val_mem_of_rdword SEGS _ _ _ _ Kgotb) | exact (val_mem_of_rdword SEGS _ _ _ _ Kgotc) | lia].
- apply (region_kept_val_at E _ _ (A_OBJ 12) (VAL (A_OBJ 12)) 8 SHADOW_OFF);
[exact (HEI (A_OBJ 12) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact (val_mem_of_rdword SEGS _ _ _ _ Kcellb) | exact (val_mem_of_rdword SEGS _ _ _ _ Kcellc) | lia]. }
clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
remember (havoc E 51 (map (getr regs3) CLOB)) as E3 eqn:HE3 in HS. assert (HEI3 : img_env VAL A_LIM E3) by (rewrite HE3; apply img_env_havoc; [first [exact HEI | assumption] | cbv; lia]).
assert (OLD3 : forall n, (n < 51)%nat -> ew E3 n = ew E n) by (intros n Hn; rewrite HE3; apply YN3v.ew_havoc_old; exact Hn).
clear HE3.
assert (Usp3 : bv_unsigned (ew E3 2) = sp0 - 80) by (rewrite OLD3 by lia; exact Usp).
shok_auto SHOK3 Bxc E3 (mrestrict (w_H W3) mem3).
paj_run_tok RUN HS HJ3 SHOK3 RBspanC.
{ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?lyx ?own =>
let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk spx fp b0 bc lyx own) end.
apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
prreg HS (1%bv : bv 5) F1.
eapply (RET W3 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold cl_post.
lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists ly3, S3, r, m, d end.
assert (E41 : ew E3 41 = getr regs 1) by (rewrite OLD3 by lia; change 41%nat with (32 + 9)%nat; rewrite EXo by (clear; lia); reflexivity).
split; [cbn [ms_regs]; rewrite F1, E41, Hra; reflexivity|].
split; [|split; [|exact HPerm3]].
{ cbn [ms_mem]. eapply (ajournal_mono_k SEGS B); [apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ3 | lia]. }
unfold aregs_preserved. intros r Hr.
assert (Hcases : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27 \/ False)
by (unfold acallee_saved in Hr; lia).
clear Hr.
repeat (destruct Hcases as [-> | Hcases]); [..| destruct Hcases];
((first [rewrite (st_ok_pi_restrict_reg (w_H W3) E3 _ _ _ HS) | rewrite (st_ok_restrict_reg SEGS (w_H W3) E3 _ _ _ HS)]); cbn [ms_regs];
lazymatch goal with |- sv_denot _ (sr_get ?a ?rr2) = _ => let v := eval vm_compute in (sr_get a rr2) in change (sr_get a rr2) with v end;
cbn [sv_denot]; rewrite ?OLD3 by lia).
all: try (rewrite Z.add_0_r, Z_to_bv_bv_unsigned).
all: try (lazymatch goal with |- ew _ ?n = getr _ (Z_to_bv 5 ?rr) =>
first [ rewrite (EEo n (Z_to_bv 5 rr) eq_refl); apply Rhi; lia
| let j := eval compute in (n - 32)%nat in change n with (32 + j)%nat; rewrite (EXo j) by (clear; lia); reflexivity ] end).
- replace (Z_to_bv 5 2) with (2%bv : bv 5) by (apply bv_eq; reflexivity). rewrite (EEo 2%nat 2%bv eq_refl), Rsp. unfold w64. rewrite unsigned_lit_small by lia.
replace (sp0 - 80 + 80) with sp0 by lia. subst sp0. unfold spZ. apply Z_to_bv_bv_unsigned.
- replace (Z_to_bv 5 3) with (3%bv : bv 5) by (apply bv_eq; reflexivity). rewrite (EEo 3%nat 3%bv eq_refl), Rgp, Hgp. reflexivity.
- replace (Z_to_bv 5 4) with (4%bv : bv 5) by (apply bv_eq; reflexivity). rewrite (EEo 4%nat 4%bv eq_refl), Rtp, Htp. reflexivity.
Qed.
Lemma cl_FR2_ok : CL_AFTER_stmt B hw CTX 2 -> CL_FR_stmt B hw CTX 2.
Proof.
intros AFT ly S W regs mem md ch g s N rest lyc Sc Wc regs1 memc mdc k s1 CX MID Hk HR R21 R22.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof CX as (HPRE & Hctx & Hfr7 & HROD & H10 & HT & HWF & HPerm & Hev & Hlive).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof MID as (HJ & Hk0 & HFR & HT1 & HOK & HPerm1).
pose proof HOK as (HWF1 & Hraw1 & Hattr1 & Hpal1 & Hngp1 & Hfrm1).
pose proof HR as (Rsp & Rgp & Rtp & R8 & R9 & R19 & R18 & R20 & Rhi).
pose proof (proj1 HJ) as HAR. pose proof HJ as (_ & HLY & _ & _ & _ & Hfrs & Hnev & _ & _ & _ & _ & _ & _ & Hpres & _).
assert (HTS : TCLOSE_STK = 17520) by reflexivity.
set (sp0 := spZ regs) in *.
assert (Hing : In (g, CGIF_SIZE) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]. left. reflexivity. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ g CGIF_SIZE HAR Hing) as (Hg16 & Hg4096 & Hgceil & Hgh_ia & HgP & _). pose proof (proj1 Hgh_ia) as Hgh.
pose proof (blk_off_imgP _ _ _ _ _ _ g CGIF_SIZE HAR Hing) as Hgh_img.
change (req_size CGIF_SIZE) with 96 in Hgceil, Hgh, HgP, Hgh_img.
pose proof (frames3 s N HWF) as FR3s. pose proof (frames3 s1 N HWF1) as FR3s1. pose proof (proj1 HWF) as Hlen. pose proof (proj1 HWF1) as Hlen1.
pose proof (slot_eq g s s1 N 2 HOK) as SLOT.
destruct (cl_seed B LAWS TL hw CL_FR (regsFR 2) true Wc regs regs1 memc lyc Sc mdc ly sp0 g s1 HAR Hing Hstk Hpres
ltac:(unfold spZ in Rsp |- *; rewrite Rsp; rewrite unsigned_lit_small by lia; lia)
(regsFR_ok 2 regs regs1 g s1 HR R21 R22 Hgh Hgceil ltac:(lia)) (fun _ => HFR) (fun _ => R20) (proj1 HT1)) as [HS SHOK].
set (E := Eimg (Ereg regs1 (cl_extra regs g s1))) in *. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (Usp : bv_unsigned (ew E 2) = sp0 - 80) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs1 _ 2 2%bv eq_refl); unfold spZ in Rsp |- *; rewrite Rsp; apply unsigned_lit_small; lia).
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros n rr Hn; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
assert (EXo : forall j, (j < 100)%nat -> ew E (32 + j) = nth j (cl_extra regs g s1) (Z_to_bv 64 0)) by (intros j Hj; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (E32 : ew E 32 = Z_to_bv 64 g) by (change 32%nat with (32 + 0)%nat; rewrite EXo by (clear; lia); reflexivity).
assert (E32u : bv_unsigned (ew E 32) = g) by (rewrite E32; apply unsigned_lit_small; lia).
assert (Efp : ew E 35 = Z_to_bv 64 (frame_ptr (nth 2 (cg_frames s1) None))) by (change 35%nat with (32 + 3)%nat; rewrite EXo by (clear; lia); reflexivity).
assert (E37 : ew E 37 = Z_to_bv 64 (cg_cur s1)) by (change 37%nat with (32 + 5)%nat; rewrite EXo by (clear; lia); reflexivity).
assert (E38 : ew E 38 = Z_to_bv 64 SB) by (change 38%nat with (32 + 6)%nat; rewrite EXo by (clear; lia); reflexivity).
pose proof (obj_at_nth SEGS _ _ _ _ 15 (88, 4%N) (cg_cur s1) (proj1 HT1) eq_refl eq_refl) as [_ Rcur]. cbn [snd] in Rcur.
paj_run_to_tok RUNTO HS HJ SHOK RBspanC A_freeFrame.
{ awr_cl Usp E32u Hing HTS. }
pmkst HS.
prreg HS (2%bv : bv 5) Q2; prreg HS (10%bv : bv 5) Q10; prreg HS (3%bv : bv 5) Q3; prreg HS (4%bv : bv 5) Q4; prreg HS (1%bv : bv 5) Q1; prreg HS (8%bv : bv 5) Q8.
prreg HS (18%bv : bv 5) Q18; prreg HS (20%bv : bv 5) Q20; prreg HS (21%bv : bv 5) Q21; prreg HS (22%bv : bv 5) Q22; prreg HS (9%bv : bv 5) Q9; prreg HS (19%bv : bv 5) Q19.
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => g + 88 <= a < g + 92) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp, ?E32u in Hrr; lia|]); destruct Hin)) as UN.
lazymatch type of HS with
| st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
let r := eval vm_compute in (nth 3 (ss_mem ssx) got_regionP) in
pose proof (st_ok_pi_region_nth E ssx (restrict _ msx) 3 r HS ltac:(vm_compute; reflexivity)) as HRg; cbn [ms_mem restrict mkst] in HRg
| st_ok _ _ ?ssx (restrict _ ?msx) =>
let r := eval vm_compute in (nth 3 (ss_mem ssx) got_regionP) in
pose proof (st_ok_region_nth E ssx (restrict _ msx) 3 r HS ltac:(vm_compute; reflexivity)) as HRg; cbn [ms_mem restrict mkst] in HRg end.
pose proof (field_of_region E _ 32 g _ _ _ _ _ 88 4 (SOff 37 0) (cg_cur s1) HRg E32u ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact E37) ltac:(clear - Rcur; cbn; lia) ltac:(cbn; lia)) as Vcur.
change (N.to_nat 4) with 4%nat in Vcur.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
assert (Q3' : getr rg 3 = w64 (as_gp B)) by (rewrite Q3, (EEo 3%nat 3%bv eq_refl); exact Rgp);
assert (Q4' : getr rg 4 = w64 (as_tp B)) by (rewrite Q4, (EEo 4%nat 4%bv eq_refl); exact Rtp);
assert (Qsp : spZ rg = sp0 + -80) by (unfold spZ; rewrite Q2, Usp; lia);
assert (Qs0 : achain lyc (aview SEGS (w_H Wc) mm) (sp0 + -80) (s0Z rg) [])
by (apply achain_low; unfold s0Z; rewrite Q8; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned, E32u; clear - Hgceil; lia);
assert (HEVc : st_nev Sc + 3 <= EV_MAX) by (clear - Hnev Hk Hev Hk0; lia);
assert (HU3 : In (call_trace0 (pc_free_ra0 (as_code B)) rg []) (as_universe B))
by (unfold call_trace0, unwind_of_chain, raZ; rewrite Q1, unsigned_lit_small by lia; cbn; rewrite (proj2 (Z.eqb_neq _ _)) by (pose proof (proj1 (pal_rt_below B TL)); lia); cbn; first [exact HUrfc | exact HUrff])
end.
pose proof HUff1 as HU1.
pose proof HUff2 as HU2.
assert (HBL : Permutation (ablocks B lyc Sc)
(match nth 2 (cg_frames s) None with Some f => frame_blocks N f | None => [] end
++ ((g, CGIF_SIZE) :: pal_blocks s ++ frames_blocks N (skipn (Datatypes.S 2) (cg_frames s)) ++ rest))).
{ eapply Permutation_trans; [exact HPerm1|]. unfold fr_blocks. change (Z.to_nat 2) with 2%nat.
rewrite (frames_blocks_skipn N (cg_frames s) 2) by (rewrite Hlen; lia). cbn [app]. rewrite <- ?app_assoc.
lazymatch goal with |- Permutation _ (?fb ++ _ :: _ ++ ?x) =>
apply (Permutation_app_swap_app ((g, CGIF_SIZE) :: pal_blocks s) fb x) end. }
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
assert (CONT : forall W2 ly2 S2 regs2 mem2 md2 ev FP1,
0 <= ev <= 3 ->
ajournal SEGS B TCLOSE_STK sp0 (FPc g s N) ly S W mem md [] ly2 S2 W2 mem2 md2 (k + ev) ->
ajournal SEGS B FF_STK (sp0 + -80) FP1 lyc Sc Wc mm mdq [] ly2 S2 W2 mem2 md2 ev ->
aregs_preserved rg regs2 ->
(forall i, 0 <= i < 96 -> ~ inFP FP1 (g + i)) ->
(forall j f i, (Datatypes.S 2 <= j)%nat -> nth_error (cg_frames s1) j = Some (Some f) -> 0 <= i < 40 -> ~ inFP FP1 (fr_ptr f + i)) ->
Permutation (ablocks B ly2 S2) ((g, CGIF_SIZE) :: pal_blocks s ++ frames_blocks N (skipn (Datatypes.S 2) (cg_frames s)) ++ rest) ->
SRr SEGS W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + 0x3000)) mem2 (seg_rom SEGS)) md2) (cl_post B ly S W regs mem md g s N rest (k + 3 * (3 - 2) + 2))) end.
{ intros W2 ly2 S2 regs2 mem2 md2 ev FP1 Hev2 HJ2 HJc2 HP2 HnFg HnFf HPerm2.
pose proof (proj1 HJ2) as HAR2.
lazymatch type of HP2 with aregs_preserved ?rg _ =>
assert (CS : forall rr : bv 5, acallee_saved (bv_unsigned rr) -> getr regs2 rr = getr rg rr)
by (intros rr Hr; pose proof (HP2 (bv_unsigned rr) Hr) as Hx; rewrite Z_to_bv_bv_unsigned in Hx; exact Hx) end.
assert (Hing2 : In (g, CGIF_SIZE) (ablocks B ly2 S2)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm2|]; left; reflexivity).
assert (Kg : blk_kept (w_H Wc) (w_H W2) (ms_mem ms) mem2 g 96).
{ eapply (blk_kept_call B); [exact HJc2 | exact Hing | exact Hing2 | change (req_size CGIF_SIZE) with 96; exact HnFg]. }
eapply SRr_mono; [apply (AFT ly S W regs mem md ch g s N rest ly2 S2 W2 regs2 mem2 md2 (k + ev) s1 CX)
| intros Wf cf _ HPf; apply (cl_post_mono B ly S W regs mem md g s N rest _ _ Wf cf HPf); clear - Hev2; lia].
-
split; [exact HJ2|]. split; [clear - Hk0 Hev2; lia|]. split.
{
apply (cl_frame_kept (w_H Wc) (w_H W2) memc mem2); [exact HFR|].
intros a Ha. pose proof HJc2 as (_ & _ & _ & _ & _ & _ & _ & _ & G1 & _).
rewrite (G1 a) by (unfold FF_STK, ASTACK; clear - Ha Hgceil Hceil Hslo HTS C1 H47 Hshi; lia). apply UN; clear - Ha Hgceil Hceil Hslo HTS C1 H47 Hshi; lia. }
split.
{ change (Z.to_nat 2) with 2%nat in HT1. split.
- apply (obj_cgif_rebuild (mrestrict (w_H Wc) memc) _ g (tcgif_vals hw s1) (cg_cur s1) (proj1 HT1)).
+ intros i Hi Hni. rewrite (mbyte_of_aview SEGS _ _ _ _ _ (Kg i Hi)). apply (mbyte_of_aview SEGS). apply UN; clear - Hi Hni Hgh Hgceil C1 C3; lia.
+ reflexivity.
+ intros kk Hkk. rewrite <- (Vcur kk Hkk). apply (mbyte_of_aview SEGS).
replace (g + 88 + Z.of_nat kk) with (g + (88 + Z.of_nat kk)) by lia. apply Kg. clear - Hkk; lia.
- intros j f Hj Hfj. pose proof (proj2 HT1 j f ltac:(clear - Hj; lia) Hfj) as Hof.
destruct (slot_frame g s s1 N j f HOK HWF Hfj) as (f' & Hfj' & Efb).
assert (Hfin : In (fr_ptr f, FRAME_SIZE) (frames_blocks N (skipn (Datatypes.S 2) (cg_frames s)))).
{ apply (frames_blocks_in N (cg_frames s) _ j f' _ Hj Hfj'). rewrite Efb. left. reflexivity. }
assert (Hfc : In (fr_ptr f, FRAME_SIZE) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]. unfold fr_blocks. change (Z.to_nat 2) with 2%nat.
rewrite (frames_blocks_skipn N (cg_frames s) 2) by (rewrite Hlen; lia). cbn [app]. right. apply in_or_app. left. apply in_or_app. right. apply in_or_app. right. exact Hfin. }
assert (Hf2 : In (fr_ptr f, FRAME_SIZE) (ablocks B ly2 S2)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm2|]. cbn [app]. right. apply in_or_app. right. apply in_or_app. left. exact Hfin. }
assert (Dgf' : g + 96 <= fr_ptr f \/ fr_ptr f + 40 <= g).
{ pose proof (sep_hd_in B LAWS lyc Sc Wc memc mdc (g, CGIF_SIZE) (fr_ptr f, FRAME_SIZE) _ HAR HPerm1) as D.
unfold zdisjoint, block_rng in D. cbn [fst snd] in D. change (req_size CGIF_SIZE) with 96 in D. change (req_size FRAME_SIZE) with 40 in D.
apply D. apply in_or_app. left. apply in_or_app. right. unfold fr_blocks in |- *. change (Z.to_nat 2) with 2%nat.
rewrite (frames_blocks_skipn N (cg_frames s) 2) by (rewrite Hlen; lia). apply in_or_app. right. exact Hfin. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ (fr_ptr f) FRAME_SIZE HAR Hfc) as (_ & Hf4096 & Hfceil & _). change (req_size FRAME_SIZE) with 40 in Hfceil.
apply (obj_at_blk_kept (w_H Wc) (w_H W2) memc mem2 (fr_ptr f) LAY_Frame _ 40 Hof lay_inside_Frame).
intros i Hi.
pose proof (blk_kept_call B _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fr_ptr f) FRAME_SIZE HJc2 Hfc Hf2) as Kf.
rewrite (Kf ltac:(intros ii Hii; apply (HnFf j f ii Hj Hfj); change (req_size FRAME_SIZE) with 40 in Hii; exact Hii) i ltac:(change (req_size FRAME_SIZE) with 40; exact Hi)).
apply UN; clear - Hi Dgf' Hgh Hgceil Hf4096 Hfceil C1 C3; lia. }
split; [exact HOK |]. unfold fr_blocks. change (Datatypes.S (Z.to_nat 2)) with (Datatypes.S 2). cbn [app]. rewrite <- ?app_assoc. exact HPerm2.
- clear - Hk Hev2. lia.
-
split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]].
+ rewrite (CS 2%bv ltac:(unfold acallee_saved; rewrite bv_unsigned_BV; lia)). rewrite Q2. rewrite (EEo 2%nat 2%bv eq_refl). exact Rsp.
+ rewrite (CS 3%bv ltac:(unfold acallee_saved; rewrite bv_unsigned_BV; lia)). exact Q3'.
+ rewrite (CS 4%bv ltac:(unfold acallee_saved; rewrite bv_unsigned_BV; lia)). exact Q4'.
+ rewrite (CS 8%bv ltac:(unfold acallee_saved; rewrite bv_unsigned_BV; lia)). rewrite Q8. exact E32.
+ rewrite (CS 9%bv ltac:(unfold acallee_saved; rewrite bv_unsigned_BV; lia)). rewrite Q9. cbn [sv_denot]. rewrite E32u. reflexivity.
+ rewrite (CS 19%bv ltac:(unfold acallee_saved; rewrite bv_unsigned_BV; lia)). rewrite Q19. exact (denot_shx E 32 38 88 g SB E32 E38 ltac:(lia) ltac:(lia) ltac:(clear - Hgceil C1; lia) ltac:(unfold SB; lia)).
+ rewrite (CS 18%bv ltac:(unfold acallee_saved; rewrite bv_unsigned_BV; lia)). rewrite Q18. exact E38.
+ rewrite (CS 20%bv ltac:(unfold acallee_saved; rewrite bv_unsigned_BV; lia)). rewrite Q20, (EEo 20%nat 20%bv eq_refl). exact R20.
+ intros r Hr. rewrite (HP2 r ltac:(unfold acallee_saved; lia)).
assert (Hr4 : r = 25 \/ r = 26 \/ r = 27) by lia.
destruct Hr4 as [-> | [-> | ->]];
((first [rewrite (st_ok_pi_restrict_reg (w_H Wc) E _ _ _ HS) | rewrite (st_ok_restrict_reg SEGS (w_H Wc) E _ _ _ HS)]); cbn [ms_regs];
lazymatch goal with |- sv_denot _ (sr_get ?a ?rr2) = _ => let v := eval vm_compute in (sr_get a rr2) in change (sr_get a rr2) with v end;
cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
lazymatch goal with |- ew _ ?n = getr _ (Z_to_bv 5 ?rr) => rewrite (EEo n (Z_to_bv 5 rr) eq_refl); apply Rhi; lia end).
- rewrite (CS 21%bv ltac:(unfold acallee_saved; rewrite bv_unsigned_BV; lia)). rewrite Q21. apply bv_eq. vm_compute. reflexivity.
- rewrite (CS 22%bv ltac:(unfold acallee_saved; rewrite bv_unsigned_BV; lia)). rewrite Q22. apply bv_eq. vm_compute. reflexivity. }
change (Z.to_nat 2) with 2%nat in HT1.
assert (HN0 : 0 <= N) by (clear - HWF; destruct HWF as (_ & HW1 & HH1 & HN & _); nia).
destruct (nth 2 (cg_frames s1) None) as [f|] eqn:Hfi.
-
cbn [frame_ptr] in Efp.
assert (HfI : nth_error (cg_frames s1) 2 = Some (Some f)) by (rewrite (nth_error_nth' (cg_frames s1) None) by (rewrite Hlen1; lia); rewrite Hfi; reflexivity).
destruct (slot_frame g s s1 N 2 f HOK HWF HfI) as (f' & HfI' & SL).
pose proof (nth_error_nth (cg_frames s) 2 None HfI') as Hfi'.
rewrite Hfi' in HBL. cbv beta iota in HBL. rewrite SL in HBL.
pose proof (proj2 HT1 2%nat f (le_n _) HfI) as Hof.
assert (Hfc : In (fr_ptr f, FRAME_SIZE) (ablocks B lyc Sc)) by (eapply Permutation_in; [apply Permutation_sym; exact HBL|]; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ (fr_ptr f) FRAME_SIZE HAR Hfc) as (Hf16 & Hf4096 & Hfceil & _). change (req_size FRAME_SIZE) with 40 in Hfceil.
assert (SEPg : forall p n, In (p, n) (frame_blocks N f) -> p + req_size n <= g \/ g + 96 <= p).
{ intros p n Hpn. pose proof (sep_app B LAWS lyc Sc Wc memc mdc (p, n) (g, CGIF_SIZE) _ _ HAR HBL Hpn ltac:(left; reflexivity)) as D.
unfold zdisjoint, block_rng in D. cbn [fst snd] in D. change (req_size CGIF_SIZE) with 96 in D. clear - D. lia. }
assert (Dgf : g + 96 <= fr_ptr f \/ fr_ptr f + 40 <= g).
{ pose proof (SEPg (fr_ptr f) FRAME_SIZE ltac:(left; reflexivity)) as D. change (req_size FRAME_SIZE) with 40 in D. clear - D. lia. }
lazymatch goal with |- SRr _ _ (mkCfg (mkst _ _ ?mm _) _) _ =>
assert (Hof' : obj_at SEGS (mrestrict (w_H Wc) mm) (fr_ptr f) LAY_Frame (frame_vals f))
by (apply (obj_at_kept _ _ (fr_ptr f) LAY_Frame (frame_vals f) 40 Hof lay_inside_Frame);
intros i Hi; apply (mbyte_of_aview SEGS); apply UN; clear - Hi Dgf Hgh Hgceil Hf4096 Hfceil C1 C3; lia) end.
pose proof (obj_at_nth SEGS _ _ _ _ 0 (0, 8%N) (fr_lpal f) Hof' eq_refl eq_refl) as [Vlp Rlp].
pose proof (obj_at_nth SEGS _ _ _ _ 1 (8, 8%N) (fr_img f) Hof' eq_refl eq_refl) as [Vim Rim].
pose proof (obj_at_nth SEGS _ _ _ _ 2 (16, 4%N) (fr_attr f) Hof' eq_refl eq_refl) as [Vat Rat].
pose proof (obj_at_nth SEGS _ _ _ _ 5 (26, 2%N) (fr_nlp f) Hof' eq_refl eq_refl) as [_ Rnlp].
cbn [fst snd] in Vlp, Rlp, Vim, Rim, Vat, Rat, Rnlp. rewrite Z.add_0_r in Vlp.
change (N.to_nat 8) with 8%nat in Vlp, Vim. change (N.to_nat 4) with 4%nat in Vat.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
eapply SRr_bind;
[ eapply (cl_call B LAWS Wc rg mm _ TCLOSE_STK sp0 (FPc g s N) ly S W mem md [] lyc Sc mdq k FF_STK
(ablocks_fp (ff_blocks (fr_ptr f) (fr_img f) (fr_lpal f) (fr_attr f) N (fr_nlp f))) 3 (-80) (Z_to_bv 64 (BASE + 0x3000)) []
(fun ly3 S3 W3 regs3 mem3 md3 => Permutation (ablocks B ly3 S3) ((g, CGIF_SIZE) :: pal_blocks s ++ frames_blocks N (skipn (Datatypes.S 2) (cg_frames s)) ++ rest)) HJ Qsp);
[ reflexivity | lia | unfold FF_STK, ASTACK; lia | rewrite HTS; unfold FF_STK, ASTACK; lia
| exact Q3' | exact Q4' | exact Q1 | apply ret_ok_codeptr_v; [cbv; split; [congruence | reflexivity] | reflexivity] | rewrite unsigned_lit_small by lia; lia
| exact Qs0
| intros HPRE1; eapply SRr_mono;
[ eapply (pb_freeFrame B LAWS TL ML AFREE Wc lyc Sc rg mm _ [] (fr_ptr f) (fr_lpal f) (fr_img f) (fr_attr f) N (fr_nlp f) _ HPRE1 HEVc);
[ rewrite Q10; cbn [sv_denot]; rewrite Efp; reflexivity
| exact Vlp | exact Vim | exact Vat | clear - Rlp; lia | clear - Rat; lia | exact HN0 | clear - Rnlp; lia
| exact HBL | exact HU1 | exact HU2 | exact HU3 ]
| cbv beta; unfold ff_post; intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ1 & HP & HK);
exists ly3, S3, regs3, mem3, md3; split; [rewrite Q1; reflexivity | split; [exact HJ1 | split; [exact HP | exact HK]]] ]
| intros a Ha; left; destruct (inFP_ablocks_fp_inv _ a Ha) as (p & n & Hpn & Hpa);
change (ff_blocks (fr_ptr f) (fr_img f) (fr_lpal f) (fr_attr f) N (fr_nlp f)) with (frame_blocks N f) in Hpn; split;
[ unfold FPc; replace a with (p + (a - p)) by lia; apply (inFP_ablocks_fp _ p n (a - p)); [| clear - Hpa; lia];
unfold cgif_blocks; right; right; apply in_or_app; right; rewrite <- SL in Hpn;
exact (frames_blocks_in N (cg_frames s) 0 2 f' (p, n) (Nat.le_0_l _) HfI' Hpn)
| exists p, n; split; [eapply Permutation_in; [apply Permutation_sym; exact HBL|]; apply in_or_app; left; exact Hpn | exact Hpa] ] ]
| ] end.
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc2 & HP2 & HPerm2).
apply (CONT W2 ly2 S2 regs2 mem2 md2 3 _ ltac:(lia) HJ2 HJc2 HP2).
+ intros i Hi HFP. destruct (inFP_ablocks_fp_inv _ _ HFP) as (p & n & Hpn & Hpa).
change (ff_blocks (fr_ptr f) (fr_img f) (fr_lpal f) (fr_attr f) N (fr_nlp f)) with (frame_blocks N f) in Hpn.
pose proof (SEPg p n Hpn) as D. clear - D Hi Hpa. lia.
+ intros j f2 i Hj Hf2 Hi HFP. destruct (inFP_ablocks_fp_inv _ _ HFP) as (p & n & Hpn & Hpa).
change (ff_blocks (fr_ptr f) (fr_img f) (fr_lpal f) (fr_attr f) N (fr_nlp f)) with (frame_blocks N f) in Hpn.
destruct (slot_frame g s s1 N j f2 HOK HWF Hf2) as (f2' & Hf2' & Efb).
assert (Hin2 : In (fr_ptr f2, FRAME_SIZE) (frames_blocks N (skipn (Datatypes.S 2) (cg_frames s)))).
{ apply (frames_blocks_in N (cg_frames s) _ j f2' _ Hj Hf2'). rewrite Efb. left. reflexivity. }
pose proof (sep_app B LAWS lyc Sc Wc memc mdc (p, n) (fr_ptr f2, FRAME_SIZE) _ _ HAR HBL Hpn
ltac:(right; apply in_or_app; right; apply in_or_app; left; exact Hin2)) as D.
unfold zdisjoint, block_rng in D. cbn [fst snd] in D. change (req_size FRAME_SIZE) with 40 in D. clear - D Hi Hpa. lia.
+ exact HPerm2.
-
cbn [frame_ptr] in Efp.
destruct (nth 2 (cg_frames s) None) as [f'|] eqn:Hfi'; [discriminate SLOT|]. cbn [app] in HBL.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
eapply SRr_bind;
[ eapply (cl_call B LAWS Wc rg mm _ TCLOSE_STK sp0 (FPc g s N) ly S W mem md [] lyc Sc mdq k FF_STK [] 0 (-80)
(Z_to_bv 64 (BASE + 0x3000)) [] (fun ly2 S2 W2 regs2 mem2 md2 => ly2 = lyc /\ S2 = Sc) HJ Qsp);
[ reflexivity | lia | unfold FF_STK, ASTACK; lia | rewrite HTS; unfold FF_STK, ASTACK; lia
| exact Q3' | exact Q4' | exact Q1 | apply ret_ok_codeptr_v; [cbv; split; [congruence | reflexivity] | reflexivity] | rewrite unsigned_lit_small by lia; lia
| exact Qs0
| intros HPRE1; eapply SRr_mono;
[ apply (pb_freeFrame_null B LAWS Wc lyc Sc rg mm _ [] HPRE1); rewrite Q10, Efp; reflexivity
| cbv beta; intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ1 & HP & HK);
exists ly2, S2, regs2, mem2, md2; split; [rewrite Q1; reflexivity | split; [exact HJ1 | split; [exact HP | exact HK]]] ]
| intros a Ha; exfalso; exact (inFP_nil a Ha) ]
| ] end.
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc2 & HP2 & -> & ->).
apply (CONT W2 lyc Sc regs2 mem2 md2 0 [] ltac:(lia) HJ2 HJc2 HP2).
+ intros i Hi HFP. exact (inFP_nil _ HFP).
+ intros j f2 i Hj Hf2 Hi HFP. exact (inFP_nil _ HFP).
+ exact HBL.
Qed.
Lemma cl_AFT1_ok : CL_FR_stmt B hw CTX 2 -> CL_AFTER_stmt B hw CTX 1.
Proof.
intros FRN ly S W regs mem md ch g s N rest lyc Sc Wc regs1 memc mdc k s1 CX MID Hk HR R21 R22.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof CX as (HPRE & Hctx & Hfr7 & HROD & H10 & HT & HWF & HPerm & Hev & Hlive).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof MID as (HJ & Hk0 & HFR & HT1 & HOK & HPerm1).
pose proof HOK as (HWF1 & Hraw1 & Hattr1 & Hpal1 & Hngp1 & Hfrm1).
pose proof HR as (Rsp & Rgp & Rtp & R8 & R9 & R19 & R18 & R20 & Rhi).
pose proof (proj1 HJ) as HAR. pose proof HJ as (_ & HLY & _ & _ & _ & Hfrs & Hnev & _ & _ & _ & _ & _ & _ & Hpres & _).
assert (HTS : TCLOSE_STK = 17520) by reflexivity.
set (sp0 := spZ regs) in *.
assert (Hing : In (g, CGIF_SIZE) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]. left. reflexivity. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ g CGIF_SIZE HAR Hing) as (Hg16 & Hg4096 & Hgceil & Hgh_ia & HgP & _). pose proof (proj1 Hgh_ia) as Hgh.
pose proof (blk_off_imgP _ _ _ _ _ _ g CGIF_SIZE HAR Hing) as Hgh_img.
change (req_size CGIF_SIZE) with 96 in Hgceil, Hgh, HgP, Hgh_img.
pose proof (proj1 HWF) as Hlen. pose proof (proj1 HWF1) as Hlen1.
destruct (cl_seed B LAWS TL hw CL_RET_FREEFRAME (regsFR 1) true Wc regs regs1 memc lyc Sc mdc ly sp0 g s1 HAR Hing Hstk Hpres
ltac:(unfold spZ in Rsp |- *; rewrite Rsp; rewrite unsigned_lit_small by lia; lia)
(regsFR_ok 1 regs regs1 g s1 HR R21 R22 Hgh Hgceil ltac:(lia)) (fun _ => HFR) (fun _ => R20) (proj1 HT1)) as [HS SHOK].
set (E := Eimg (Ereg regs1 (cl_extra regs g s1))) in *. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (Usp : bv_unsigned (ew E 2) = sp0 - 80) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs1 _ 2 2%bv eq_refl); unfold spZ in Rsp |- *; rewrite Rsp; apply unsigned_lit_small; lia).
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros n rr Hn; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
assert (EXo : forall j, (j < 100)%nat -> ew E (32 + j) = nth j (cl_extra regs g s1) (Z_to_bv 64 0)) by (intros j Hj; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (E32 : ew E 32 = Z_to_bv 64 g) by (change 32%nat with (32 + 0)%nat; rewrite EXo by (clear; lia); reflexivity).
assert (E32u : bv_unsigned (ew E 32) = g) by (rewrite E32; apply unsigned_lit_small; lia).
assert (E37 : ew E 37 = Z_to_bv 64 (cg_cur s1)) by (change 37%nat with (32 + 5)%nat; rewrite EXo by (clear; lia); reflexivity).
assert (E38 : ew E 38 = Z_to_bv 64 SB) by (change 38%nat with (32 + 6)%nat; rewrite EXo by (clear; lia); reflexivity).
pose proof (obj_at_nth SEGS _ _ _ _ 15 (88, 4%N) (cg_cur s1) (proj1 HT1) eq_refl eq_refl) as [_ Rcur]. cbn [snd] in Rcur.
paj_run_to_tok RUNTO HS HJ SHOK RBspanC CL_FR.
{ awr_cl Usp E32u Hing HTS. }
pmkst HS.
prreg HS (2%bv : bv 5) Q2; prreg HS (3%bv : bv 5) Q3; prreg HS (4%bv : bv 5) Q4; prreg HS (8%bv : bv 5) Q8; prreg HS (9%bv : bv 5) Q9; prreg HS (19%bv : bv 5) Q19.
prreg HS (18%bv : bv 5) Q18; prreg HS (20%bv : bv 5) Q20; prreg HS (21%bv : bv 5) Q21; prreg HS (22%bv : bv 5) Q22.
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => g + 88 <= a < g + 92) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp, ?E32u in Hrr; lia|]); destruct Hin)) as UN.
lazymatch type of HS with
| st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
let r := eval vm_compute in (nth 3 (ss_mem ssx) got_regionP) in
pose proof (st_ok_pi_region_nth E ssx (restrict _ msx) 3 r HS ltac:(vm_compute; reflexivity)) as HRg; cbn [ms_mem restrict mkst] in HRg
| st_ok _ _ ?ssx (restrict _ ?msx) =>
let r := eval vm_compute in (nth 3 (ss_mem ssx) got_regionP) in
pose proof (st_ok_region_nth E ssx (restrict _ msx) 3 r HS ltac:(vm_compute; reflexivity)) as HRg; cbn [ms_mem restrict mkst] in HRg end.
pose proof (field_of_region E _ 32 g _ _ _ _ _ 88 4 (SOff 37 0) (cg_cur s1) HRg E32u ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact E37) ltac:(clear - Rcur; cbn; lia) ltac:(cbn; lia)) as Vcur.
change (N.to_nat 4) with 4%nat in Vcur.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
eapply SRr_mono; [apply (FRN ly S W regs mem md ch g s N rest lyc Sc Wc rg mm mdq k s1 CX)
| intros Wf cf _ HPf; apply (cl_post_mono B ly S W regs mem md g s N rest _ _ Wf cf HPf); clear; lia] end.
-
split; [exact HJ|]. split; [exact Hk0|]. split.
{ apply (cl_frame_kept (w_H Wc) (w_H Wc) memc); [exact HFR|].
intros a Ha. apply UN; clear - Ha Hgceil Hceil Hslo HTS C1 H47 Hshi; lia. }
split.
{ change (Datatypes.S (Z.to_nat 1)) with (Z.to_nat 2) in HT1. split.
- lazymatch goal with |- obj_at _ (mrestrict _ ?mm) _ _ _ =>
apply (obj_cgif_rebuild (mrestrict (w_H Wc) memc) _ g (tcgif_vals hw s1) (cg_cur s1) (proj1 HT1)) end.
+ intros i Hi Hni. apply (mbyte_of_aview SEGS). apply UN; clear - Hi Hni Hgh Hgceil C1 C3; lia.
+ reflexivity.
+ exact Vcur.
- intros j f Hj Hfj. pose proof (proj2 HT1 j f Hj Hfj) as Hof.
destruct (slot_frame g s s1 N j f HOK HWF Hfj) as (f' & Hfj' & Efb).
assert (Hfin : In (fr_ptr f, FRAME_SIZE) (frames_blocks N (skipn (Z.to_nat 2) (cg_frames s)))).
{ apply (frames_blocks_in N (cg_frames s) _ j f' _ Hj Hfj'). rewrite Efb. left. reflexivity. }
assert (Hfc : In (fr_ptr f, FRAME_SIZE) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]. unfold fr_blocks. change (Datatypes.S (Z.to_nat 1)) with (Z.to_nat 2).
right. apply in_or_app. left. apply in_or_app. right. exact Hfin. }
assert (Dgf' : g + 96 <= fr_ptr f \/ fr_ptr f + 40 <= g).
{ pose proof (sep_hd_in B LAWS lyc Sc Wc memc mdc (g, CGIF_SIZE) (fr_ptr f, FRAME_SIZE) _ HAR HPerm1) as D.
unfold zdisjoint, block_rng in D. cbn [fst snd] in D. change (req_size CGIF_SIZE) with 96 in D. change (req_size FRAME_SIZE) with 40 in D.
apply D. apply in_or_app. left. apply in_or_app. right. exact Hfin. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ (fr_ptr f) FRAME_SIZE HAR Hfc) as (_ & Hf4096 & Hfceil & _). change (req_size FRAME_SIZE) with 40 in Hfceil.
apply (obj_at_kept _ _ (fr_ptr f) LAY_Frame _ 40 Hof lay_inside_Frame).
intros i Hi. apply (mbyte_of_aview SEGS). apply UN; clear - Hi Dgf' Hgh Hgceil Hf4096 Hfceil C1 C3; lia. }
split; [exact HOK |]. change (Datatypes.S (Z.to_nat 1)) with (Z.to_nat 2) in HPerm1. exact HPerm1.
- clear - Hk. lia.
-
split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]].
+ rewrite Q2. rewrite (EEo 2%nat 2%bv eq_refl). exact Rsp.
+ rewrite Q3, (EEo 3%nat 3%bv eq_refl). exact Rgp.
+ rewrite Q4, (EEo 4%nat 4%bv eq_refl). exact Rtp.
+ rewrite Q8. exact E32.
+ rewrite Q9. cbn [sv_denot]. rewrite E32u. reflexivity.
+ rewrite Q19. exact (denot_shx E 32 38 88 g SB E32 E38 ltac:(lia) ltac:(lia) ltac:(clear - Hgceil C1; lia) ltac:(unfold SB; lia)).
+ rewrite Q18. exact E38.
+ rewrite Q20, (EEo 20%nat 20%bv eq_refl). exact R20.
+ intros r Hr.
assert (Hr4 : r = 25 \/ r = 26 \/ r = 27) by lia.
destruct Hr4 as [-> | [-> | ->]];
((first [rewrite (st_ok_pi_restrict_reg (w_H Wc) E _ _ _ HS) | rewrite (st_ok_restrict_reg SEGS (w_H Wc) E _ _ _ HS)]); cbn [ms_regs];
lazymatch goal with |- sv_denot _ (sr_get ?a ?rr2) = _ => let v := eval vm_compute in (sr_get a rr2) in change (sr_get a rr2) with v end;
cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
lazymatch goal with |- ew _ ?n = getr _ (Z_to_bv 5 ?rr) => rewrite (EEo n (Z_to_bv 5 rr) eq_refl); apply Rhi; lia end).
- rewrite Q21. apply bv_eq. vm_compute. reflexivity.
- rewrite Q22. apply bv_eq. vm_compute. reflexivity.
Qed.
Lemma cl_FR1_ok : CL_AFTER_stmt B hw CTX 1 -> CL_FR_stmt B hw CTX 1.
Proof.
intros AFT ly S W regs mem md ch g s N rest lyc Sc Wc regs1 memc mdc k s1 CX MID Hk HR R21 R22.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof CX as (HPRE & Hctx & Hfr7 & HROD & H10 & HT & HWF & HPerm & Hev & Hlive).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof MID as (HJ & Hk0 & HFR & HT1 & HOK & HPerm1).
pose proof HOK as (HWF1 & Hraw1 & Hattr1 & Hpal1 & Hngp1 & Hfrm1).
pose proof HR as (Rsp & Rgp & Rtp & R8 & R9 & R19 & R18 & R20 & Rhi).
pose proof (proj1 HJ) as HAR. pose proof HJ as (_ & HLY & _ & _ & _ & Hfrs & Hnev & _ & _ & _ & _ & _ & _ & Hpres & _).
assert (HTS : TCLOSE_STK = 17520) by reflexivity.
set (sp0 := spZ regs) in *.
assert (Hing : In (g, CGIF_SIZE) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]. left. reflexivity. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ g CGIF_SIZE HAR Hing) as (Hg16 & Hg4096 & Hgceil & Hgh_ia & HgP & _). pose proof (proj1 Hgh_ia) as Hgh.
pose proof (blk_off_imgP _ _ _ _ _ _ g CGIF_SIZE HAR Hing) as Hgh_img.
change (req_size CGIF_SIZE) with 96 in Hgceil, Hgh, HgP, Hgh_img.
pose proof (frames3 s N HWF) as FR3s. pose proof (frames3 s1 N HWF1) as FR3s1. pose proof (proj1 HWF) as Hlen. pose proof (proj1 HWF1) as Hlen1.
pose proof (slot_eq g s s1 N 1 HOK) as SLOT.
destruct (cl_seed B LAWS TL hw CL_FR (regsFR 1) true Wc regs regs1 memc lyc Sc mdc ly sp0 g s1 HAR Hing Hstk Hpres
ltac:(unfold spZ in Rsp |- *; rewrite Rsp; rewrite unsigned_lit_small by lia; lia)
(regsFR_ok 1 regs regs1 g s1 HR R21 R22 Hgh Hgceil ltac:(lia)) (fun _ => HFR) (fun _ => R20) (proj1 HT1)) as [HS SHOK].
set (E := Eimg (Ereg regs1 (cl_extra regs g s1))) in *. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (Usp : bv_unsigned (ew E 2) = sp0 - 80) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs1 _ 2 2%bv eq_refl); unfold spZ in Rsp |- *; rewrite Rsp; apply unsigned_lit_small; lia).
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros n rr Hn; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
assert (EXo : forall j, (j < 100)%nat -> ew E (32 + j) = nth j (cl_extra regs g s1) (Z_to_bv 64 0)) by (intros j Hj; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (E32 : ew E 32 = Z_to_bv 64 g) by (change 32%nat with (32 + 0)%nat; rewrite EXo by (clear; lia); reflexivity).
assert (E32u : bv_unsigned (ew E 32) = g) by (rewrite E32; apply unsigned_lit_small; lia).
assert (Efp : ew E 34 = Z_to_bv 64 (frame_ptr (nth 1 (cg_frames s1) None))) by (change 34%nat with (32 + 2)%nat; rewrite EXo by (clear; lia); reflexivity).
assert (E37 : ew E 37 = Z_to_bv 64 (cg_cur s1)) by (change 37%nat with (32 + 5)%nat; rewrite EXo by (clear; lia); reflexivity).
assert (E38 : ew E 38 = Z_to_bv 64 SB) by (change 38%nat with (32 + 6)%nat; rewrite EXo by (clear; lia); reflexivity).
pose proof (obj_at_nth SEGS _ _ _ _ 15 (88, 4%N) (cg_cur s1) (proj1 HT1) eq_refl eq_refl) as [_ Rcur]. cbn [snd] in Rcur.
paj_run_to_tok RUNTO HS HJ SHOK RBspanC A_freeFrame.
{ awr_cl Usp E32u Hing HTS. }
pmkst HS.
prreg HS (2%bv : bv 5) Q2; prreg HS (10%bv : bv 5) Q10; prreg HS (3%bv : bv 5) Q3; prreg HS (4%bv : bv 5) Q4; prreg HS (1%bv : bv 5) Q1; prreg HS (8%bv : bv 5) Q8.
prreg HS (18%bv : bv 5) Q18; prreg HS (20%bv : bv 5) Q20; prreg HS (21%bv : bv 5) Q21; prreg HS (22%bv : bv 5) Q22; prreg HS (9%bv : bv 5) Q9; prreg HS (19%bv : bv 5) Q19.
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => g + 88 <= a < g + 92) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp, ?E32u in Hrr; lia|]); destruct Hin)) as UN.
lazymatch type of HS with
| st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
let r := eval vm_compute in (nth 3 (ss_mem ssx) got_regionP) in
pose proof (st_ok_pi_region_nth E ssx (restrict _ msx) 3 r HS ltac:(vm_compute; reflexivity)) as HRg; cbn [ms_mem restrict mkst] in HRg
| st_ok _ _ ?ssx (restrict _ ?msx) =>
let r := eval vm_compute in (nth 3 (ss_mem ssx) got_regionP) in
pose proof (st_ok_region_nth E ssx (restrict _ msx) 3 r HS ltac:(vm_compute; reflexivity)) as HRg; cbn [ms_mem restrict mkst] in HRg end.
pose proof (field_of_region E _ 32 g _ _ _ _ _ 88 4 (SOff 37 0) (cg_cur s1) HRg E32u ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact E37) ltac:(clear - Rcur; cbn; lia) ltac:(cbn; lia)) as Vcur.
change (N.to_nat 4) with 4%nat in Vcur.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
assert (Q3' : getr rg 3 = w64 (as_gp B)) by (rewrite Q3, (EEo 3%nat 3%bv eq_refl); exact Rgp);
assert (Q4' : getr rg 4 = w64 (as_tp B)) by (rewrite Q4, (EEo 4%nat 4%bv eq_refl); exact Rtp);
assert (Qsp : spZ rg = sp0 + -80) by (unfold spZ; rewrite Q2, Usp; lia);
assert (Qs0 : achain lyc (aview SEGS (w_H Wc) mm) (sp0 + -80) (s0Z rg) [])
by (apply achain_low; unfold s0Z; rewrite Q8; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned, E32u; clear - Hgceil; lia);
assert (HEVc : st_nev Sc + 3 <= EV_MAX) by (clear - Hnev Hk Hev Hk0; lia);
assert (HU3 : In (call_trace0 (pc_free_ra0 (as_code B)) rg []) (as_universe B))
by (unfold call_trace0, unwind_of_chain, raZ; rewrite Q1, unsigned_lit_small by lia; cbn; rewrite (proj2 (Z.eqb_neq _ _)) by (pose proof (proj1 (pal_rt_below B TL)); lia); cbn; first [exact HUrfc | exact HUrff])
end.
pose proof HUff1 as HU1.
pose proof HUff2 as HU2.
assert (HBL : Permutation (ablocks B lyc Sc)
(match nth 1 (cg_frames s) None with Some f => frame_blocks N f | None => [] end
++ ((g, CGIF_SIZE) :: pal_blocks s ++ frames_blocks N (skipn (Datatypes.S 1) (cg_frames s)) ++ rest))).
{ eapply Permutation_trans; [exact HPerm1|]. unfold fr_blocks. change (Z.to_nat 1) with 1%nat.
rewrite (frames_blocks_skipn N (cg_frames s) 1) by (rewrite Hlen; lia). cbn [app]. rewrite <- ?app_assoc.
lazymatch goal with |- Permutation _ (?fb ++ _ :: _ ++ ?x) =>
apply (Permutation_app_swap_app ((g, CGIF_SIZE) :: pal_blocks s) fb x) end. }
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
assert (CONT : forall W2 ly2 S2 regs2 mem2 md2 ev FP1,
0 <= ev <= 3 ->
ajournal SEGS B TCLOSE_STK sp0 (FPc g s N) ly S W mem md [] ly2 S2 W2 mem2 md2 (k + ev) ->
ajournal SEGS B FF_STK (sp0 + -80) FP1 lyc Sc Wc mm mdq [] ly2 S2 W2 mem2 md2 ev ->
aregs_preserved rg regs2 ->
(forall i, 0 <= i < 96 -> ~ inFP FP1 (g + i)) ->
(forall j f i, (Datatypes.S 1 <= j)%nat -> nth_error (cg_frames s1) j = Some (Some f) -> 0 <= i < 40 -> ~ inFP FP1 (fr_ptr f + i)) ->
Permutation (ablocks B ly2 S2) ((g, CGIF_SIZE) :: pal_blocks s ++ frames_blocks N (skipn (Datatypes.S 1) (cg_frames s)) ++ rest) ->
SRr SEGS W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + 0x3000)) mem2 (seg_rom SEGS)) md2) (cl_post B ly S W regs mem md g s N rest (k + 3 * (3 - 1) + 2))) end.
{ intros W2 ly2 S2 regs2 mem2 md2 ev FP1 Hev2 HJ2 HJc2 HP2 HnFg HnFf HPerm2.
pose proof (proj1 HJ2) as HAR2.
lazymatch type of HP2 with aregs_preserved ?rg _ =>
assert (CS : forall rr : bv 5, acallee_saved (bv_unsigned rr) -> getr regs2 rr = getr rg rr)
by (intros rr Hr; pose proof (HP2 (bv_unsigned rr) Hr) as Hx; rewrite Z_to_bv_bv_unsigned in Hx; exact Hx) end.
assert (Hing2 : In (g, CGIF_SIZE) (ablocks B ly2 S2)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm2|]; left; reflexivity).
assert (Kg : blk_kept (w_H Wc) (w_H W2) (ms_mem ms) mem2 g 96).
{ eapply (blk_kept_call B); [exact HJc2 | exact Hing | exact Hing2 | change (req_size CGIF_SIZE) with 96; exact HnFg]. }
eapply SRr_mono; [apply (AFT ly S W regs mem md ch g s N rest ly2 S2 W2 regs2 mem2 md2 (k + ev) s1 CX)
| intros Wf cf _ HPf; apply (cl_post_mono B ly S W regs mem md g s N rest _ _ Wf cf HPf); clear - Hev2; lia].
-
split; [exact HJ2|]. split; [clear - Hk0 Hev2; lia|]. split.
{
apply (cl_frame_kept (w_H Wc) (w_H W2) memc mem2); [exact HFR|].
intros a Ha. pose proof HJc2 as (_ & _ & _ & _ & _ & _ & _ & _ & G1 & _).
rewrite (G1 a) by (unfold FF_STK, ASTACK; clear - Ha Hgceil Hceil Hslo HTS C1 H47 Hshi; lia). apply UN; clear - Ha Hgceil Hceil Hslo HTS C1 H47 Hshi; lia. }
split.
{ change (Z.to_nat 1) with 1%nat in HT1. split.
- apply (obj_cgif_rebuild (mrestrict (w_H Wc) memc) _ g (tcgif_vals hw s1) (cg_cur s1) (proj1 HT1)).
+ intros i Hi Hni. rewrite (mbyte_of_aview SEGS _ _ _ _ _ (Kg i Hi)). apply (mbyte_of_aview SEGS). apply UN; clear - Hi Hni Hgh Hgceil C1 C3; lia.
+ reflexivity.
+ intros kk Hkk. rewrite <- (Vcur kk Hkk). apply (mbyte_of_aview SEGS).
replace (g + 88 + Z.of_nat kk) with (g + (88 + Z.of_nat kk)) by lia. apply Kg. clear - Hkk; lia.
- intros j f Hj Hfj. pose proof (proj2 HT1 j f ltac:(clear - Hj; lia) Hfj) as Hof.
destruct (slot_frame g s s1 N j f HOK HWF Hfj) as (f' & Hfj' & Efb).
assert (Hfin : In (fr_ptr f, FRAME_SIZE) (frames_blocks N (skipn (Datatypes.S 1) (cg_frames s)))).
{ apply (frames_blocks_in N (cg_frames s) _ j f' _ Hj Hfj'). rewrite Efb. left. reflexivity. }
assert (Hfc : In (fr_ptr f, FRAME_SIZE) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]. unfold fr_blocks. change (Z.to_nat 1) with 1%nat.
rewrite (frames_blocks_skipn N (cg_frames s) 1) by (rewrite Hlen; lia). cbn [app]. right. apply in_or_app. left. apply in_or_app. right. apply in_or_app. right. exact Hfin. }
assert (Hf2 : In (fr_ptr f, FRAME_SIZE) (ablocks B ly2 S2)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm2|]. cbn [app]. right. apply in_or_app. right. apply in_or_app. left. exact Hfin. }
assert (Dgf' : g + 96 <= fr_ptr f \/ fr_ptr f + 40 <= g).
{ pose proof (sep_hd_in B LAWS lyc Sc Wc memc mdc (g, CGIF_SIZE) (fr_ptr f, FRAME_SIZE) _ HAR HPerm1) as D.
unfold zdisjoint, block_rng in D. cbn [fst snd] in D. change (req_size CGIF_SIZE) with 96 in D. change (req_size FRAME_SIZE) with 40 in D.
apply D. apply in_or_app. left. apply in_or_app. right. unfold fr_blocks in |- *. change (Z.to_nat 1) with 1%nat.
rewrite (frames_blocks_skipn N (cg_frames s) 1) by (rewrite Hlen; lia). apply in_or_app. right. exact Hfin. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ (fr_ptr f) FRAME_SIZE HAR Hfc) as (_ & Hf4096 & Hfceil & _). change (req_size FRAME_SIZE) with 40 in Hfceil.
apply (obj_at_blk_kept (w_H Wc) (w_H W2) memc mem2 (fr_ptr f) LAY_Frame _ 40 Hof lay_inside_Frame).
intros i Hi.
pose proof (blk_kept_call B _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fr_ptr f) FRAME_SIZE HJc2 Hfc Hf2) as Kf.
rewrite (Kf ltac:(intros ii Hii; apply (HnFf j f ii Hj Hfj); change (req_size FRAME_SIZE) with 40 in Hii; exact Hii) i ltac:(change (req_size FRAME_SIZE) with 40; exact Hi)).
apply UN; clear - Hi Dgf' Hgh Hgceil Hf4096 Hfceil C1 C3; lia. }
split; [exact HOK |]. unfold fr_blocks. change (Datatypes.S (Z.to_nat 1)) with (Datatypes.S 1). cbn [app]. rewrite <- ?app_assoc. exact HPerm2.
- clear - Hk Hev2. lia.
-
split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]].
+ rewrite (CS 2%bv ltac:(unfold acallee_saved; rewrite bv_unsigned_BV; lia)). rewrite Q2. rewrite (EEo 2%nat 2%bv eq_refl). exact Rsp.
+ rewrite (CS 3%bv ltac:(unfold acallee_saved; rewrite bv_unsigned_BV; lia)). exact Q3'.
+ rewrite (CS 4%bv ltac:(unfold acallee_saved; rewrite bv_unsigned_BV; lia)). exact Q4'.
+ rewrite (CS 8%bv ltac:(unfold acallee_saved; rewrite bv_unsigned_BV; lia)). rewrite Q8. exact E32.
+ rewrite (CS 9%bv ltac:(unfold acallee_saved; rewrite bv_unsigned_BV; lia)). rewrite Q9. cbn [sv_denot]. rewrite E32u. reflexivity.
+ rewrite (CS 19%bv ltac:(unfold acallee_saved; rewrite bv_unsigned_BV; lia)). rewrite Q19. exact (denot_shx E 32 38 88 g SB E32 E38 ltac:(lia) ltac:(lia) ltac:(clear - Hgceil C1; lia) ltac:(unfold SB; lia)).
+ rewrite (CS 18%bv ltac:(unfold acallee_saved; rewrite bv_unsigned_BV; lia)). rewrite Q18. exact E38.
+ rewrite (CS 20%bv ltac:(unfold acallee_saved; rewrite bv_unsigned_BV; lia)). rewrite Q20, (EEo 20%nat 20%bv eq_refl). exact R20.
+ intros r Hr. rewrite (HP2 r ltac:(unfold acallee_saved; lia)).
assert (Hr4 : r = 25 \/ r = 26 \/ r = 27) by lia.
destruct Hr4 as [-> | [-> | ->]];
((first [rewrite (st_ok_pi_restrict_reg (w_H Wc) E _ _ _ HS) | rewrite (st_ok_restrict_reg SEGS (w_H Wc) E _ _ _ HS)]); cbn [ms_regs];
lazymatch goal with |- sv_denot _ (sr_get ?a ?rr2) = _ => let v := eval vm_compute in (sr_get a rr2) in change (sr_get a rr2) with v end;
cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
lazymatch goal with |- ew _ ?n = getr _ (Z_to_bv 5 ?rr) => rewrite (EEo n (Z_to_bv 5 rr) eq_refl); apply Rhi; lia end).
- rewrite (CS 21%bv ltac:(unfold acallee_saved; rewrite bv_unsigned_BV; lia)). rewrite Q21. apply bv_eq. vm_compute. reflexivity.
- rewrite (CS 22%bv ltac:(unfold acallee_saved; rewrite bv_unsigned_BV; lia)). rewrite Q22. apply bv_eq. vm_compute. reflexivity. }
change (Z.to_nat 1) with 1%nat in HT1.
assert (HN0 : 0 <= N) by (clear - HWF; destruct HWF as (_ & HW1 & HH1 & HN & _); nia).
destruct (nth 1 (cg_frames s1) None) as [f|] eqn:Hfi.
-
cbn [frame_ptr] in Efp.
assert (HfI : nth_error (cg_frames s1) 1 = Some (Some f)) by (rewrite (nth_error_nth' (cg_frames s1) None) by (rewrite Hlen1; lia); rewrite Hfi; reflexivity).
destruct (slot_frame g s s1 N 1 f HOK HWF HfI) as (f' & HfI' & SL).
pose proof (nth_error_nth (cg_frames s) 1 None HfI') as Hfi'.
rewrite Hfi' in HBL. cbv beta iota in HBL. rewrite SL in HBL.
pose proof (proj2 HT1 1%nat f (le_n _) HfI) as Hof.
assert (Hfc : In (fr_ptr f, FRAME_SIZE) (ablocks B lyc Sc)) by (eapply Permutation_in; [apply Permutation_sym; exact HBL|]; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ (fr_ptr f) FRAME_SIZE HAR Hfc) as (Hf16 & Hf4096 & Hfceil & _). change (req_size FRAME_SIZE) with 40 in Hfceil.
assert (SEPg : forall p n, In (p, n) (frame_blocks N f) -> p + req_size n <= g \/ g + 96 <= p).
{ intros p n Hpn. pose proof (sep_app B LAWS lyc Sc Wc memc mdc (p, n) (g, CGIF_SIZE) _ _ HAR HBL Hpn ltac:(left; reflexivity)) as D.
unfold zdisjoint, block_rng in D. cbn [fst snd] in D. change (req_size CGIF_SIZE) with 96 in D. clear - D. lia. }
assert (Dgf : g + 96 <= fr_ptr f \/ fr_ptr f + 40 <= g).
{ pose proof (SEPg (fr_ptr f) FRAME_SIZE ltac:(left; reflexivity)) as D. change (req_size FRAME_SIZE) with 40 in D. clear - D. lia. }
lazymatch goal with |- SRr _ _ (mkCfg (mkst _ _ ?mm _) _) _ =>
assert (Hof' : obj_at SEGS (mrestrict (w_H Wc) mm) (fr_ptr f) LAY_Frame (frame_vals f))
by (apply (obj_at_kept _ _ (fr_ptr f) LAY_Frame (frame_vals f) 40 Hof lay_inside_Frame);
intros i Hi; apply (mbyte_of_aview SEGS); apply UN; clear - Hi Dgf Hgh Hgceil Hf4096 Hfceil C1 C3; lia) end.
pose proof (obj_at_nth SEGS _ _ _ _ 0 (0, 8%N) (fr_lpal f) Hof' eq_refl eq_refl) as [Vlp Rlp].
pose proof (obj_at_nth SEGS _ _ _ _ 1 (8, 8%N) (fr_img f) Hof' eq_refl eq_refl) as [Vim Rim].
pose proof (obj_at_nth SEGS _ _ _ _ 2 (16, 4%N) (fr_attr f) Hof' eq_refl eq_refl) as [Vat Rat].
pose proof (obj_at_nth SEGS _ _ _ _ 5 (26, 2%N) (fr_nlp f) Hof' eq_refl eq_refl) as [_ Rnlp].
cbn [fst snd] in Vlp, Rlp, Vim, Rim, Vat, Rat, Rnlp. rewrite Z.add_0_r in Vlp.
change (N.to_nat 8) with 8%nat in Vlp, Vim. change (N.to_nat 4) with 4%nat in Vat.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
eapply SRr_bind;
[ eapply (cl_call B LAWS Wc rg mm _ TCLOSE_STK sp0 (FPc g s N) ly S W mem md [] lyc Sc mdq k FF_STK
(ablocks_fp (ff_blocks (fr_ptr f) (fr_img f) (fr_lpal f) (fr_attr f) N (fr_nlp f))) 3 (-80) (Z_to_bv 64 (BASE + 0x3000)) []
(fun ly3 S3 W3 regs3 mem3 md3 => Permutation (ablocks B ly3 S3) ((g, CGIF_SIZE) :: pal_blocks s ++ frames_blocks N (skipn (Datatypes.S 1) (cg_frames s)) ++ rest)) HJ Qsp);
[ reflexivity | lia | unfold FF_STK, ASTACK; lia | rewrite HTS; unfold FF_STK, ASTACK; lia
| exact Q3' | exact Q4' | exact Q1 | apply ret_ok_codeptr_v; [cbv; split; [congruence | reflexivity] | reflexivity] | rewrite unsigned_lit_small by lia; lia
| exact Qs0
| intros HPRE1; eapply SRr_mono;
[ eapply (pb_freeFrame B LAWS TL ML AFREE Wc lyc Sc rg mm _ [] (fr_ptr f) (fr_lpal f) (fr_img f) (fr_attr f) N (fr_nlp f) _ HPRE1 HEVc);
[ rewrite Q10; cbn [sv_denot]; rewrite Efp; reflexivity
| exact Vlp | exact Vim | exact Vat | clear - Rlp; lia | clear - Rat; lia | exact HN0 | clear - Rnlp; lia
| exact HBL | exact HU1 | exact HU2 | exact HU3 ]
| cbv beta; unfold ff_post; intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ1 & HP & HK);
exists ly3, S3, regs3, mem3, md3; split; [rewrite Q1; reflexivity | split; [exact HJ1 | split; [exact HP | exact HK]]] ]
| intros a Ha; left; destruct (inFP_ablocks_fp_inv _ a Ha) as (p & n & Hpn & Hpa);
change (ff_blocks (fr_ptr f) (fr_img f) (fr_lpal f) (fr_attr f) N (fr_nlp f)) with (frame_blocks N f) in Hpn; split;
[ unfold FPc; replace a with (p + (a - p)) by lia; apply (inFP_ablocks_fp _ p n (a - p)); [| clear - Hpa; lia];
unfold cgif_blocks; right; right; apply in_or_app; right; rewrite <- SL in Hpn;
exact (frames_blocks_in N (cg_frames s) 0 1 f' (p, n) (Nat.le_0_l _) HfI' Hpn)
| exists p, n; split; [eapply Permutation_in; [apply Permutation_sym; exact HBL|]; apply in_or_app; left; exact Hpn | exact Hpa] ] ]
| ] end.
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc2 & HP2 & HPerm2).
apply (CONT W2 ly2 S2 regs2 mem2 md2 3 _ ltac:(lia) HJ2 HJc2 HP2).
+ intros i Hi HFP. destruct (inFP_ablocks_fp_inv _ _ HFP) as (p & n & Hpn & Hpa).
change (ff_blocks (fr_ptr f) (fr_img f) (fr_lpal f) (fr_attr f) N (fr_nlp f)) with (frame_blocks N f) in Hpn.
pose proof (SEPg p n Hpn) as D. clear - D Hi Hpa. lia.
+ intros j f2 i Hj Hf2 Hi HFP. destruct (inFP_ablocks_fp_inv _ _ HFP) as (p & n & Hpn & Hpa).
change (ff_blocks (fr_ptr f) (fr_img f) (fr_lpal f) (fr_attr f) N (fr_nlp f)) with (frame_blocks N f) in Hpn.
destruct (slot_frame g s s1 N j f2 HOK HWF Hf2) as (f2' & Hf2' & Efb).
assert (Hin2 : In (fr_ptr f2, FRAME_SIZE) (frames_blocks N (skipn (Datatypes.S 1) (cg_frames s)))).
{ apply (frames_blocks_in N (cg_frames s) _ j f2' _ Hj Hf2'). rewrite Efb. left. reflexivity. }
pose proof (sep_app B LAWS lyc Sc Wc memc mdc (p, n) (fr_ptr f2, FRAME_SIZE) _ _ HAR HBL Hpn
ltac:(right; apply in_or_app; right; apply in_or_app; left; exact Hin2)) as D.
unfold zdisjoint, block_rng in D. cbn [fst snd] in D. change (req_size FRAME_SIZE) with 40 in D. clear - D Hi Hpa. lia.
+ exact HPerm2.
-
cbn [frame_ptr] in Efp.
destruct (nth 1 (cg_frames s) None) as [f'|] eqn:Hfi'; [discriminate SLOT|]. cbn [app] in HBL.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
eapply SRr_bind;
[ eapply (cl_call B LAWS Wc rg mm _ TCLOSE_STK sp0 (FPc g s N) ly S W mem md [] lyc Sc mdq k FF_STK [] 0 (-80)
(Z_to_bv 64 (BASE + 0x3000)) [] (fun ly2 S2 W2 regs2 mem2 md2 => ly2 = lyc /\ S2 = Sc) HJ Qsp);
[ reflexivity | lia | unfold FF_STK, ASTACK; lia | rewrite HTS; unfold FF_STK, ASTACK; lia
| exact Q3' | exact Q4' | exact Q1 | apply ret_ok_codeptr_v; [cbv; split; [congruence | reflexivity] | reflexivity] | rewrite unsigned_lit_small by lia; lia
| exact Qs0
| intros HPRE1; eapply SRr_mono;
[ apply (pb_freeFrame_null B LAWS Wc lyc Sc rg mm _ [] HPRE1); rewrite Q10, Efp; reflexivity
| cbv beta; intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ1 & HP & HK);
exists ly2, S2, regs2, mem2, md2; split; [rewrite Q1; reflexivity | split; [exact HJ1 | split; [exact HP | exact HK]]] ]
| intros a Ha; exfalso; exact (inFP_nil a Ha) ]
| ] end.
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc2 & HP2 & -> & ->).
apply (CONT W2 lyc Sc regs2 mem2 md2 0 [] ltac:(lia) HJ2 HJc2 HP2).
+ intros i Hi HFP. exact (inFP_nil _ HFP).
+ intros j f2 i Hj Hf2 Hi HFP. exact (inFP_nil _ HFP).
+ exact HBL.
Qed.
Lemma cl_AFT0_ok : CL_FR_stmt B hw CTX 1 -> CL_AFTER_stmt B hw CTX 0.
Proof.
intros FRN ly S W regs mem md ch g s N rest lyc Sc Wc regs1 memc mdc k s1 CX MID Hk HR R21 R22.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof CX as (HPRE & Hctx & Hfr7 & HROD & H10 & HT & HWF & HPerm & Hev & Hlive).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof MID as (HJ & Hk0 & HFR & HT1 & HOK & HPerm1).
pose proof HOK as (HWF1 & Hraw1 & Hattr1 & Hpal1 & Hngp1 & Hfrm1).
pose proof HR as (Rsp & Rgp & Rtp & R8 & R9 & R19 & R18 & R20 & Rhi).
pose proof (proj1 HJ) as HAR. pose proof HJ as (_ & HLY & _ & _ & _ & Hfrs & Hnev & _ & _ & _ & _ & _ & _ & Hpres & _).
assert (HTS : TCLOSE_STK = 17520) by reflexivity.
set (sp0 := spZ regs) in *.
assert (Hing : In (g, CGIF_SIZE) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]. left. reflexivity. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ g CGIF_SIZE HAR Hing) as (Hg16 & Hg4096 & Hgceil & Hgh_ia & HgP & _). pose proof (proj1 Hgh_ia) as Hgh.
pose proof (blk_off_imgP _ _ _ _ _ _ g CGIF_SIZE HAR Hing) as Hgh_img.
change (req_size CGIF_SIZE) with 96 in Hgceil, Hgh, HgP, Hgh_img.
pose proof (proj1 HWF) as Hlen. pose proof (proj1 HWF1) as Hlen1.
destruct (cl_seed B LAWS TL hw CL_RET_FREEFRAME (regsFR 0) true Wc regs regs1 memc lyc Sc mdc ly sp0 g s1 HAR Hing Hstk Hpres
ltac:(unfold spZ in Rsp |- *; rewrite Rsp; rewrite unsigned_lit_small by lia; lia)
(regsFR_ok 0 regs regs1 g s1 HR R21 R22 Hgh Hgceil ltac:(lia)) (fun _ => HFR) (fun _ => R20) (proj1 HT1)) as [HS SHOK].
set (E := Eimg (Ereg regs1 (cl_extra regs g s1))) in *. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (Usp : bv_unsigned (ew E 2) = sp0 - 80) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs1 _ 2 2%bv eq_refl); unfold spZ in Rsp |- *; rewrite Rsp; apply unsigned_lit_small; lia).
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros n rr Hn; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
assert (EXo : forall j, (j < 100)%nat -> ew E (32 + j) = nth j (cl_extra regs g s1) (Z_to_bv 64 0)) by (intros j Hj; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (E32 : ew E 32 = Z_to_bv 64 g) by (change 32%nat with (32 + 0)%nat; rewrite EXo by (clear; lia); reflexivity).
assert (E32u : bv_unsigned (ew E 32) = g) by (rewrite E32; apply unsigned_lit_small; lia).
assert (E37 : ew E 37 = Z_to_bv 64 (cg_cur s1)) by (change 37%nat with (32 + 5)%nat; rewrite EXo by (clear; lia); reflexivity).
assert (E38 : ew E 38 = Z_to_bv 64 SB) by (change 38%nat with (32 + 6)%nat; rewrite EXo by (clear; lia); reflexivity).
pose proof (obj_at_nth SEGS _ _ _ _ 15 (88, 4%N) (cg_cur s1) (proj1 HT1) eq_refl eq_refl) as [_ Rcur]. cbn [snd] in Rcur.
paj_run_to_tok RUNTO HS HJ SHOK RBspanC CL_FR.
{ awr_cl Usp E32u Hing HTS. }
pmkst HS.
prreg HS (2%bv : bv 5) Q2; prreg HS (3%bv : bv 5) Q3; prreg HS (4%bv : bv 5) Q4; prreg HS (8%bv : bv 5) Q8; prreg HS (9%bv : bv 5) Q9; prreg HS (19%bv : bv 5) Q19.
prreg HS (18%bv : bv 5) Q18; prreg HS (20%bv : bv 5) Q20; prreg HS (21%bv : bv 5) Q21; prreg HS (22%bv : bv 5) Q22.
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => g + 88 <= a < g + 92) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp, ?E32u in Hrr; lia|]); destruct Hin)) as UN.
lazymatch type of HS with
| st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
let r := eval vm_compute in (nth 3 (ss_mem ssx) got_regionP) in
pose proof (st_ok_pi_region_nth E ssx (restrict _ msx) 3 r HS ltac:(vm_compute; reflexivity)) as HRg; cbn [ms_mem restrict mkst] in HRg
| st_ok _ _ ?ssx (restrict _ ?msx) =>
let r := eval vm_compute in (nth 3 (ss_mem ssx) got_regionP) in
pose proof (st_ok_region_nth E ssx (restrict _ msx) 3 r HS ltac:(vm_compute; reflexivity)) as HRg; cbn [ms_mem restrict mkst] in HRg end.
pose proof (field_of_region E _ 32 g _ _ _ _ _ 88 4 (SOff 37 0) (cg_cur s1) HRg E32u ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact E37) ltac:(clear - Rcur; cbn; lia) ltac:(cbn; lia)) as Vcur.
change (N.to_nat 4) with 4%nat in Vcur.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
eapply SRr_mono; [apply (FRN ly S W regs mem md ch g s N rest lyc Sc Wc rg mm mdq k s1 CX)
| intros Wf cf _ HPf; apply (cl_post_mono B ly S W regs mem md g s N rest _ _ Wf cf HPf); clear; lia] end.
-
split; [exact HJ|]. split; [exact Hk0|]. split.
{ apply (cl_frame_kept (w_H Wc) (w_H Wc) memc); [exact HFR|].
intros a Ha. apply UN; clear - Ha Hgceil Hceil Hslo HTS C1 H47 Hshi; lia. }
split.
{ change (Datatypes.S (Z.to_nat 0)) with (Z.to_nat 1) in HT1. split.
- lazymatch goal with |- obj_at _ (mrestrict _ ?mm) _ _ _ =>
apply (obj_cgif_rebuild (mrestrict (w_H Wc) memc) _ g (tcgif_vals hw s1) (cg_cur s1) (proj1 HT1)) end.
+ intros i Hi Hni. apply (mbyte_of_aview SEGS). apply UN; clear - Hi Hni Hgh Hgceil C1 C3; lia.
+ reflexivity.
+ exact Vcur.
- intros j f Hj Hfj. pose proof (proj2 HT1 j f Hj Hfj) as Hof.
destruct (slot_frame g s s1 N j f HOK HWF Hfj) as (f' & Hfj' & Efb).
assert (Hfin : In (fr_ptr f, FRAME_SIZE) (frames_blocks N (skipn (Z.to_nat 1) (cg_frames s)))).
{ apply (frames_blocks_in N (cg_frames s) _ j f' _ Hj Hfj'). rewrite Efb. left. reflexivity. }
assert (Hfc : In (fr_ptr f, FRAME_SIZE) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]. unfold fr_blocks. change (Datatypes.S (Z.to_nat 0)) with (Z.to_nat 1).
right. apply in_or_app. left. apply in_or_app. right. exact Hfin. }
assert (Dgf' : g + 96 <= fr_ptr f \/ fr_ptr f + 40 <= g).
{ pose proof (sep_hd_in B LAWS lyc Sc Wc memc mdc (g, CGIF_SIZE) (fr_ptr f, FRAME_SIZE) _ HAR HPerm1) as D.
unfold zdisjoint, block_rng in D. cbn [fst snd] in D. change (req_size CGIF_SIZE) with 96 in D. change (req_size FRAME_SIZE) with 40 in D.
apply D. apply in_or_app. left. apply in_or_app. right. exact Hfin. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ (fr_ptr f) FRAME_SIZE HAR Hfc) as (_ & Hf4096 & Hfceil & _). change (req_size FRAME_SIZE) with 40 in Hfceil.
apply (obj_at_kept _ _ (fr_ptr f) LAY_Frame _ 40 Hof lay_inside_Frame).
intros i Hi. apply (mbyte_of_aview SEGS). apply UN; clear - Hi Dgf' Hgh Hgceil Hf4096 Hfceil C1 C3; lia. }
split; [exact HOK |]. change (Datatypes.S (Z.to_nat 0)) with (Z.to_nat 1) in HPerm1. exact HPerm1.
- clear - Hk. lia.
-
split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]].
+ rewrite Q2. rewrite (EEo 2%nat 2%bv eq_refl). exact Rsp.
+ rewrite Q3, (EEo 3%nat 3%bv eq_refl). exact Rgp.
+ rewrite Q4, (EEo 4%nat 4%bv eq_refl). exact Rtp.
+ rewrite Q8. exact E32.
+ rewrite Q9. cbn [sv_denot]. rewrite E32u. reflexivity.
+ rewrite Q19. exact (denot_shx E 32 38 88 g SB E32 E38 ltac:(lia) ltac:(lia) ltac:(clear - Hgceil C1; lia) ltac:(unfold SB; lia)).
+ rewrite Q18. exact E38.
+ rewrite Q20, (EEo 20%nat 20%bv eq_refl). exact R20.
+ intros r Hr.
assert (Hr4 : r = 25 \/ r = 26 \/ r = 27) by lia.
destruct Hr4 as [-> | [-> | ->]];
((first [rewrite (st_ok_pi_restrict_reg (w_H Wc) E _ _ _ HS) | rewrite (st_ok_restrict_reg SEGS (w_H Wc) E _ _ _ HS)]); cbn [ms_regs];
lazymatch goal with |- sv_denot _ (sr_get ?a ?rr2) = _ => let v := eval vm_compute in (sr_get a rr2) in change (sr_get a rr2) with v end;
cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
lazymatch goal with |- ew _ ?n = getr _ (Z_to_bv 5 ?rr) => rewrite (EEo n (Z_to_bv 5 rr) eq_refl); apply Rhi; lia end).
- rewrite Q21. apply bv_eq. vm_compute. reflexivity.
- rewrite Q22. apply bv_eq. vm_compute. reflexivity.
Qed.
Lemma cl_FR0_ok : CL_AFTER_stmt B hw CTX 0 -> CL_FR_stmt B hw CTX 0.
Proof.
intros AFT ly S W regs mem md ch g s N rest lyc Sc Wc regs1 memc mdc k s1 CX MID Hk HR R21 R22.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof CX as (HPRE & Hctx & Hfr7 & HROD & H10 & HT & HWF & HPerm & Hev & Hlive).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof MID as (HJ & Hk0 & HFR & HT1 & HOK & HPerm1).
pose proof HOK as (HWF1 & Hraw1 & Hattr1 & Hpal1 & Hngp1 & Hfrm1).
pose proof HR as (Rsp & Rgp & Rtp & R8 & R9 & R19 & R18 & R20 & Rhi).
pose proof (proj1 HJ) as HAR. pose proof HJ as (_ & HLY & _ & _ & _ & Hfrs & Hnev & _ & _ & _ & _ & _ & _ & Hpres & _).
assert (HTS : TCLOSE_STK = 17520) by reflexivity.
set (sp0 := spZ regs) in *.
assert (Hing : In (g, CGIF_SIZE) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]. left. reflexivity. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ g CGIF_SIZE HAR Hing) as (Hg16 & Hg4096 & Hgceil & Hgh_ia & HgP & _). pose proof (proj1 Hgh_ia) as Hgh.
pose proof (blk_off_imgP _ _ _ _ _ _ g CGIF_SIZE HAR Hing) as Hgh_img.
change (req_size CGIF_SIZE) with 96 in Hgceil, Hgh, HgP, Hgh_img.
pose proof (frames3 s N HWF) as FR3s. pose proof (frames3 s1 N HWF1) as FR3s1. pose proof (proj1 HWF) as Hlen. pose proof (proj1 HWF1) as Hlen1.
pose proof (slot_eq g s s1 N 0 HOK) as SLOT.
destruct (cl_seed B LAWS TL hw CL_FR (regsFR 0) true Wc regs regs1 memc lyc Sc mdc ly sp0 g s1 HAR Hing Hstk Hpres
ltac:(unfold spZ in Rsp |- *; rewrite Rsp; rewrite unsigned_lit_small by lia; lia)
(regsFR_ok 0 regs regs1 g s1 HR R21 R22 Hgh Hgceil ltac:(lia)) (fun _ => HFR) (fun _ => R20) (proj1 HT1)) as [HS SHOK].
set (E := Eimg (Ereg regs1 (cl_extra regs g s1))) in *. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (Usp : bv_unsigned (ew E 2) = sp0 - 80) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs1 _ 2 2%bv eq_refl); unfold spZ in Rsp |- *; rewrite Rsp; apply unsigned_lit_small; lia).
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros n rr Hn; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
assert (EXo : forall j, (j < 100)%nat -> ew E (32 + j) = nth j (cl_extra regs g s1) (Z_to_bv 64 0)) by (intros j Hj; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (E32 : ew E 32 = Z_to_bv 64 g) by (change 32%nat with (32 + 0)%nat; rewrite EXo by (clear; lia); reflexivity).
assert (E32u : bv_unsigned (ew E 32) = g) by (rewrite E32; apply unsigned_lit_small; lia).
assert (Efp : ew E 33 = Z_to_bv 64 (frame_ptr (nth 0 (cg_frames s1) None))) by (change 33%nat with (32 + 1)%nat; rewrite EXo by (clear; lia); reflexivity).
assert (E37 : ew E 37 = Z_to_bv 64 (cg_cur s1)) by (change 37%nat with (32 + 5)%nat; rewrite EXo by (clear; lia); reflexivity).
assert (E38 : ew E 38 = Z_to_bv 64 SB) by (change 38%nat with (32 + 6)%nat; rewrite EXo by (clear; lia); reflexivity).
pose proof (obj_at_nth SEGS _ _ _ _ 15 (88, 4%N) (cg_cur s1) (proj1 HT1) eq_refl eq_refl) as [_ Rcur]. cbn [snd] in Rcur.
paj_run_to_tok RUNTO HS HJ SHOK RBspanC A_freeFrame.
{ awr_cl Usp E32u Hing HTS. }
pmkst HS.
prreg HS (2%bv : bv 5) Q2; prreg HS (10%bv : bv 5) Q10; prreg HS (3%bv : bv 5) Q3; prreg HS (4%bv : bv 5) Q4; prreg HS (1%bv : bv 5) Q1; prreg HS (8%bv : bv 5) Q8.
prreg HS (18%bv : bv 5) Q18; prreg HS (20%bv : bv 5) Q20; prreg HS (21%bv : bv 5) Q21; prreg HS (22%bv : bv 5) Q22; prreg HS (9%bv : bv 5) Q9; prreg HS (19%bv : bv 5) Q19.
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => g + 88 <= a < g + 92) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp, ?E32u in Hrr; lia|]); destruct Hin)) as UN.
lazymatch type of HS with
| st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
let r := eval vm_compute in (nth 3 (ss_mem ssx) got_regionP) in
pose proof (st_ok_pi_region_nth E ssx (restrict _ msx) 3 r HS ltac:(vm_compute; reflexivity)) as HRg; cbn [ms_mem restrict mkst] in HRg
| st_ok _ _ ?ssx (restrict _ ?msx) =>
let r := eval vm_compute in (nth 3 (ss_mem ssx) got_regionP) in
pose proof (st_ok_region_nth E ssx (restrict _ msx) 3 r HS ltac:(vm_compute; reflexivity)) as HRg; cbn [ms_mem restrict mkst] in HRg end.
pose proof (field_of_region E _ 32 g _ _ _ _ _ 88 4 (SOff 37 0) (cg_cur s1) HRg E32u ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact E37) ltac:(clear - Rcur; cbn; lia) ltac:(cbn; lia)) as Vcur.
change (N.to_nat 4) with 4%nat in Vcur.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
assert (Q3' : getr rg 3 = w64 (as_gp B)) by (rewrite Q3, (EEo 3%nat 3%bv eq_refl); exact Rgp);
assert (Q4' : getr rg 4 = w64 (as_tp B)) by (rewrite Q4, (EEo 4%nat 4%bv eq_refl); exact Rtp);
assert (Qsp : spZ rg = sp0 + -80) by (unfold spZ; rewrite Q2, Usp; lia);
assert (Qs0 : achain lyc (aview SEGS (w_H Wc) mm) (sp0 + -80) (s0Z rg) [])
by (apply achain_low; unfold s0Z; rewrite Q8; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned, E32u; clear - Hgceil; lia);
assert (HEVc : st_nev Sc + 3 <= EV_MAX) by (clear - Hnev Hk Hev Hk0; lia);
assert (HU3 : In (call_trace0 (pc_free_ra0 (as_code B)) rg []) (as_universe B))
by (unfold call_trace0, unwind_of_chain, raZ; rewrite Q1, unsigned_lit_small by lia; cbn; rewrite (proj2 (Z.eqb_neq _ _)) by (pose proof (proj1 (pal_rt_below B TL)); lia); cbn; first [exact HUrfc | exact HUrff])
end.
pose proof HUff1 as HU1.
pose proof HUff2 as HU2.
assert (HBL : Permutation (ablocks B lyc Sc)
(match nth 0 (cg_frames s) None with Some f => frame_blocks N f | None => [] end
++ ((g, CGIF_SIZE) :: pal_blocks s ++ frames_blocks N (skipn (Datatypes.S 0) (cg_frames s)) ++ rest))).
{ eapply Permutation_trans; [exact HPerm1|]. unfold fr_blocks. change (Z.to_nat 0) with 0%nat.
rewrite (frames_blocks_skipn N (cg_frames s) 0) by (rewrite Hlen; lia). cbn [app]. rewrite <- ?app_assoc.
lazymatch goal with |- Permutation _ (?fb ++ _ :: _ ++ ?x) =>
apply (Permutation_app_swap_app ((g, CGIF_SIZE) :: pal_blocks s) fb x) end. }
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
assert (CONT : forall W2 ly2 S2 regs2 mem2 md2 ev FP1,
0 <= ev <= 3 ->
ajournal SEGS B TCLOSE_STK sp0 (FPc g s N) ly S W mem md [] ly2 S2 W2 mem2 md2 (k + ev) ->
ajournal SEGS B FF_STK (sp0 + -80) FP1 lyc Sc Wc mm mdq [] ly2 S2 W2 mem2 md2 ev ->
aregs_preserved rg regs2 ->
(forall i, 0 <= i < 96 -> ~ inFP FP1 (g + i)) ->
(forall j f i, (Datatypes.S 0 <= j)%nat -> nth_error (cg_frames s1) j = Some (Some f) -> 0 <= i < 40 -> ~ inFP FP1 (fr_ptr f + i)) ->
Permutation (ablocks B ly2 S2) ((g, CGIF_SIZE) :: pal_blocks s ++ frames_blocks N (skipn (Datatypes.S 0) (cg_frames s)) ++ rest) ->
SRr SEGS W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + 0x3000)) mem2 (seg_rom SEGS)) md2) (cl_post B ly S W regs mem md g s N rest (k + 3 * (3 - 0) + 2))) end.
{ intros W2 ly2 S2 regs2 mem2 md2 ev FP1 Hev2 HJ2 HJc2 HP2 HnFg HnFf HPerm2.
pose proof (proj1 HJ2) as HAR2.
lazymatch type of HP2 with aregs_preserved ?rg _ =>
assert (CS : forall rr : bv 5, acallee_saved (bv_unsigned rr) -> getr regs2 rr = getr rg rr)
by (intros rr Hr; pose proof (HP2 (bv_unsigned rr) Hr) as Hx; rewrite Z_to_bv_bv_unsigned in Hx; exact Hx) end.
assert (Hing2 : In (g, CGIF_SIZE) (ablocks B ly2 S2)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm2|]; left; reflexivity).
assert (Kg : blk_kept (w_H Wc) (w_H W2) (ms_mem ms) mem2 g 96).
{ eapply (blk_kept_call B); [exact HJc2 | exact Hing | exact Hing2 | change (req_size CGIF_SIZE) with 96; exact HnFg]. }
eapply SRr_mono; [apply (AFT ly S W regs mem md ch g s N rest ly2 S2 W2 regs2 mem2 md2 (k + ev) s1 CX)
| intros Wf cf _ HPf; apply (cl_post_mono B ly S W regs mem md g s N rest _ _ Wf cf HPf); clear - Hev2; lia].
-
split; [exact HJ2|]. split; [clear - Hk0 Hev2; lia|]. split.
{
apply (cl_frame_kept (w_H Wc) (w_H W2) memc mem2); [exact HFR|].
intros a Ha. pose proof HJc2 as (_ & _ & _ & _ & _ & _ & _ & _ & G1 & _).
rewrite (G1 a) by (unfold FF_STK, ASTACK; clear - Ha Hgceil Hceil Hslo HTS C1 H47 Hshi; lia). apply UN; clear - Ha Hgceil Hceil Hslo HTS C1 H47 Hshi; lia. }
split.
{ change (Z.to_nat 0) with 0%nat in HT1. split.
- apply (obj_cgif_rebuild (mrestrict (w_H Wc) memc) _ g (tcgif_vals hw s1) (cg_cur s1) (proj1 HT1)).
+ intros i Hi Hni. rewrite (mbyte_of_aview SEGS _ _ _ _ _ (Kg i Hi)). apply (mbyte_of_aview SEGS). apply UN; clear - Hi Hni Hgh Hgceil C1 C3; lia.
+ reflexivity.
+ intros kk Hkk. rewrite <- (Vcur kk Hkk). apply (mbyte_of_aview SEGS).
replace (g + 88 + Z.of_nat kk) with (g + (88 + Z.of_nat kk)) by lia. apply Kg. clear - Hkk; lia.
- intros j f Hj Hfj. pose proof (proj2 HT1 j f ltac:(clear - Hj; lia) Hfj) as Hof.
destruct (slot_frame g s s1 N j f HOK HWF Hfj) as (f' & Hfj' & Efb).
assert (Hfin : In (fr_ptr f, FRAME_SIZE) (frames_blocks N (skipn (Datatypes.S 0) (cg_frames s)))).
{ apply (frames_blocks_in N (cg_frames s) _ j f' _ Hj Hfj'). rewrite Efb. left. reflexivity. }
assert (Hfc : In (fr_ptr f, FRAME_SIZE) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]. unfold fr_blocks. change (Z.to_nat 0) with 0%nat.
rewrite (frames_blocks_skipn N (cg_frames s) 0) by (rewrite Hlen; lia). cbn [app]. right. apply in_or_app. left. apply in_or_app. right. apply in_or_app. right. exact Hfin. }
assert (Hf2 : In (fr_ptr f, FRAME_SIZE) (ablocks B ly2 S2)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm2|]. cbn [app]. right. apply in_or_app. right. apply in_or_app. left. exact Hfin. }
assert (Dgf' : g + 96 <= fr_ptr f \/ fr_ptr f + 40 <= g).
{ pose proof (sep_hd_in B LAWS lyc Sc Wc memc mdc (g, CGIF_SIZE) (fr_ptr f, FRAME_SIZE) _ HAR HPerm1) as D.
unfold zdisjoint, block_rng in D. cbn [fst snd] in D. change (req_size CGIF_SIZE) with 96 in D. change (req_size FRAME_SIZE) with 40 in D.
apply D. apply in_or_app. left. apply in_or_app. right. unfold fr_blocks in |- *. change (Z.to_nat 0) with 0%nat.
rewrite (frames_blocks_skipn N (cg_frames s) 0) by (rewrite Hlen; lia). apply in_or_app. right. exact Hfin. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ (fr_ptr f) FRAME_SIZE HAR Hfc) as (_ & Hf4096 & Hfceil & _). change (req_size FRAME_SIZE) with 40 in Hfceil.
apply (obj_at_blk_kept (w_H Wc) (w_H W2) memc mem2 (fr_ptr f) LAY_Frame _ 40 Hof lay_inside_Frame).
intros i Hi.
pose proof (blk_kept_call B _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fr_ptr f) FRAME_SIZE HJc2 Hfc Hf2) as Kf.
rewrite (Kf ltac:(intros ii Hii; apply (HnFf j f ii Hj Hfj); change (req_size FRAME_SIZE) with 40 in Hii; exact Hii) i ltac:(change (req_size FRAME_SIZE) with 40; exact Hi)).
apply UN; clear - Hi Dgf' Hgh Hgceil Hf4096 Hfceil C1 C3; lia. }
split; [exact HOK |]. unfold fr_blocks. change (Datatypes.S (Z.to_nat 0)) with (Datatypes.S 0). cbn [app]. rewrite <- ?app_assoc. exact HPerm2.
- clear - Hk Hev2. lia.
-
split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]].
+ rewrite (CS 2%bv ltac:(unfold acallee_saved; rewrite bv_unsigned_BV; lia)). rewrite Q2. rewrite (EEo 2%nat 2%bv eq_refl). exact Rsp.
+ rewrite (CS 3%bv ltac:(unfold acallee_saved; rewrite bv_unsigned_BV; lia)). exact Q3'.
+ rewrite (CS 4%bv ltac:(unfold acallee_saved; rewrite bv_unsigned_BV; lia)). exact Q4'.
+ rewrite (CS 8%bv ltac:(unfold acallee_saved; rewrite bv_unsigned_BV; lia)). rewrite Q8. exact E32.
+ rewrite (CS 9%bv ltac:(unfold acallee_saved; rewrite bv_unsigned_BV; lia)). rewrite Q9. cbn [sv_denot]. rewrite E32u. reflexivity.
+ rewrite (CS 19%bv ltac:(unfold acallee_saved; rewrite bv_unsigned_BV; lia)). rewrite Q19. exact (denot_shx E 32 38 88 g SB E32 E38 ltac:(lia) ltac:(lia) ltac:(clear - Hgceil C1; lia) ltac:(unfold SB; lia)).
+ rewrite (CS 18%bv ltac:(unfold acallee_saved; rewrite bv_unsigned_BV; lia)). rewrite Q18. exact E38.
+ rewrite (CS 20%bv ltac:(unfold acallee_saved; rewrite bv_unsigned_BV; lia)). rewrite Q20, (EEo 20%nat 20%bv eq_refl). exact R20.
+ intros r Hr. rewrite (HP2 r ltac:(unfold acallee_saved; lia)).
assert (Hr4 : r = 25 \/ r = 26 \/ r = 27) by lia.
destruct Hr4 as [-> | [-> | ->]];
((first [rewrite (st_ok_pi_restrict_reg (w_H Wc) E _ _ _ HS) | rewrite (st_ok_restrict_reg SEGS (w_H Wc) E _ _ _ HS)]); cbn [ms_regs];
lazymatch goal with |- sv_denot _ (sr_get ?a ?rr2) = _ => let v := eval vm_compute in (sr_get a rr2) in change (sr_get a rr2) with v end;
cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
lazymatch goal with |- ew _ ?n = getr _ (Z_to_bv 5 ?rr) => rewrite (EEo n (Z_to_bv 5 rr) eq_refl); apply Rhi; lia end).
- rewrite (CS 21%bv ltac:(unfold acallee_saved; rewrite bv_unsigned_BV; lia)). rewrite Q21. apply bv_eq. vm_compute. reflexivity.
- rewrite (CS 22%bv ltac:(unfold acallee_saved; rewrite bv_unsigned_BV; lia)). rewrite Q22. apply bv_eq. vm_compute. reflexivity. }
change (Z.to_nat 0) with 0%nat in HT1.
assert (HN0 : 0 <= N) by (clear - HWF; destruct HWF as (_ & HW1 & HH1 & HN & _); nia).
destruct (nth 0 (cg_frames s1) None) as [f|] eqn:Hfi.
-
cbn [frame_ptr] in Efp.
assert (HfI : nth_error (cg_frames s1) 0 = Some (Some f)) by (rewrite (nth_error_nth' (cg_frames s1) None) by (rewrite Hlen1; lia); rewrite Hfi; reflexivity).
destruct (slot_frame g s s1 N 0 f HOK HWF HfI) as (f' & HfI' & SL).
pose proof (nth_error_nth (cg_frames s) 0 None HfI') as Hfi'.
rewrite Hfi' in HBL. cbv beta iota in HBL. rewrite SL in HBL.
pose proof (proj2 HT1 0%nat f (le_n _) HfI) as Hof.
assert (Hfc : In (fr_ptr f, FRAME_SIZE) (ablocks B lyc Sc)) by (eapply Permutation_in; [apply Permutation_sym; exact HBL|]; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ (fr_ptr f) FRAME_SIZE HAR Hfc) as (Hf16 & Hf4096 & Hfceil & _). change (req_size FRAME_SIZE) with 40 in Hfceil.
assert (SEPg : forall p n, In (p, n) (frame_blocks N f) -> p + req_size n <= g \/ g + 96 <= p).
{ intros p n Hpn. pose proof (sep_app B LAWS lyc Sc Wc memc mdc (p, n) (g, CGIF_SIZE) _ _ HAR HBL Hpn ltac:(left; reflexivity)) as D.
unfold zdisjoint, block_rng in D. cbn [fst snd] in D. change (req_size CGIF_SIZE) with 96 in D. clear - D. lia. }
assert (Dgf : g + 96 <= fr_ptr f \/ fr_ptr f + 40 <= g).
{ pose proof (SEPg (fr_ptr f) FRAME_SIZE ltac:(left; reflexivity)) as D. change (req_size FRAME_SIZE) with 40 in D. clear - D. lia. }
lazymatch goal with |- SRr _ _ (mkCfg (mkst _ _ ?mm _) _) _ =>
assert (Hof' : obj_at SEGS (mrestrict (w_H Wc) mm) (fr_ptr f) LAY_Frame (frame_vals f))
by (apply (obj_at_kept _ _ (fr_ptr f) LAY_Frame (frame_vals f) 40 Hof lay_inside_Frame);
intros i Hi; apply (mbyte_of_aview SEGS); apply UN; clear - Hi Dgf Hgh Hgceil Hf4096 Hfceil C1 C3; lia) end.
pose proof (obj_at_nth SEGS _ _ _ _ 0 (0, 8%N) (fr_lpal f) Hof' eq_refl eq_refl) as [Vlp Rlp].
pose proof (obj_at_nth SEGS _ _ _ _ 1 (8, 8%N) (fr_img f) Hof' eq_refl eq_refl) as [Vim Rim].
pose proof (obj_at_nth SEGS _ _ _ _ 2 (16, 4%N) (fr_attr f) Hof' eq_refl eq_refl) as [Vat Rat].
pose proof (obj_at_nth SEGS _ _ _ _ 5 (26, 2%N) (fr_nlp f) Hof' eq_refl eq_refl) as [_ Rnlp].
cbn [fst snd] in Vlp, Rlp, Vim, Rim, Vat, Rat, Rnlp. rewrite Z.add_0_r in Vlp.
change (N.to_nat 8) with 8%nat in Vlp, Vim. change (N.to_nat 4) with 4%nat in Vat.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
eapply SRr_bind;
[ eapply (cl_call B LAWS Wc rg mm _ TCLOSE_STK sp0 (FPc g s N) ly S W mem md [] lyc Sc mdq k FF_STK
(ablocks_fp (ff_blocks (fr_ptr f) (fr_img f) (fr_lpal f) (fr_attr f) N (fr_nlp f))) 3 (-80) (Z_to_bv 64 (BASE + 0x3000)) []
(fun ly3 S3 W3 regs3 mem3 md3 => Permutation (ablocks B ly3 S3) ((g, CGIF_SIZE) :: pal_blocks s ++ frames_blocks N (skipn (Datatypes.S 0) (cg_frames s)) ++ rest)) HJ Qsp);
[ reflexivity | lia | unfold FF_STK, ASTACK; lia | rewrite HTS; unfold FF_STK, ASTACK; lia
| exact Q3' | exact Q4' | exact Q1 | apply ret_ok_codeptr_v; [cbv; split; [congruence | reflexivity] | reflexivity] | rewrite unsigned_lit_small by lia; lia
| exact Qs0
| intros HPRE1; eapply SRr_mono;
[ eapply (pb_freeFrame B LAWS TL ML AFREE Wc lyc Sc rg mm _ [] (fr_ptr f) (fr_lpal f) (fr_img f) (fr_attr f) N (fr_nlp f) _ HPRE1 HEVc);
[ rewrite Q10; cbn [sv_denot]; rewrite Efp; reflexivity
| exact Vlp | exact Vim | exact Vat | clear - Rlp; lia | clear - Rat; lia | exact HN0 | clear - Rnlp; lia
| exact HBL | exact HU1 | exact HU2 | exact HU3 ]
| cbv beta; unfold ff_post; intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ1 & HP & HK);
exists ly3, S3, regs3, mem3, md3; split; [rewrite Q1; reflexivity | split; [exact HJ1 | split; [exact HP | exact HK]]] ]
| intros a Ha; left; destruct (inFP_ablocks_fp_inv _ a Ha) as (p & n & Hpn & Hpa);
change (ff_blocks (fr_ptr f) (fr_img f) (fr_lpal f) (fr_attr f) N (fr_nlp f)) with (frame_blocks N f) in Hpn; split;
[ unfold FPc; replace a with (p + (a - p)) by lia; apply (inFP_ablocks_fp _ p n (a - p)); [| clear - Hpa; lia];
unfold cgif_blocks; right; right; apply in_or_app; right; rewrite <- SL in Hpn;
exact (frames_blocks_in N (cg_frames s) 0 0 f' (p, n) (Nat.le_0_l _) HfI' Hpn)
| exists p, n; split; [eapply Permutation_in; [apply Permutation_sym; exact HBL|]; apply in_or_app; left; exact Hpn | exact Hpa] ] ]
| ] end.
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc2 & HP2 & HPerm2).
apply (CONT W2 ly2 S2 regs2 mem2 md2 3 _ ltac:(lia) HJ2 HJc2 HP2).
+ intros i Hi HFP. destruct (inFP_ablocks_fp_inv _ _ HFP) as (p & n & Hpn & Hpa).
change (ff_blocks (fr_ptr f) (fr_img f) (fr_lpal f) (fr_attr f) N (fr_nlp f)) with (frame_blocks N f) in Hpn.
pose proof (SEPg p n Hpn) as D. clear - D Hi Hpa. lia.
+ intros j f2 i Hj Hf2 Hi HFP. destruct (inFP_ablocks_fp_inv _ _ HFP) as (p & n & Hpn & Hpa).
change (ff_blocks (fr_ptr f) (fr_img f) (fr_lpal f) (fr_attr f) N (fr_nlp f)) with (frame_blocks N f) in Hpn.
destruct (slot_frame g s s1 N j f2 HOK HWF Hf2) as (f2' & Hf2' & Efb).
assert (Hin2 : In (fr_ptr f2, FRAME_SIZE) (frames_blocks N (skipn (Datatypes.S 0) (cg_frames s)))).
{ apply (frames_blocks_in N (cg_frames s) _ j f2' _ Hj Hf2'). rewrite Efb. left. reflexivity. }
pose proof (sep_app B LAWS lyc Sc Wc memc mdc (p, n) (fr_ptr f2, FRAME_SIZE) _ _ HAR HBL Hpn
ltac:(right; apply in_or_app; right; apply in_or_app; left; exact Hin2)) as D.
unfold zdisjoint, block_rng in D. cbn [fst snd] in D. change (req_size FRAME_SIZE) with 40 in D. clear - D Hi Hpa. lia.
+ exact HPerm2.
-
cbn [frame_ptr] in Efp.
destruct (nth 0 (cg_frames s) None) as [f'|] eqn:Hfi'; [discriminate SLOT|]. cbn [app] in HBL.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
eapply SRr_bind;
[ eapply (cl_call B LAWS Wc rg mm _ TCLOSE_STK sp0 (FPc g s N) ly S W mem md [] lyc Sc mdq k FF_STK [] 0 (-80)
(Z_to_bv 64 (BASE + 0x3000)) [] (fun ly2 S2 W2 regs2 mem2 md2 => ly2 = lyc /\ S2 = Sc) HJ Qsp);
[ reflexivity | lia | unfold FF_STK, ASTACK; lia | rewrite HTS; unfold FF_STK, ASTACK; lia
| exact Q3' | exact Q4' | exact Q1 | apply ret_ok_codeptr_v; [cbv; split; [congruence | reflexivity] | reflexivity] | rewrite unsigned_lit_small by lia; lia
| exact Qs0
| intros HPRE1; eapply SRr_mono;
[ apply (pb_freeFrame_null B LAWS Wc lyc Sc rg mm _ [] HPRE1); rewrite Q10, Efp; reflexivity
| cbv beta; intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ1 & HP & HK);
exists ly2, S2, regs2, mem2, md2; split; [rewrite Q1; reflexivity | split; [exact HJ1 | split; [exact HP | exact HK]]] ]
| intros a Ha; exfalso; exact (inFP_nil a Ha) ]
| ] end.
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc2 & HP2 & -> & ->).
apply (CONT W2 lyc Sc regs2 mem2 md2 0 [] ltac:(lia) HJ2 HJc2 HP2).
+ intros i Hi HFP. exact (inFP_nil _ HFP).
+ intros j f2 i Hj Hf2 Hi HFP. exact (inFP_nil _ HFP).
+ exact HBL.
Qed.
End h.
End e.
End c.
