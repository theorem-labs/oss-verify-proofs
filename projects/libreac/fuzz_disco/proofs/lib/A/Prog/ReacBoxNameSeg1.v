(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_ctrl_stamp_headamp on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACam.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACbf.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACf6.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v, with its module paths, module names and numbers changed; 361 of its 413 lines of code are new or changed and 1226 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YG0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase DiscoFrame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
YC1g YC1h YC81 YC4b YC45 YC85 YCkd YC1i ACbf ACj1 DiscoACjr DiscoACja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import SbDec ReacBoxName ReacBoxNameCut.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
Definition rbn1_regions : smem :=
  [ YP09.mkRegion (Some 2%nat) (-288) 16 (-288) 0
      [YP09.mkChunk 0 (CVal 8 (SOff 34 0)); YP09.mkChunk 8 (CVal 8 (SOff 35 0))];
    got_regionP; bcell_regionP 32; uar_got_regionP 33; uar_cell_regionP 33 ].
Definition rbn1_facts : facts := mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SB SB 0) ] [] [].
Definition ss_rbn1 : sstate := mkSS AF_reac_box_name sr_atoms rbn1_regions None rbn1_facts.

Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASM3 : forall fq : YK11.FPState, astack_malloc_realizes (fx := fq) SEGS B 3.
Hypothesis TLF : PALibF B.
Hypothesis SMP : stack_malloc_progressP B.
Definition rbn1_extra (display display_len : Z) : list word :=
  map (Z_to_bv 64) [SB; as_uar_cell B; display; display_len].
Definition ERB1 (regs : bvmap 5 word) (display display_len : Z) : env :=
  Eimg (Ereg regs (rbn1_extra display display_len)).
Lemma regs_ok_ERB1 : forall regs d dl, regs_ok (ERB1 regs d dl) sr_atoms regs.
Proof.
intros. unfold ERB1. apply (regs_ok_agree 32 (Ereg regs (rbn1_extra d dl))).
- split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity].
- vm_compute. reflexivity.
- apply regs_ok_Ereg.
Qed.
Lemma rbn1_entry : forall (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
  (regs : bvmap 5 word) (display display_len : Z),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - REAC_BOX_NAME_STK -> spZ regs + 16 <= sp0 ->
  val_mem SEGS (mrestrict (w_H W) memc) (spZ regs) 8 display -> 0 <= display < 2 ^ 64 ->
  val_mem SEGS (mrestrict (w_H W) memc) (spZ regs + 8) 8 display_len -> 0 <= display_len < 2 ^ 64 ->
  st_ok_pi SEGS VAL (ERB1 regs display display_len) ss_rbn1
    (restrict (w_H W) (mkst (fx := fq) regs (Z_to_bv 64 (BASE + AF_reac_box_name)) memc (seg_rom SEGS))).
Proof.
intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs display display_len
HJ Hal16 Hbud Hsp Md Rd Mdl Rdl.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres &
  (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop) & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_BOX_NAME_STK = 8784) by reflexivity.
destruct (al_const _ _ LAWS lyc Sc W memc mdc HAR) as (Kcell & Kuar & Kgot & Kguar).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
rewrite (pal_got_uar B TL) in Kguar.
pose proof (pa_obj_img 0%nat ltac:(unfold disco_nobj; lia)) as Hob0.
pose proof (pa_obj_img 1%nat ltac:(unfold disco_nobj; lia)) as Hob1.
pose proof (pa_obj_img 66%nat ltac:(unfold disco_nobj; lia)) as Hob66.
pose proof (palf_uar_img B TL) as Huar.
pose proof (palf_sep B TLF) as Hsep. cbn [zseps zseps_from fst snd] in Hsep.
rewrite restrict_mkst_fx.
set (E := ERB1 regs display display_len).
assert (EL : forall m, (m < A_TEXT)%nat -> ew E m = ew (Ereg regs (rbn1_extra display display_len)) m)
by (intros m Hm; subst E; unfold ERB1; apply Eimg_low; exact Hm).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (as_uar_cell B)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 display) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 display_len) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (EO0 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0)))
by (subst E; unfold ERB1; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (EO1 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1)))
by (subst E; unfold ERB1; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (EO66 : ew E (A_OBJ 66) = Z_to_bv 64 (VAL (A_OBJ 66)))
by (subst E; unfold ERB1; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall m v, ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some m) = v).
{ intros m v Hm Hv. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hv. }
pose proof (pa_val_range (A_OBJ 0)) as VR0. pose proof (pa_val_range (A_OBJ 1)) as VR1.
pose proof (pa_val_range (A_OBJ 66)) as VR66.
unfold IMG_LO, IMG_TOP in *.
unfold ss_rbn1, rbn1_regions. apply pa_entry_st_ok_full.
- apply regs_ok_ERB1.
- vm_compute. reflexivity.
- unfold got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  * cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split.
    -- intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
    -- constructor; [|constructor; [|constructor]].
       ++ apply (chunk_ok_val SEGS E _ (spZ regs) 0 8 _ display);
          [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
          change (N.to_nat 8) with 8%nat. rewrite Z.add_0_r. exact Md.
       ++ apply (chunk_ok_val SEGS E _ (spZ regs) 8 8 _ display_len);
          [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
          change (N.to_nat 8) with 8%nat. exact Mdl.
  * rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) EO1) by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 66) 0) (VAL (A_OBJ 66)));
    [cbn [sv_denot]; rewrite EO66, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kgot).
  * rewrite (VB (A_OBJ 66) (VAL (A_OBJ 66)) EO66) by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 66)) 0 8 SBx SB);
    [cbn [sv_denot SBx]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kcell).
  * rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) EO0) by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff 33 0) (as_uar_cell B));
    [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kguar).
  * rewrite (VB 33%nat (as_uar_cell B) E33) by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (as_uar_cell B) 0 4 (SLit 1) 1);
    [reflexivity | lia | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rd32 SEGS (w_H W) memc _ _ Kuar).
- apply pairwise_disjoint_of_extents.
  unfold got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite (VB 33%nat (as_uar_cell B) E33) by lia.
  rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) EO0) by lia. rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) EO1) by lia.
  rewrite (VB (A_OBJ 66) (VAL (A_OBJ 66)) EO66) by lia.
  cbn [base_val]. rewrite Usp.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat split; lia.
- unfold rbn1_facts. split; [|split; exact I]. cbn [f_atoms atoms_ok].
  split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite Usp; change (2 ^ 4) with 16;
          split; [lia|]; split; [exact Hal16 | lia]|].
  split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E32, unsigned_lit_small by (unfold SB; lia);
          rewrite Z.pow_0_r; split; [unfold SB; lia|]; split; [apply Z.mod_1_r | unfold SB; lia]|].
  exact I.
Qed.

Lemma rbn1_kept_frame : forall E rs H (m m' : word -> option byte) lo hi,
  frame_of E rs (mrestrict H m) (mrestrict H m') ->
  (forall a, in_wrange E rs a -> lo <= a < hi) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' lo hi HF Hw a Ha Hn. apply aview_eq_of. apply HF. rewrite unsigned_lit_small by lia.
intros Hi. apply Hn. apply Hw. exact Hi.
Qed.
Lemma rbn1_frame_of_region : forall E m spe cs (regs : bvmap 5 word),
  region_ok SEGS E m (YP09.mkRegion (Some 2%nat) (-288) 16 (-288) 0 cs) -> bv_unsigned (ew E 2) = spe ->
  (forall j r, nth_error rbn_saved_regs j = Some r ->
     In (YP09.mkChunk (-8 - 8 * Z.of_nat j) (CVal 8 (SOff (Z.to_nat r) 0))) cs) ->
  (forall r, 0 <= r < 32 -> ew E (Z.to_nat r) = getr regs (Z_to_bv 5 r)) ->
  forall j r, nth_error rbn_saved_regs j = Some r ->
    val_mem SEGS m (spe - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs (Z_to_bv 5 r))).
Proof.
intros E m spe cs regs HR Hsp Hin Hew j r Hj.
assert (Hr : 0 <= r < 32).
{ apply nth_error_In in Hj. unfold rbn_saved_regs in Hj. cbn [In] in Hj. lia. }
replace (spe - 8 - 8 * Z.of_nat j) with (spe + (-8 - 8 * Z.of_nat j)) by lia.
apply (slot_of_region E m spe cs (-288) 16 (-288) 0 (-8 - 8 * Z.of_nat j) (SOff (Z.to_nat r) 0)
  (bv_unsigned (getr regs (Z_to_bv 5 r))) HR Hsp (Hin j r Hj)).
- cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. rewrite (Hew r Hr). symmetry. apply Z_to_bv_bv_unsigned.
- apply bv_unsigned_in_range.
Qed.
Theorem rbn_seg1 : rbn_seg1_stmt B.
Proof.
intros [fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ch f said i o name name_len token token_len
  display display_len sd] HX.
unfold rbn_cx, rbm_args in HX. cbn [ri_fq ri_STK ri_sp0 ri_FP ri_ly ri_S ri_W0 ri_mem0 ri_md0 ri_own ri_lyc ri_Sc
  ri_W ri_memc ri_mdc ri_k ri_regs ri_ch ri_f ri_said ri_i ri_o ri_name ri_name_len ri_token ri_token_len
  ri_display ri_display_len ri_sd] in HX |- *.
destruct HX as (HJ & Hro & Hrv & Hra & Hra4 & Hgp & Htp & Hch & Hal & Hstk & Hsp & Hfrl & H10 & Rf & H11 & Rsaid &
  H12 & Ri & H13 & Ro & H14 & Rn & H15 & Rnl & H16 & Rt & H17 & Rtl & Md & Rd & Mdl & Rdl & Himg & Hargs).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof (rbn1_entry fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs display display_len
  HJ Hal Hstk Hsp Md Rd Mdl Rdl) as HS.
pose proof (@SRr_run_pi_AJ fq _ _ _ _ _ B LAWS) as RUNP.
pose proof (@SRr_run_pi_AJ_call fq _ _ _ _ _ B LAWS) as RUNC.
pose proof (@SRr_run_to_pi_AJ fq _ _ _ _ _ B LAWS) as RUNTOP.
pose proof (paj_branch (fx := fq) (L := disco_listing) (PI := PI)) as BR.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres &
  (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop) & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_BOX_NAME_STK = 8784) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
remember (ERB1 regs display display_len) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs (rbn1_extra display display_len)) E)
  by (subst E; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn; subst E; unfold ERB1; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (exact (EE 2%nat 2%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (E32 : ew E 32 = Z_to_bv 64 SB)
  by (subst E; unfold ERB1; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E35 : ew E 35 = Z_to_bv 64 display_len)
  by (subst E; unfold ERB1; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
clear HE.
unfold cfg_at. change (w64 (BASE + AF_reac_box_name)) with (Z_to_bv 64 (BASE + AF_reac_box_name)).
paj_run_shc RUNP RUNC HS HJ.
{ lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
  let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
  eapply (awr_ok_cons_stack_off E _ _ STK sp0 FP _ _ lyc own 2%nat (spZ regs - sp0));
    [reflexivity | rewrite Usp; lia | cbn; lia | cbn; lia |].
  repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
pose proof (rbn1_kept_frame _ _ _ _ _ (spZ regs - 288) (spZ regs) HFr
  ltac:(intros a (r & Hr & Hw); unfold ss_rbn1, rbn1_regions in Hr; cbn [ss_mem In] in Hr;
        repeat destruct Hr as [<- | Hr]; try destruct Hr;
        unfold got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP in Hw;
        cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; rewrite ?Usp in Hw; lia)) as K1.
rename HG into G1. clear HF HFr.
set (A := 32 * ((spZ regs + -288) / 32)).
destruct (sp1_facts (spZ regs + -288) ltac:(lia) ltac:(rewrite <- Zplus_mod_idemp_l, Hal; reflexivity))
  as (HAr & HAal & HAal16). fold A in HAr, HAal, HAal16.
pmkst HS.
rreg_by HS (2%bv : bv 5) (Z_to_bv 64 A)
  (denot_and_m32 E 2 (spZ regs) (-288) ltac:(rewrite E2; symmetry; apply Z_to_bv_bv_unsigned) ltac:(lia) ltac:(lia)
    ltac:(unfold spZ; apply bv_unsigned_in_range)) R2.
prreg HS (1%bv : bv 5) R1. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
pose proof (count_cid_le_length 3 (frames Sc)) as Hcnt.
assert (Hfs3 : fs_frames 3 = 2048) by reflexivity.
rewrite (palf_sm3 B TLF).
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
  eapply (aj_stack_malloc_at SEGS B LAWS Hsegs (pal_env B TL) ML SMP 3 (ASM3 fq) ltac:(lia) W rg mm
    STK sp0 FP ly S W0 mem0 md0 own lyc Sc _ k (A - sp0) _ HJ) end.
  - unfold spZ at 1. rewrite R2, unsigned_lit_small by lia. lia.
  - rewrite <- Zminus_mod_idemp_l, HAal16, <- Zminus_mod_idemp_r, Hsp0al. reflexivity.
  - lia.
  - rewrite Hes. lia.
  - rewrite R3. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
  - rewrite R4. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
  - exact R1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite Hfs3. lia. }
cbv beta. intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & pos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2 & Hbb2 & Hz & Hflag & HK).
pose proof (proj1 HJ2) as HAR2.
assert (Hfin2 : In (3, pos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 3 pos HAR2 Hfin2) as (HF4096 & HFceil & HFapp).
assert (Hfb3 : fs_frame_bytes 3 = 512) by reflexivity.
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres2 & _).
jafter_call_keep_pi HS 36%nat regs2 (mrestrict (w_H W) mem2) HP2 [0]%nat HS2.
match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict mkst]. apply Forall_cons; [|apply Forall_nil].
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Usp; intros a Ha.
  - apply (mbyte_of_aview SEGS). apply (proj1 HK); [lia | rewrite Hes; lia].
  - intros _. apply (apresent_writable SEGS). apply HJpres2. lia. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 36 (map (getr regs2) CLOB)) as Ev2 eqn:HE2 in HS.
assert (HEI2 : img_env VAL A_LIM Ev2) by (rewrite HE2; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD : forall n, (n < 36)%nat -> ew Ev2 n = ew E n) by (intros n Hn; rewrite HE2; apply YN3v.ew_havoc_old; exact Hn).
assert (E40 : ew Ev2 40 = getr regs2 10)
  by (rewrite HE2; exact (ew_havoc_new E 36 (map (getr regs2) CLOB) 4 (Z_to_bv 64 0) ltac:(cbn; lia))).
assert (Usp2 : bv_unsigned (ew Ev2 2) = spZ regs) by (rewrite OLD by lia; exact Usp).
clear HE2.
paj_run_to_sh RUNTOP HS HJ2 14240.
{ lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
  let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
  eapply (awr_ok_cons_stack_off Ev2 _ _ STK sp0 FP _ _ lyc _ 2%nat (spZ regs - sp0));
    [reflexivity | rewrite Usp2; lia | cbn; lia | cbn; lia |].
  apply awr_ok_nil. }
pose proof (rbn1_kept_frame _ _ _ _ _ (spZ regs - 288) (spZ regs) HFr
  ltac:(intros a (r & Hr & Hw); cbn [ss_mem In] in Hr;
        repeat destruct Hr as [<- | Hr]; try destruct Hr;
        cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; rewrite ?Usp2 in Hw; lia)) as K2.
rename HG into G2. clear HF HFr.
psrr_branch_pi RUNP BR HS.
2: { exfalso. cbn [branch_taken sv_denot] in Hc. rewrite E40, Ha0 in Hc. unfold w64 in Hc.
     rewrite unsigned_lit_small, Z.add_0_r in Hc by lia.
     apply negb_false_iff in Hc. apply bv_eqb_eq in Hc. apply (f_equal bv_unsigned) in Hc.
     rewrite !unsigned_lit_small in Hc by lia. lia. }
paj_run_to_sh RUNTOP HS HJ2 14240.
{ lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
  let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
  eapply (awr_ok_cons_stack_off Ev2 _ _ STK sp0 FP _ _ lyc _ 2%nat (spZ regs - sp0));
    [reflexivity | rewrite Usp2; lia | cbn; lia | cbn; lia |].
  apply awr_ok_nil. }
pose proof (rbn1_kept_frame _ _ _ _ _ (spZ regs - 288) (spZ regs) HFr
  ltac:(intros a (r & Hr & Hw); cbn [ss_mem In add_cond] in Hr;
        repeat destruct Hr as [<- | Hr]; try destruct Hr;
        cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; rewrite ?Usp2 in Hw; lia)) as K3.
rename HG into G3. clear HF HFr.
apply SRr_ret.
pmkst HS.
assert (Gsp : bv_unsigned (getr regs 2) = spZ regs) by reflexivity.
assert (EA : sv_denot Ev2 (SAlu ALU_AND (SOff 2 (-288)) (SLit (-32))) = Z_to_bv 64 A)
  by (apply denot_and_m32; [rewrite OLD, E2 by lia; symmetry; apply Z_to_bv_bv_unsigned | lia | lia
       | unfold spZ; apply bv_unsigned_in_range]).
rreg_by HS (2%bv : bv 5) (Z_to_bv 64 A) EA G2r.
assert (EA9 : sv_denot Ev2 (SAlu ALU_ADD (SAlu ALU_AND (SOff 2 (-288)) (SLit (-32))) (SLit 0)) = Z_to_bv 64 A).
{ change (alu64 ALU_ADD (sv_denot Ev2 (SAlu ALU_AND (SOff 2 (-288)) (SLit (-32)))) (Z_to_bv 64 0) = Z_to_bv 64 A).
  rewrite EA, alu_add_small by (unfold M64; lia). f_equal; lia. }
rreg_by HS (9%bv : bv 5) (Z_to_bv 64 A) EA9 G9r.
assert (GR : forall (r : bv 5) n, getr (ms_regs ms1) r = ew Ev2 n -> (n < 32)%nat -> Z.of_nat n = bv_unsigned r ->
  getr (ms_regs ms1) r = getr regs r).
{ intros r n Hr Hn Hnr. rewrite Hr, OLD by lia. apply EE. exact Hnr. }
prreg HS (3%bv : bv 5) G3r. prreg HS (4%bv : bv 5) G4r. prreg HS (8%bv : bv 5) G8r.
prreg HS (12%bv : bv 5) G12r. prreg HS (13%bv : bv 5) G13r. prreg HS (15%bv : bv 5) G15r.
prreg HS (16%bv : bv 5) G16r. prreg HS (19%bv : bv 5) G19r. prreg HS (20%bv : bv 5) G20r.
prreg HS (22%bv : bv 5) G22r. prreg HS (23%bv : bv 5) G23r. prreg HS (24%bv : bv 5) G24r.
prreg HS (25%bv : bv 5) G25r. prreg HS (26%bv : bv 5) G26r. prreg HS (27%bv : bv 5) G27r.
apply (GR _ 3%nat) in G3r; [|lia|reflexivity]. apply (GR _ 4%nat) in G4r; [|lia|reflexivity].
rewrite OLD, (EE 2%nat 2%bv eq_refl) in G8r by lia.
rewrite OLD, (EE 12%nat 12%bv eq_refl) in G12r by lia. rewrite OLD, (EE 13%nat 13%bv eq_refl) in G13r by lia.
rewrite OLD, (EE 15%nat 15%bv eq_refl) in G15r by lia. rewrite OLD, (EE 11%nat 11%bv eq_refl) in G20r by lia.
rewrite OLD, (EE 16%nat 16%bv eq_refl) in G23r by lia. rewrite OLD, (EE 14%nat 14%bv eq_refl) in G24r by lia.
rewrite OLD, (EE 10%nat 10%bv eq_refl) in G25r by lia. rewrite OLD, (EE 17%nat 17%bv eq_refl) in G27r by lia.
rewrite OLD, E35 in G16r by lia. rewrite OLD, E32 in G22r by lia. rewrite E40, Ha0 in G19r, G26r.
pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as HR0. cbn [ms_mem restrict] in HR0.
exists pos, (ms_regs ms1), lyc, S2, (ms_mem ms1), (with_vm_backing (m_vm_lazy md2) mat1 md2).
split.
{ unfold rbn_cfg, cfg_at, w64. cbn [ri_fq].
  replace (BASE + AF_reac_box_name + RBN_P2) with (BASE + 14240) by (unfold AF_reac_box_name, RBN_P2; lia).
  reflexivity. }
unfold rbn_st2, rbn_mid, rbn_rbase, rbn_kept, rbn_shadow_at, rbn_A, rbn_F, rbn_FL, rbn_SH, rbn_SP.
cbn [ri_fq ri_STK ri_sp0 ri_FP ri_ly ri_S ri_W0 ri_mem0 ri_md0 ri_own ri_lyc ri_Sc
  ri_W ri_memc ri_mdc ri_k ri_regs ri_ch ri_f ri_said ri_i ri_o ri_name ri_name_len ri_token ri_token_len
  ri_display ri_display_len ri_sd].
fold A.
assert (KR : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 288 <= a < spZ regs) ->
  aview SEGS (w_H W) (ms_mem ms1) a = aview SEGS (w_H W) mem2 a).
{ intros a Ha Hn. rewrite (K3 a Ha Hn). exact (K2 a Ha Hn). }
assert (Hwin : forall a, spZ regs - REAC_BOX_NAME_STK <= a < spZ regs -> apresent (w_H W) (ms_mem ms1) a).
{ pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJp & _). intros a Ha. apply HJp. lia. }
split.
{ split; [exact HJ2|]. split; [exact Hfrs2|]. split; [rewrite Eab; apply Permutation_refl|].
  split.
  { intros a Hro0 Ho He.
    assert (Hia : in_img SEGS a)
      by (destruct Hro0 as [(sg & Hsg & _ & Hr) | Hr]; [exists sg; split; [exact Hsg | exact Hr] | exact (pa_relro_img a Hr)]).
    pose proof (Hsegs a Hia) as Hlow.
    rewrite (KR a) by lia. rewrite (proj1 (proj2 (proj2 HK)) a Hia Ho He). rewrite (K1 a) by lia.
    exact (Hro a Hro0 Ho He). }
  split.
  { split; [|split; [|split; [|split; [|split]]]].
    - intros a Ha Hn _. rewrite (KR a) by lia. rewrite (proj1 HK a) by (rewrite ?Hes; lia). rewrite (K1 a) by lia. reflexivity.
    - intros b m j Hb Hj _.
      destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hb) as (_ & Hb4 & Hbc & _).
      rewrite (KR (b + j)) by lia. rewrite (proj1 (proj2 HK) b m j Hb Hj) by (intros []). rewrite (K1 (b + j)) by lia. reflexivity.
    - intros a Hia Ho He. pose proof (Hsegs a Hia) as Hlow.
      rewrite (KR a) by lia. rewrite (proj1 (proj2 (proj2 HK)) a Hia Ho He). rewrite (K1 a) by lia. reflexivity.
    - intros cid p a Hcp Ha _.
      destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid p HAR Hcp) as (Hf1 & Hf2 & Hf3).
      assert (Hac : 0 <= a < alloc_ceiling).
      { pose proof (Z.div_mod (frame_addr lyc cid p) 8 ltac:(lia)) as D1.
        pose proof (Z.mod_pos_bound (frame_addr lyc cid p) 8 ltac:(lia)) as M1.
        pose proof (Z.div_mod (fs_frame_bytes cid) 8 ltac:(lia)) as D2.
        pose proof (Z.mod_pos_bound (fs_frame_bytes cid) 8 ltac:(lia)) as M2.
        pose proof (Z.div_mod (frame_addr lyc cid p + fs_frame_bytes cid) 8 ltac:(lia)) as D3.
        pose proof (Z.mod_pos_bound (frame_addr lyc cid p + fs_frame_bytes cid) 8 ltac:(lia)) as M3.
        pose proof (Z.div_le_mono (frame_addr lyc cid p + fs_frame_bytes cid) alloc_ceiling 8 ltac:(lia) Hf2) as D4.
        pose proof (Z.div_mod alloc_ceiling 8 ltac:(lia)) as D5. pose proof (Z.mod_pos_bound alloc_ceiling 8 ltac:(lia)) as M5.
        destruct Ha as [Ha | Ha]; unfold in_zr, frame_rng, shadow_addr, SHADOW_OFF in Ha; cbn [fst snd] in Ha; lia. }
      rewrite (KR a) by lia. rewrite (proj1 (proj2 (proj2 (proj2 HK))) cid p a Hcp Ha) by (intros []).
      rewrite (K1 a) by lia. reflexivity.
    - intros a Ha Hn Hp. apply (apresent_grows _ _ _ _ G3). apply (apresent_grows _ _ _ _ G2).
      apply (proj1 (proj2 (proj2 (proj2 (proj2 HK)))) a); [lia | rewrite ?Hes; lia|].
      apply (apresent_grows _ _ _ _ G1). exact Hp.
    - exact Hwin. }
  split.
  { unfold rbn_frame, rbn_SP. cbn [ri_regs].
    apply (rbn1_frame_of_region Ev2 _ (spZ regs) _ regs HR0 Usp2).
    - intros j r Hj. unfold rbn_saved_regs in Hj.
      do 13 (destruct j as [|j]; [cbn in Hj; injection Hj as <-; cbn [In]; repeat (first [left; reflexivity | right])|]).
      cbn in Hj. destruct j; discriminate.
    - intros r Hr. rewrite OLD by lia. apply EE. rewrite Z_to_bv_unsigned. unfold bv_wrap.
      change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. lia. }
  split.
  { apply (val_mem_kept SEGS (w_H W) (w_H W) mem2 (ms_mem ms1)).
    - intros k0 Hk0. apply KR; lia.
    - rewrite Hfb3 in Hflag. replace (frame_addr lyc 3 pos + 504) with (frame_addr lyc 3 pos + 512 - 8) by lia.
      exact (val_mem_of_rdword SEGS _ _ _ _ Hflag). }
  intros j Hj. cbn [length repeat] in Hj.
  assert (Hsh : 0 <= shadow_addr (frame_addr lyc 3 pos) + j < alloc_ceiling).
  { unfold shadow_addr, SHADOW_OFF.
    assert (HFle : frame_addr lyc 3 pos <= alloc_ceiling) by (rewrite Hfb3 in HFceil; lia).
    pose proof (Z.div_le_mono (frame_addr lyc 3 pos) alloc_ceiling 8 ltac:(lia) HFle) as D4.
    pose proof (Z.div_mod alloc_ceiling 8 ltac:(lia)) as D5. pose proof (Z.mod_pos_bound alloc_ceiling 8 ltac:(lia)) as M5.
    pose proof (Z.div_pos (frame_addr lyc 3 pos) 8 ltac:(lia) ltac:(lia)). lia. }
  unfold rbn_F. cbn [ri_lyc].
  rewrite (KR (shadow_addr (frame_addr lyc 3 pos) + j)) by lia.
  rewrite nth_repeat. unfold zero_shadow, shadow_of_addr in Hz. rewrite Hfb3 in Hz. change (512 / 8) with 64 in Hz.
  apply Hz. lia. }
split.
{ split; [exact G2r|]. split; [rewrite G3r; exact Hgp|]. split; [rewrite G4r; exact Htp|].
  split; [rewrite G8r; unfold w64, spZ; symmetry; apply Z_to_bv_bv_unsigned|]. split; [exact G9r|].
  split; [exact G19r | rewrite G22r; reflexivity]. }
split; [exact G26r|].
split; [rewrite G20r; exact H11|]. split; [rewrite G23r; exact H16|]. split; [rewrite G24r; exact H14|].
split; [rewrite G25r; exact H10|]. split; [rewrite G27r; exact H17|].
split; [rewrite G12r; exact H12|]. split; [rewrite G13r; exact H13|].
split; [rewrite G15r; exact H15 | exact G16r].
Qed.
End h.
End f.
End d.
