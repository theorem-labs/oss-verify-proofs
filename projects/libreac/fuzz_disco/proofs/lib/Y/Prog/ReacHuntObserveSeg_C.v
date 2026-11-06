(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the contract and walk of ctrl_lay_block on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8h.v, proofs/cgif/cgif_file_fuzzer/lib/A/AC8k.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChz.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACa2.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACb8.v. *)
(* Modified by Theorem Labs, 2026-10: the walk of ctrl_lay_block on image B (fuzz_grant.asan-ubsan), ported from
   image A's closed walk lib/A/Prog/CtrlLayBlock.v (a working branch 5aae1e8a0ce), itself written with proof steps adapted
   from proofs/cgif/cgif_file_fuzzer/lib/A/AC8h.v, AC8k.v, AChz.v, ACa2.v and ACb8.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/B/Prog/CtrlLayBlock.v, with its module paths, module names and numbers changed; 805 of its 880 lines of code are new or changed and 987 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/Y/Prog/ReacHuntObserveSeg_A.v; 169 of its 238 lines of code are new or changed and 811 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YA0o YA0q YCbm YK06 YI0m YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC44 YC8g YC8i YXcalls YCbj.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YRo.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC1g YC1h YC1i YC45 YC4b YC7k YC81 YC85 YC88 YCbw YCkd YCbf YCj1 YCja YCjr.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import ClassifyCore ReacDiscoClassifyOnSegment ReacDiscoTableObserve.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require ReacFrameCleanLen.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Mem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require
disco_classify_c disco_table_c hunt_c reac_disco_table_observe_c reac_frame_clean_len_c reac_hunt_observe_c
HuntObsFacts HuntObsLib.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import ReacHuntObserveCore.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
Context {PX : PAXcalls lib_both3_0_listing}.
Context {PO : PAObjImg lib_both3_0_listing}.
Context {PW : PAWinImg lib_both3_0_listing}.
Context {PV : PAObjVal lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AMEMCPY : forall fq : YK11.FPState, aintrin_realizes (fx := fq) SEGS B OCpy (SIGMA AS___asan_memcpy).
Hypothesis ABCMP : forall fq : YK11.FPState,
  abcmp_realizes (fx := fq) SEGS B (SIGMA AS___interceptor_trampoline_bcmp).
Hypothesis ASM1 : forall fq : YK11.FPState, astack_malloc_realizes (fx := fq) SEGS B 1.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis TCOS : treac_disco_classify_on_segment_spec B.
Hypothesis TOBS : treac_disco_table_observe_spec B.
Hypothesis HRO : YRo.tfib_ro_unowned B.
#[local] Notation hoC := (@ReacHuntObserveCore.hoC rc PI).
#[local] Notation ho_post := (@ReacHuntObserveCore.ho_post rc SK PI B).
#[local] Notation ho_fsh := (@ReacHuntObserveCore.ho_fsh rc PI).
#[local] Notation ho_cfg := (@ReacHuntObserveCore.ho_cfg rc PI).
#[local] Notation ho_base := (@ReacHuntObserveCore.ho_base rc SK PI B).
#[local] Notation ho_L := (@ReacHuntObserveCore.ho_L rc PI).
#[local] Notation ho_seg_C_stmt := (@ReacHuntObserveCore.ho_seg_C_stmt rc SK PI B).
#[local] Notation ho_seg_E_stmt := (@ReacHuntObserveCore.ho_seg_E_stmt rc SK PI B).
#[local] Notation ho_seg_T_stmt := (@ReacHuntObserveCore.ho_seg_T_stmt rc SK PI B).
Hypothesis hoC_call : ho_seg_E_stmt -> ho_seg_T_stmt ->
  forall (c : hoC) fpos ly2 S2 W2 mem2 md2 k2 regs2 sp1 F (regsY : bvmap 5 word) mdY,
  ho_base c fpos ly2 S2 W2 mem2 md2 k2 (c_H c) regs2 sp1 F ->
  getr regs2 19 = w64 (c_out c) -> getr regs2 20 = w64 (c_now c) -> getr regs2 22 = w64 (c_f c) ->
  getr regs2 26 = w64 SB -> ho_fsh W2 mem2 F ho_shC ->
  (exists ch, achain ly2 (aview SEGS (w_H W2) mem2) (spZ (c_regs c) - 16) (spZ (c_regs c)) ch) ->
  (c_out c <> 0 -> garr8 SEGS (mrestrict (w_H W2) mem2) (c_out c) (map (fun b : byte => bv_unsigned b) (c_O c))) ->
  ajournal SEGS B (c_STK c) (c_sp0 c) (c_FP c) (c_ly c) (c_S c) (c_W0 c) (c_mem0 c) (c_md0 c)
    ((1, fpos) :: c_own c) ly2 S2 W2 mem2 mdY k2 ->
  getr regsY 1 = Z_to_bv 64 (BASE + 0x733c) ->
  getr regsY 10 = Z_to_bv 64 (c_h c + 400) -> getr regsY 11 = Z_to_bv 64 (c_f c) ->
  getr regsY 12 = w64 (ho_L c) -> getr regsY 13 = Z_to_bv 64 (c_h c + 412) ->
  getr regsY 14 = Z_to_bv 64 (F + 32) -> getr regsY 23 = Z_to_bv 64 (F + 32) ->
  getr regsY 2 = getr regs2 2 -> getr regsY 3 = getr regs2 3 -> getr regsY 4 = getr regs2 4 ->
  getr regsY 8 = getr regs2 8 -> getr regsY 9 = getr regs2 9 -> getr regsY 18 = getr regs2 18 ->
  getr regsY 19 = getr regs2 19 -> getr regsY 20 = getr regs2 20 -> getr regsY 21 = getr regs2 21 ->
  getr regsY 22 = getr regs2 22 -> getr regsY 24 = getr regs2 24 -> getr regsY 25 = getr regs2 25 ->
  getr regsY 26 = getr regs2 26 -> getr regsY 27 = getr regs2 27 ->
  SRr SEGS W2 (mkCfg (mkst (fx := c_fq c) regsY (Z_to_bv 64 (BASE + AF_both3_reac_disco_classify_on_segment)) mem2
    (seg_rom SEGS)) mdY) (ho_post c).

Local Strategy expand [zalu_raw zmd_raw].
Lemma ho_seg_C : ho_seg_E_stmt -> ho_seg_T_stmt -> ho_seg_C_stmt.
Proof.
intros HE HT. unfold ho_seg_C_stmt.
intros c fpos ly2 S2 W2 mem2 md2 k2 regs2 sp1 F Hbase H19 H20 H22 H23 H26 Hfsh Hch HGO HKM2 HKT2.
pose proof Hbase as (HPRE & HMID & HSP1 & HFeq & HREGS & HSAVED).
pose proof HMID as (HJ & Hfrs2 & Hfa2 & Hperm & HKEPT & HROD2 & HGh & HlenH & Hflag120 & Hk2le).
pose proof HSP1 as (Hsp1eq & Hsp1win & Hsp1mod).
pose proof HREGS as (R2 & R3 & R4 & R8 & R9 & R18 & R21 & R24 & R25).
pose proof HPRE as ((mdc & HJ0) & HROD & Hra & Hra4 & Hgp & Htp & Hal16 & Hwin1 & Hwin2 & Hdepth & Hlen & Hnow & Hout &
  Hh0 & Hh8 & Hin & Hhb & Hhe & Hwr & HOK & LFB & HGH & Hfr50 & Houtp & HKM & HKT).
pose proof HJ as (HAR2 & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & HcA & HcB & HcC & HcD & HcE & Hpres2 &
  (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop) & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hin1 : In (1%Z, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 fpos HAR2 Hin1) as (HF4096 & HFceil & HFapp).
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR2 Hin1) as (HFal & [HFhi _] & HFpres & HFSpres).
assert (HFaddr : frame_addr ly2 1 fpos = F) by (rewrite Hfa2; symmetry; exact HFeq).
rewrite HFaddr in HF4096, HFceil, HFapp, HFal, HFpres, HFSpres.
assert (Hfb : fs_frame_bytes 1 = 128) by reflexivity.
rewrite Hfb in HFceil, HFapp, HFpres, HFSpres.
assert (Hhb2 : In (c_hb c, c_hn c) (ablocks B ly2 S2)) by (apply (Permutation_in _ (Permutation_sym Hperm)); exact Hin).
destruct (al_blocks _ _ LAWS _ _ _ _ _ (c_hb c) (c_hn c) HAR2 Hhb2) as (Hb16 & Hb4096 & Hbceil & Hbapp & Hbpres & _).
assert (HFR : REAC_HUNT_OBSERVE_STK = 8688) by reflexivity.
assert (HCS : CLS_STK = 8512) by reflexivity.
remember (Eimg (Ereg regs2 [])) as E eqn:HEd.
assert (HEI : img_env VAL A_LIM E) by (rewrite HEd; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs2 r)
  by (intros n r Hn; rewrite HEd; apply ew_Eimg_Ereg_nat; exact Hn).
assert (HAE : env_agree 32 (Ereg regs2 []) E)
  by (rewrite HEd; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (HS : st_ok_pi (fx := c_fq c) SEGS VAL E (mkSS 0x730c sr_atoms [] None (mkFacts [(21%nat, HPTR 3)] [] []))
  (restrict (w_H W2) (mkst (fx := c_fq c) regs2 (Z_to_bv 64 (BASE + 0x730c)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - rewrite HEd. apply regs_ok_Eimg_Ereg.
  - reflexivity.
  - constructor.
  - exact I.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
    rewrite (EE 21%nat 21%bv eq_refl), R21. unfold w64. rewrite unsigned_lit_small by lia.
    change (2 ^ 3) with 8. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hbapp.
    repeat split; first [exact I | lia]. }
assert (SHOK : sh_ok SEGS (SLit SHADOW_OFF) [] E
  (mrestrict (w_H W2) (ms_mem (mkst (fx := c_fq c) regs2 (Z_to_bv 64 (BASE + 0x730c)) mem2 (seg_rom SEGS)))))
  by constructor.
unfold ho_cfg.
pose (RUN := paj_run (fx := c_fq c) B LAWS).
pose (BR := paj_branch (fx := c_fq c) (PI := PI)).
paj_run_tok RUN HS HJ SHOK (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1); [apply awr_ok_nil|].
assert (Em1 : ms_mem ms = mem2)
  by (apply FunctionalExtensionality.functional_extensionality; intros x; apply HF; intros (r & Hr & _); destruct Hr).
rewrite pa_sigma_reac_frame_clean_len in HS.
lazymatch type of HS with st_ok _ _ (setpc ?ssx _) ?msx =>
  assert (HS1 : st_ok_pi (fx := c_fq c) SEGS VAL E (setpc ssx AF_both3_reac_frame_clean_len) msx) by exact HS end.
clear HS HF HFr HG.
pose proof (pa_obj_img_all 63 ltac:(vm_compute; lia)) as HO63. pose proof (pa_obj_img_all 64 ltac:(vm_compute; lia)) as HO64.
unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in HO63, HO64.
assert (B63 : base_val E (Some (A_OBJ 63)) = VAL (A_OBJ 63)).
{ cbn [base_val]. rewrite HEd, Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia). apply unsigned_lit_small.
  exact (pa_val_range (A_OBJ 63)). }
assert (B64 : base_val E (Some (A_OBJ 64)) = VAL (A_OBJ 64)).
{ cbn [base_val]. rewrite HEd, Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia). apply unsigned_lit_small.
  exact (pa_val_range (A_OBJ 64)). }
pose proof (ReacFrameCleanLen.fcl_sep _ _ _ _ HKM2 HKT2) as Hsep6364.
lazymatch type of HS1 with st_ok_pi _ _ _ ?ssv ?msv =>
  pose proof (st_ok_pi_add_region E ssv msv
    (YP09.mkRegion (Some (A_OBJ 63)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SLit reac_frame_clean_len_c.KM))]) HS1 eq_refl
    ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]; rewrite B63;
          split; [lia|]; split; [lia|]; split; [intros o Ho; lia|]; constructor; [|constructor];
          apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 63)) 0 8 (SLit reac_frame_clean_len_c.KM) reac_frame_clean_len_c.KM);
          [reflexivity | unfold reac_frame_clean_len_c.KM; lia | lia |];
          rewrite Z.add_0_r; cbn [ms_mem restrict]; rewrite Em1; exact HKM2)
    ltac:(cbn; exact I)) as HS2 end.
clear HS1.
lazymatch type of HS2 with st_ok_pi _ _ _ ?ssv ?msv =>
  pose proof (st_ok_pi_add_region E ssv msv
    (YP09.mkRegion (Some (A_OBJ 64)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SLit reac_frame_clean_len_c.KT))]) HS2 eq_refl
    ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]; rewrite B64;
          split; [lia|]; split; [lia|]; split; [intros o Ho; lia|]; constructor; [|constructor];
          apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 64)) 0 8 (SLit reac_frame_clean_len_c.KT) reac_frame_clean_len_c.KT);
          [reflexivity | unfold reac_frame_clean_len_c.KT; lia | lia |];
          rewrite Z.add_0_r; cbn [ms_mem restrict]; rewrite Em1; exact HKT2)
    ltac:(cbn [all_disjoint ss_mem setpc]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi];
          rewrite B63, B64; split; [lia | exact I])) as HS3 end.
clear HS2. rename HS3 into HS. norm_ss HS.
paj_run_tok RUN HS HJ SHOK (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1); [awr_ok_tac|].
assert (Em2 : ms_mem ms0 = ms_mem ms)
  by (apply FunctionalExtensionality.functional_extensionality; intros x; apply HF; intros (r & Hr & Hx);
      cbn [ss_mem In] in Hr; destruct Hr as [<- | [<- | []]]; cbn [YP09.r_wlo YP09.r_whi] in Hx; lia).
clear HF HFr HG.
assert (E21 : ew E 21 = Z_to_bv 64 (c_h c)) by (rewrite (EE 21%nat 21%bv eq_refl); exact R21).
assert (E22 : ew E 22 = Z_to_bv 64 (c_f c)) by (rewrite (EE 22%nat 22%bv eq_refl); exact H22).
assert (E23 : ew E 23 = Z_to_bv 64 (c_len c)) by (rewrite (EE 23%nat 23%bv eq_refl); exact H23).
assert (E25 : ew E 25 = Z_to_bv 64 F) by (rewrite (EE 25%nat 25%bv eq_refl); exact R25).
assert (Hhlt : c_h c + 480 <= YM05.alloc_ceiling) by lia.
assert (HFlt : F + 128 <= YM05.alloc_ceiling) by lia.
psrr_branch_tok RUN BR HS SHOK (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1);
paj_run_tok RUN HS HJ SHOK (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1); try awr_ok_tac.
all: assert (Em3 : ms_mem ms1 = ms_mem ms0)
  by (apply FunctionalExtensionality.functional_extensionality; intros x; apply HF; intros (r & Hr & Hx);
      cbn [ss_mem In] in Hr; destruct Hr as [<- | [<- | []]]; cbn [YP09.r_wlo YP09.r_whi] in Hx; lia).
all: clear HF HFr HG.
all: prreg HS (1%bv : bv 5) Q1; prreg HS (10%bv : bv 5) Q10; prreg HS (11%bv : bv 5) Q11;
  prreg HS (13%bv : bv 5) Q13; prreg HS (14%bv : bv 5) Q14; prreg HS (23%bv : bv 5) Q23.
all: assert (Q10' : getr (ms_regs ms1) 10 = Z_to_bv 64 (c_h c + 400))
  by (rewrite Q10, E21, unsigned_lit_small by lia; reflexivity).
all: assert (Q11' : getr (ms_regs ms1) 11 = Z_to_bv 64 (c_f c)) by (rewrite Q11, E22; reflexivity).
all: assert (Q13' : getr (ms_regs ms1) 13 = Z_to_bv 64 (c_h c + 412))
  by (rewrite Q13, E21, unsigned_lit_small by lia; reflexivity).
all: assert (Q14' : getr (ms_regs ms1) 14 = Z_to_bv 64 (F + 32))
  by (rewrite Q14, E25, unsigned_lit_small by lia; reflexivity).
all: assert (Q23' : getr (ms_regs ms1) 23 = Z_to_bv 64 (F + 32))
  by (rewrite Q23, E25, unsigned_lit_small by lia; reflexivity).
all: clear Q10 Q11 Q13 Q14 Q23.
all: pose proof (regs_kept_of_st_ok SEGS E _ _ regs2 [] [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 24; 25; 26; 27]%bv HS HAE
  ltac:(vm_compute; reflexivity)) as RK; cbn [ms_regs restrict] in RK.
all: pose proof (RK 2%bv ltac:(cbn; tauto)) as G2; pose proof (RK 3%bv ltac:(cbn; tauto)) as G3;
  pose proof (RK 4%bv ltac:(cbn; tauto)) as G4; pose proof (RK 8%bv ltac:(cbn; tauto)) as G8;
  pose proof (RK 9%bv ltac:(cbn; tauto)) as G9; pose proof (RK 18%bv ltac:(cbn; tauto)) as G18;
  pose proof (RK 19%bv ltac:(cbn; tauto)) as G19; pose proof (RK 20%bv ltac:(cbn; tauto)) as G20;
  pose proof (RK 21%bv ltac:(cbn; tauto)) as G21; pose proof (RK 22%bv ltac:(cbn; tauto)) as G22;
  pose proof (RK 24%bv ltac:(cbn; tauto)) as G24; pose proof (RK 25%bv ltac:(cbn; tauto)) as G25;
  pose proof (RK 26%bv ltac:(cbn; tauto)) as G26; pose proof (RK 27%bv ltac:(cbn; tauto)) as G27; clear RK.
- prreg HS (12%bv : bv 5) Q12. rewrite E23 in Q12.
  rewrite branch_ltu_U, (U_atom E 23 (c_len c) E23 ltac:(lia)), U_lit in Hc by lia. apply Z.ltb_lt in Hc.
  assert (Q12' : getr (ms_regs ms1) 12 = w64 (ho_L c))
    by (rewrite Q12; unfold ho_L, reac_frame_clean_len_c.reac_frame_clean_len_model;
        rewrite (proj2 (Z.leb_gt 54 (c_len c))) by lia; reflexivity).
  pmkst HS. rewrite pa_sigma_reac_disco_classify_on_segment. rewrite Em3, Em2, Em1. rewrite Em3, Em2, Em1 in HJ.
  exact (hoC_call HE HT c fpos ly2 S2 W2 mem2 md2 k2 regs2 sp1 F (ms_regs ms1) _ Hbase H19 H20 H22 H26 Hfsh Hch HGO HJ
    Q1 Q10' Q11' Q12' Q13' Q14' Q23' G2 G3 G4 G8 G9 G18 G19 G20 G21 G22 G24 G25 G26 G27).
- pose proof (st_ok_restrict_reg SEGS _ E _ _ (12%bv : bv 5) HS) as Q12.
  lazymatch type of HS with st_ok _ _ ?ssx _ =>
    let e := eval vm_compute in (sr_get (ss_regs ssx) 12%bv) in change (sr_get (ss_regs ssx) 12%bv) with e in Q12 end.
  cbn [ms_regs restrict mkst] in Q12.
  rewrite denot_lit_U in Q12; rewrite ?U_SAlu, ?U_SMd, ?U_SOff, ?U_SLit in Q12; cbn [zalu_raw zmd_raw] in Q12.
  rewrite E23 in Q12; rewrite unsigned_lit_small in Q12 by lia; rewrite ?Z.add_0_r in Q12.
  rewrite ?(zcanon_id (c_len c)) in Q12 by (unfold M64; lia).
  rewrite branch_ltu_U, (U_atom E 23 (c_len c) E23 ltac:(lia)), U_lit in Hc by lia. apply Z.ltb_ge in Hc.
  rewrite ReacFrameCleanLen.fcl_arith in Q12 by lia. fold (ho_L c) in Q12.
  assert (HLr : 0 <= ho_L c < 2 ^ 64)
    by (unfold ho_L, reac_frame_clean_len_c.reac_frame_clean_len_model; destruct (_ && _); lia).
  rewrite (zcanon_id (ho_L c)) in Q12 by (unfold M64; lia).
  pmkst HS. rewrite pa_sigma_reac_disco_classify_on_segment. rewrite Em3, Em2, Em1. rewrite Em3, Em2, Em1 in HJ.
  exact (hoC_call HE HT c fpos ly2 S2 W2 mem2 md2 k2 regs2 sp1 F (ms_regs ms1) _ Hbase H19 H20 H22 H26 Hfsh Hch HGO HJ
    Q1 Q10' Q11' Q12 Q13' Q14' Q23' G2 G3 G4 G8 G9 G18 G19 G20 G21 G22 G24 G25 G26 G27).
Qed.

End h.
End f.
End d.
