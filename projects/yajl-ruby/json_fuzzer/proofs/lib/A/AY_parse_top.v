(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import InitMem SysStep Image SFW1_lemmas.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.MS Require Import MallocRep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim YajlBase YajlLeaf YajlBuf YajlLex YajlDecode YajlParser YajlFactsBuf YajlFactsLex YajlFactsDecode YajlFactsParse YajlFactsLoop.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RY_lib.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA AImages LazyModel NodesA Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import A_iface AYajlRep AYajl_iface AY_rz AY_hand AY_acct_needs AY_parse_kit AY_parse_pol AY_parse_pro AY_parse_head AY_parse_lex AY_parse_lexc AY_parse_epi AY_parse_tails AY_parse_tails2
     AY_parse_sep AY_parse_sep2 AY_parse_agv AY_parse_agv2 AY_parse_mgv AY_parse_mgv2 AY_parse_map AY_parse_map2 AY_parse_mapk AY_parse_kitD AY_parse_kitD2 AY_parse_mape AY_parse_map3
     AY_parse_gv AY_parse_gv2 AY_parse_kitV AY_parse_gv3 AY_parse_val AY_parse_val2 AY_parse_val3 AY_parse_val4 AY_parse_val5 AY_parse_loop.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Open Scope yprog_scope.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac aceil := first [pose proof alloc_ceiling_range as CEILB | idtac].
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma oshw_hi_0 : oshw_hi 0 (2^47) = 17594333495296. Proof. reflexivity. Qed.

End RC__1.
Ltac ay_statics_open STA :=
  let G1 := fresh "G1" in let G2 := fresh "G2" in let G3 := fresh "G3" in let G4 := fresh "G4" in
  destruct STA as (G1 & G2 & G3 & G4);
  unfold AY_GOT_SHADOW, AY_SHADOW_VAR, AY_GOT_UAR, AY_UAR_VAR, A_SB, wz in G1, G2, G3, G4.

Section RC__2.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section W.
Variable Y : ay_params.
Hypothesis KIPY : AHK_y_kip_stmt Y.
Hypothesis FRAMEY : AHK_y_frame_stmt Y.
Hypothesis BLKY : AHK_y_blocks_stmt Y.
Hypothesis BSHY : AHK_y_block_shadow_stmt Y.
Hypothesis BSMALL : AHK_y_small_high_stmt Y.   (* [comment removed for export] *)
Hypothesis LAYY : AHK_y_layout_stmt Y.
Hypothesis PERMY : AHK_y_perm_stmt Y.
Hypothesis STATY : AHK_y_statics_stmt Y.
Hypothesis RRT : ayR_trans_stmt Y.
Hypothesis NONNEG : yacct_nonneg_stmt Y.
Hypothesis YHM : yacct_hand_mono_stmt Y.
Hypothesis RELY : AHK_y_fake_release_stmt Y.
Hypothesis AFLSEP : AHK_y_aflsep_stmt Y.
Hypothesis FLAGY : AHK_y_flag_cell_stmt Y.
Hypothesis FND : AHK_y_fnodup_stmt Y.
Hypothesis UFRAME : forall m m' SP ra s0, (forall a, SP <= a < 2^47 -> m' (wa a) = m (wa a)) -> y_uanchor Y m SP ra s0 -> y_uanchor Y m' SP ra s0.
Variable phr : Z -> Z -> Z -> Z -> Z.
Hypothesis YSPLIT : yphi_hand_split_stmt Y phr.
Hypothesis WREA : aywrap_realloc_stmt Y.
Variable URA : list Z.
Hypothesis USTEP : forall m SP ra s0 ra' s0', In (bv_unsigned ra) URA -> SP + 16 <= bv_unsigned s0 < 2^47 ->
    rw_cells asegs m (bv_unsigned s0 - 16) [C8 s0'; C8 ra'] -> y_uanchor Y m (bv_unsigned s0) ra' s0' -> y_uanchor Y m SP ra s0.
Hypothesis URA_push : In PUSH_RET URA.
Hypothesis URA_lex : forall pc, lex_site pc -> In (pc + 48) URA.
Hypothesis URA_dec : forall pc, dec_site pc -> In pc URA.
Hypothesis YRP : ayreset_parser_stmt.
Hypothesis GLOBY : AHK_y_globals_shadow_stmt Y.
Hypothesis YCN : aycb_null_stmt.
Hypothesis YCB : aycb_boolean_stmt.
Hypothesis YCNUM : aycb_number_stmt.
Hypothesis YCS : aycb_string_stmt.
Hypothesis YCSM : aycb_start_map_stmt.
Hypothesis YCSA : aycb_start_array_stmt.
Hypothesis YCEA : aycb_end_array_stmt.
Hypothesis YCEM : aycb_end_map_stmt.
Hypothesis YCMK : aycb_map_key_stmt.
Hypothesis YBC : aybuf_clear_stmt.
Hypothesis YBE : aybuf_err_stmt.
Hypothesis YBD : aybuf_data_stmt.
Hypothesis YBL : aybuf_len_stmt.
Hypothesis YBS : aybs_set_stmt.
Hypothesis YSD : aystring_decode_stmt Y.
Hypothesis YSHAPE : yphi_shape_stmt Y.
Hypothesis YLX : aylex_lex_stmt Y.
Hypothesis ASM1 : astack_malloc_stmt Y 1 AY_STACK_MALLOC_1.

Theorem aydo_parse_proof : aydo_parse_stmt Y.
Proof. aceil.
  unfold aydo_parse_stmt. intros LF REST h mh cx T txt OT OTn lo RR K. intros until s.
  intros K0 AY HR CXR TXT T47 L26 TB OTB HINV OSH OSL OSLB OSDB OSSB OCX FCXE FLC1 FLC0 FP EA0 EA1 EA2 CRED RR0 NBIG UA CONT. subst a0 a1 a2.
  destruct FP as (ST & CEIL & LO & SPH & SP16 & MI & TP & FRM).
  apply AYST_split in AY. destruct AY as [AHK0 YS]. pose proof YS as (YCBc & YBAE & YNOOP & STA). ay_statics_open STA.
  unfold wz in TP. unfold wz.
  pose proof LO as LO0. unfold AY_DO_PARSE_STACK, AY_DECODE_STACK, AY_BUF_APPEND_STACK, AMALLOC_STACK in LO0.
  pose proof CEIL as CE. aceil.
  pose proof (bv_unsigned_in_range 64 sp) as SR. unfold bv_modulus in SR. cbn in SR.
  pose proof (zlength_nonneg txt) as NL0.
  pose proof HR as (HS & LXR & DBR & BSR). pose proof HS as ((pew & pad & HC & PW) & BC1 & BC2 & BC3 & BC4).
  pose proof HINV as (LXI & OFFB & DBI & DBOK & (FROK & USZ & BLK & SZK & EOL & EAL) & DEPTH & SZB). cbn [h_stack h_stack_blk h_set_off h_stack_size] in FROK, BLK, SZK, SZB.
  assert (U0 : 0 < h_used h). { unfold h_used. destruct (h_stack h); [destruct FROK| unfold zlength; cbn [length]; clear; lia]. }
  pose proof TXT as (TBY & TFA & T0 & T62).
  (* [comment removed for export] *)
  destruct (BLKY _ _ _ _ _ AHK0) as (RNG & SEP & ND).
  assert (INH : forall b, In b (abl (yblocks mh h)) -> In b (abl (yblocks mh h) ++ REST)) by (intros b Hb; apply in_or_app; left; exact Hb).
  pose proof (RNG _ (INH _ (yb_in_hand mh h))) as RH. unfold ablock_range, ACONSTS in RH. cbn [c_img_hi ab_addr ab_size] in RH. unfold SIZEOF_HANDLE in RH; aceil.
  pose proof (BSMALL _ _ _ _ _ _ AHK0 (INH _ (yb_in_hand mh h)) ltac:(cbn; unfold SIZEOF_HANDLE; lia)) as HLO. cbn [ab_addr] in HLO. rewrite oshw_hi_0 in HLO.
  pose proof (conj (BSMALL _ _ _ _ _ _ AHK0 (INH _ (yb_in_lexer mh h)) ltac:(cbn; unfold SIZEOF_LEXER; lia))
                (conj (BSMALL _ _ _ _ _ _ AHK0 (INH _ (yb_in_lexbuf mh h)) ltac:(cbn; unfold SIZEOF_BUF; lia))
                      (BSMALL _ _ _ _ _ _ AHK0 (INH _ (yb_in_decbuf mh h)) ltac:(cbn; unfold SIZEOF_BUF; lia)))) as STRHI. cbn [ab_addr] in STRHI. rewrite !oshw_hi_0 in STRHI.
  (* [comment removed for export] *)
  arz_seg KIPY AHK0.
  pose proof (aypol_stack Y _ LF _ _ LINK lo (bv_unsigned sp) ltac:(aceil; lia) ltac:(lia)) as PSTK.
  pose proof (aypol_img Y _ LF _ _ LINK) as PIMG. unfold AY_IMG_LO, AY_IMG_HI in PIMG.
  eapply evtA_cut.
  { eapply (pro1_seg _ ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m (mh_addr mh) T (zlength txt) lo);
      [ exact ST | exact MI | exact CE | lia | lia | exact SP16 | exact G1 | exact G2 | exact G3 | exact G4 | lia | lia | lia | lia | exact PSTK | exact PIMG ]. }
  cbv beta. intros ms1 (SQ & jq1 & jq2 & m1 & -> & SQ32 & SQR & MU & WM & MI1 & ST1 & GAP1 & FR1 & SV1).
  apply evtA_done. intros mo1 Hag1 HLI1 Hh1. destruct (BACK mo1 Hag1 HLI1) as [AHKb R1]. clear LINK BACK PSTK PIMG.
  assert (AHK1 : y_AHK Y s (abl (yblocks mh h) ++ REST) LF m1 mo1).
  { eapply FRAMEY; [exact AHKb| exact MU| exact WM|]. constructor; [left; cbn [fst snd]; aceil; lia| constructor]. }
  clear AHKb.
  pose proof (aystatics_munch _ _ _ YS MU WM ltac:(constructor; [cbn [fst snd]; lia| constructor])) as YS1.
  (* [comment removed for export] *)
  assert (BLO : forall b, In b (abl (yblocks mh h)) -> ab_addr b + ab_size b <= lo).
  { intros b Hb. pose proof (RNG b (INH b Hb)) as Rb. unfold ablock_range, ACONSTS in Rb. cbn [c_img_hi] in Rb. aceil. lia. }
  pose proof (hand_rep_below _ _ _ lo h mh HR MU WM ltac:(constructor; [cbn [fst snd]; lia| constructor]) BLO) as HR1.
  destruct FCXE as (fcx & FCXIN & FCXA & FCXC).
  destruct (LAYY _ _ _ _ _ AHK0) as (LAYF0 & LAYFB0 & LAYFF0).
  pose proof (LAYF0 fcx FCXIN) as (FCX1 & FCX2 & FCX3 & FCX4 & _). rewrite FCXC in FCX1, FCX2, FCX3. change (ff_bytes 1) with 128 in FCX1, FCX2, FCX3. unfold amem in FCX1.
  aceil.
  pose proof (ctx_rep_below _ _ _ lo (mh_ctx mh) cx CXR MU WM ltac:(constructor; [cbn [fst snd]; lia| constructor]) ltac:(lia)) as CXR1.
  assert (TLO : zlength txt = 0 \/ T + zlength txt <= lo).
  { destruct TB as [(bt & HBT & BT1 & BT2)| Z0]; [right| left; exact Z0].
    pose proof (RNG bt ltac:(apply in_or_app; right; exact HBT)) as Rb. unfold ablock_range, ACONSTS in Rb. cbn [c_img_hi] in Rb. aceil. lia. }
  pose proof (text_at_below _ _ _ lo T txt TXT MU WM ltac:(constructor; [cbn [fst snd]; lia| constructor]) TLO) as TXT1.
  pose proof (oshadow_below _ _ _ lo (mh_ctx mh) 8 OCX MU WM ltac:(constructor; [cbn [fst snd]; lia| constructor]) ltac:(lia) ltac:(lia) ltac:(lia)) as OCX1.
  assert (PRES1 : ay_pres REST LF (bv_unsigned sp) [(mh_ctx mh, mh_ctx mh + 8)] m m1).
  { eapply ay_pres_of_munch; [exact MU| exact WM|]. intros a Ha Hc _.
    eapply (ay_client_outside_stack Y BLKY LAYY _ _ _ _ _ _ (bv_unsigned sp)); [exact AHK0| intros b0 Hb0; apply in_or_app; right; exact Hb0| aceil; lia| lia| exact Hc]. }
  clear ST MI.
  (* [comment removed for export] *)
  eapply ASM1;
    [ exact K0 | exact AHK1 | exact FLC1
    | rewrite unsigned_lit by lia; exact ST1
    | exact CEIL
    | rewrite unsigned_lit by lia; unfold AMALLOC_STACK; lia
    | rewrite unsigned_lit by lia; lia
    | rewrite unsigned_lit by lia; clear -CEILB SQ32; Z.div_mod_to_equations; lia
    | exact MI1 | exact TP | exact FRM
    | exact CRED
    | ].
  cbv beta. intros t0a t1a t2a a1a a2a a3a a4a a5a a6a a7a t3a t4a t5a t6a F2 fc2 m2 mo2 sa2 FF junk ST2 PRES2 WM2 MI2 FRM2 SO2 FF0 FFal FFsh FFce FFfr FFC FFS FLG AHK2 R2 CRED2.
  rewrite unsigned_lit in ST2, PRES2 by lia.
  change (ff_bytes 1) with 128 in FFal, FFce, FFC, FFfr, FFsh. unfold amem in FFsh.
  change (Z.to_nat (128 - 8)) with 120%nat in FFC. unfold oshw_lo in FFS. change (Z.shiftl 8 1) with 16 in FFS. change (Z.to_nat 16) with 16%nat in FFS.
  replace (A_SB + FF / 8) with (2147450880 + FF / 8) in FFS by reflexivity.
  pose proof FFce as FC. aceil.
  destruct (LAYY _ _ _ _ _ AHK2) as (LAYF2 & LAYFB2 & LAYFF2).
  pose proof (proj1 (LAYFB2 (1, FF) (mkABlock (mh_addr mh) SIZEOF_HANDLE) (or_introl eq_refl) (INH _ (yb_in_hand mh h)))) as SEPHF.
  cbn [fst snd ab_addr ab_size] in SEPHF. change (ff_bytes 1) with 128 in SEPHF. unfold SIZEOF_HANDLE in SEPHF.
  pose proof (aypres_frame _ _ _ _ _ _ _ PRES2 FR1 ltac:(lia)) as FR2. pose proof (aypres_frame _ _ _ _ _ _ _ PRES2 SV1 ltac:(lia)) as SV2. clear FR1 SV1.
  assert (GAP2 : stk asegs m2 (SQ + 240) (bv_unsigned sp + -112)) by (eapply stk_agree; [eapply ay_pres_agree; exact PRES2| exact GAP1| intros a Ha; split; [left; lia| intros F0; exact F0]]). clear GAP1.
  pose proof (aystatics_pres _ _ _ _ _ YS1 PRES2) as (YCB2 & YBAE2 & YNOOP2). pose proof (STATY _ _ _ _ _ AHK2) as STA2.
  assert (YS2 : aystatics m2) by (exact (conj YCB2 (conj YBAE2 (conj YNOOP2 STA2)))). clear YCB2 YBAE2 YNOOP2.
  pose proof (ay_pres_agree _ _ _ _ _ _ PRES2) as AG2.
  assert (OWNCL : forall a, yfoot mh h a -> ay_client_addr (abl (yblocks mh h) ++ REST) LF SQ a /\ ~ yin_ivs [] a).
  { intros a (b & Hb & Ha). split; [| intros X; exact X]. right; left. exists b. split; [exact (INH _ Hb)| exact Ha]. }
  assert (HR2 : ahand_rep m2 h mh) by (eapply hand_rep_agree; [exact AG2| exact HR1| exact OWNCL]).
  assert (CXCL : forall a, (mh_ctx mh <= a < mh_ctx mh + 8 \/ A_SB + mh_ctx mh / 8 <= a < A_SB + mh_ctx mh / 8 + 1) ->
            ay_client_addr (abl (yblocks mh h) ++ REST) LF SQ a /\ ~ yin_ivs [] a).
  { intros a Ha. split; [| intros X; exact X]. right; right; left. exists fcx. split; [exact FCXIN|]. rewrite FCXC. change (ff_bytes 1) with 128. change (Z.shiftl 8 1) with 16.
    clear -CEILB Ha FCXA FCX3. unfold A_SB in *. Z.div_mod_to_equations. lia. }
  assert (CXR2 : actx_rep m2 (mh_ctx mh) cx) by (eapply ctx_rep_agree; [exact AG2| exact CXR1| intros a Ha; apply CXCL; left; exact Ha]).
  assert (OCX2 : oshadow m2 (mh_ctx mh) 8) by (eapply oshadow_agree; [exact AG2| exact OCX1| intros a Ha; apply CXCL; right; revert Ha CEILB; unfold oshw_lo, oshw_hi, A_SB, amem; clear; intros Ha CEILB; Z.div_mod_to_equations; lia]).
  assert (TXT2 : atext_at m2 T txt).
  { eapply aypres_text; [exact PRES2| exact TXT1|]. destruct TB as [(bt & HBT & BT)|Z0]; [left; exists bt; split; [apply in_or_app; right; exact HBT| exact BT]| right; exact Z0]. }
  assert (PRES12 : ay_pres REST LF (bv_unsigned sp) [(mh_ctx mh, mh_ctx mh + 8)] m m2).
  { eapply ay_pres_trans; [exact PRES1|]. eapply (ay_pres_weaken Y); [exact PRES2| lia| intros b0 Hb0; apply in_or_app; right; exact Hb0| intros f Hf; exact Hf| intros a X; destruct X]. }
  (* [comment removed for export] *)
  pose proof HR2 as (((pew2 & pad2 & HC2 & PW2) & _) & _).
  unfold hand_cells, hand_head_cells, alloc_cells in HC2. cbn [yc_callbacks yc_malloc_w yc_realloc_w yc_free_w ayc app] in HC2. unfold wz in HC2.
  pose proof (proj1 (BSHY _ _ _ _ _ _ AHK2 (INH _ (yb_in_hand mh h)) ltac:(cbn; unfold SIZEOF_HANDLE; lia))) as OSH2. cbn [ab_addr ab_size] in OSH2.
  pose proof OSH2 as (_ & _ & SHH2). unfold A_SB, SIZEOF_HANDLE in SHH2.
  clear ST1 MI1 HR1 CXR1 TXT1 OCX1.
  (* [comment removed for export] *)
  replace (ret_pc (Z_to_bv 64 AY_PRO_RET)) with (Z_to_bv 64 AY_PRO_RET) by (symmetry; apply ret_pc_even; [unfold AY_PRO_RET; lia| reflexivity]).
  arz_seg KIPY AHK2. unfold wz.
  pose proof (aypol_stack Y _ ((1, FF) :: LF) _ _ LINK lo (bv_unsigned sp) ltac:(aceil; lia) ltac:(lia)) as PSTK.
  pose proof (aypol_fframe Y _ ((1, FF) :: LF) _ _ LINK (1, FF) FF (FF + 128) (or_introl eq_refl) ltac:(cbn; lia) ltac:(cbn [fst snd]; change (ff_bytes 1) with 128; lia) ltac:(lia) ltac:(cbn [fst snd]; change (ff_bytes 1) with 128; lia)) as PFF.
  pose proof (aypol_ffshadow Y _ ((1, FF) :: LF) _ _ LINK (1, FF) (2147450880 + FF / 8) (2147450880 + FF / 8 + 16) (or_introl eq_refl)
                ltac:(cbn [snd]; unfold oshw_lo, A_SB; lia) ltac:(cbn [fst snd]; unfold oshw_lo, A_SB; change (Z.shiftl 8 1) with 16; lia) ltac:(lia) ltac:(cbn [fst snd]; unfold oshw_lo, A_SB; change (Z.shiftl 8 1) with 16; lia)) as PFFS.
  pose proof (aypol_block Y _ ((1, FF) :: LF) _ _ LINK (mkABlock (mh_addr mh) SIZEOF_HANDLE) (mh_addr mh) (mh_addr mh + 104) (INH _ (yb_in_hand mh h))
                ltac:(cbn; lia) ltac:(cbn; unfold SIZEOF_HANDLE; lia) ltac:(lia) ltac:(cbn; unfold SIZEOF_HANDLE; lia)) as PH.
  pose proof (aypol_bshadow Y _ ((1, FF) :: LF) _ _ LINK (mkABlock (mh_addr mh) SIZEOF_HANDLE) (2147450880 + mh_addr mh / 8) (2147450880 + mh_addr mh / 8 + 13) (INH _ (yb_in_hand mh h))
                ltac:(cbn [ab_addr]; unfold oshw_lo, A_SB; lia) ltac:(cbn [ab_addr ab_size]; unfold oshw_hi, A_SB, amem, SIZEOF_HANDLE; Z.div_mod_to_equations; lia) ltac:(lia)
                ltac:(cbn [ab_addr ab_size]; unfold oshw_hi, A_SB, amem, SIZEOF_HANDLE; lia)) as PHS.
  eapply evtA_cut.
  { eapply (pro2_seg _ sp gp tp t0a t1a t2a a1a a2a a3a a4a a5a a6a a7a s3 s4 s5 s6 s7 s9 s10 s11 t3a t4a t5a t6a F2 fc2 m2 (mh_addr mh) SQ FF lo jq1 jq2 junk T (zlength txt)
              (Z_to_bv 64 (y_aflag Y 1 FF)) pew2 pad2 (blk_shadow 104));
      [ exact ST2 | exact MI2 | exact CE | lia | lia | lia | exact SQ32 | exact FR2 | exact FFC | exact FFS | exact FFsh | exact FC | exact FFal
      | exact HC2 | lia | lia | lia | lia | exact SEPHF | exact SHH2 | reflexivity
      | exact PSTK | exact PFF | exact PFFS | exact PH | exact PHS ]. }
  cbv beta. intros ms3 (k0 & k224 & j1 & j2 & j3 & obw & olw & m3 & -> & MU3 & WM3 & MI3 & ST3 & FR3 & HC3 & FFA3 & OB3 & FJ2 & OL3 & FFZ3 & FSH3 & LJ1 & LJ2 & LJ3).
  apply evtA_done. intros mo3 Hag3 HLI3 Hh3. destruct (BACK mo3 Hag3 HLI3) as [AHKb3 R3]. clear LINK BACK PSTK PFF PFFS PH PHS.
  assert (AHK3 : y_AHK Y sa2 (abl (yblocks mh h) ++ REST) ((1, FF) :: LF) m3 mo3).
  { eapply FRAMEY; [exact AHKb3| exact MU3| exact WM3|].
    constructor; [left; cbn [fst snd]; aceil; lia|].
    constructor; [right; right; left; exists (1, FF); split; [left; reflexivity| cbn [fst snd]; change (ff_bytes 1) with 128; lia]|].
    constructor; [right; right; right; left; exists (1, FF); split; [left; reflexivity| cbn [fst snd]; unfold oshw_lo, A_SB; change (Z.shiftl 8 1) with 16; lia]|].
    constructor; [right; left; exists (mkABlock (mh_addr mh) SIZEOF_HANDLE); split; [exact (INH _ (yb_in_hand mh h))| cbn; unfold SIZEOF_HANDLE; lia]|].
    constructor. }
  clear AHKb3.
  pose proof (aystatics_munch _ _ _ YS2 MU3 WM3 ltac:(repeat (constructor; [cbn [fst snd]; lia|]); constructor)) as YS3.
  (* [comment removed for export] *)
  set (E := mkPE sp gp tp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (reg_get F 8) SQ FF j1 j2 j3 (Z_to_bv 64 (y_aflag Y 1 FF)) lo T txt OT OTn K LF REST mh RR m s mo).
  pose proof (proj1 (LAYFB0 fcx (mkABlock (mh_addr mh) SIZEOF_HANDLE) FCXIN (INH _ (yb_in_hand mh h)))) as SEPHCX.
  cbn [fst snd ab_addr ab_size] in SEPHCX. rewrite FCXC in SEPHCX. change (ff_bytes 1) with 128 in SEPHCX. unfold SIZEOF_HANDLE in SEPHCX.
  pose proof (FFfr fcx FCXIN) as SEPFCX. rewrite FCXC in SEPFCX. change (ff_bytes 1) with 128 in SEPFCX.
  assert (PA : penvA E).
  { constructor; cbn [p_lo p_sp p_SQ p_mh p_ff p_txt p_T p_OT p_OTn p_fj1 p_fj2 p_fj3 E].
    - exact CEIL.
    - lia.
    - split; [exact SPH| exact SP16].
    - split; [exact SQ32| lia].
    - lia.
    - lia.
    - lia.
    - lia.
    - exact SEPHF.
    - lia.
    - lia.
    - lia.
    - intros Hl. destruct OTB as [Z0| (OSHT & O1 & O2 & O3 & O4 & _)]; [exfalso; lia|]. destruct OSHT as (O8 & _ & _). unfold amem in O3.
      aceil. lia.
    - intros Hl. destruct TB as [(bt & HBT & BT1 & BT2)| Z0]; [| exfalso; lia].
      assert (SEPH0 : asep_from (mkABlock (mh_addr mh) SIZEOF_HANDLE) (tl (abl (yblocks mh h)) ++ REST)) by exact (proj1 (ay_all_sep Y BLKY _ _ _ _ _ AHK0)).
      pose proof (asep_from_In _ _ bt SEPH0 ltac:(apply in_or_app; right; exact HBT)) as D1. unfold absep in D1. cbn [ab_addr ab_size] in D1. unfold SIZEOF_HANDLE in D1.
      pose proof (proj1 (LAYFB2 (1, FF) bt (or_introl eq_refl) ltac:(apply in_or_app; right; exact HBT))) as D2. cbn [fst snd] in D2. change (ff_bytes 1) with 128 in D2.
      pose proof (proj1 (LAYFB0 fcx bt FCXIN ltac:(apply in_or_app; right; exact HBT))) as D3. cbn [fst snd] in D3. rewrite FCXC in D3. change (ff_bytes 1) with 128 in D3.
      lia.
    - exact (conj LJ1 (conj LJ2 LJ3)).
    - exact STRHI.
    - (* [comment removed for export] *) clear -CEILB FCX1 FCXA. lia.
    - (* [comment removed for export] *) clear -CEILB FFsh. lia.
    - (* [comment removed for export] *) intros Hl. destruct OTB as [Z0| (OSHT & O1 & O2 & O3 & O4 & _)]; [exfalso; lia|]. unfold amem in O3. clear -CEILB O3. lia. }
  assert (OK : pok E (h_set_off h 0) cx).
  { unfold pok. cbn [p_K p_txt p_REST p_T p_OT p_OTn p_LF p_RR p_tp p_ffp p_ff p_mh E h_stack_blk h_stack_size h_set_off].
    split; [exact K0|]. split; [apply ydo_parse_loop_pre; exact HINV|]. split; [exact U0|].
    split; [split; [exact BLK| destruct SZK as (k & _ & EK); rewrite EK; unfold YAJL_BS_INC; clear; Z.div_mod_to_equations; lia]|].
    split; [exact TB|]. split; [destruct OTB as [Z0| (_ & _ & _ & _ & _ & X)]; [left; exact Z0| right; exact X]|].
    split; [exists fcx; split; [exact FCXIN| split; [exact FCXA| exact FCXC]]|]. split; [exact FLC0|].
    split; [exact NBIG|]. split; [exact RR0|]. split; [exact TP|]. split; [reflexivity| exact FFfr]. }
  (* [comment removed for export] *)
  assert (SAME : mh_same mh mh) by (unfold mh_same; repeat split; reflexivity).
  assert (SZ : 0 < h_stack_size h) by (destruct SZK as (k & Hk & EK); rewrite EK; unfold YAJL_BS_INC; clear -CEILB Hk; lia).
  assert (AHK3' : y_AHK Y sa2 (abl (yblocks mh (h_set_off h 0)) ++ [] ++ p_REST E) (pLF E) m3 mo3) by exact AHK3.
  assert (BLK' : h_stack_blk (h_set_off h 0) <> None) by exact BLK.
  pose proof (mk_pblk BLKY LAYY BSHY E sa2 [] (h_set_off h 0) mh (h_set_off h 0) cx m3 mo3 PA OK AHK3' SAME BLK' SZ) as PB.
  openPB PB. clear PB. cbn [p_mh p_ff p_T p_txt E h_stack_size h_set_off h_lexer h_decbuf] in pb_H0, pb_L0, pb_LB0, pb_DB0, pb_SB0, pb_LD0, pb_DD0, pb_HL0, pb_HLB0, pb_HLD0, pb_HDB0, pb_HDD0, pb_HSB0, pb_LSB0, pb_LBSB0, pb_LDSB0, pb_DBSB0, pb_DDSB0, pb_LCX0, pb_LBCX0, pb_LDCX0, pb_DBCX0, pb_DDCX0, pb_SBCX0, pb_SBff0, pb_DBff0, pb_Lff0, pb_LBff0, pb_LDff0, pb_DDff0, pb_SBT0, pb_SBP0.
  pose proof (munch_agree _ _ _ MU3 WM3) as AG3.
  assert (OUTsep : forall A n a, (A + n <= mh_addr mh \/ mh_addr mh + 104 <= A) -> (A + n <= FF \/ FF + 128 <= A) -> (6303744 <= A /\ (A + n <= 2147446784 \/ 17594333495296 <= A)) -> A + n <= alloc_ceiling ->
            A <= a < A + n -> outside [(SQ, SQ + 240); (FF, FF + 128); (FF / 8 + 2147450880, FF / 8 + 2147450880 + 16); (mh_addr mh + 32, mh_addr mh + 36)] a).
  { intros A n a D1 D2 D3 D4 Ha. cbn. clear -CEILB D1 D2 D3 D4 Ha RH SQR LO0 CE FC FFsh. lia. }
  assert (OUTlow : forall a, (a < 6303744 \/ 2147446784 <= a < 17594333495296) -> (a + 1 <= FF / 8 + 2147450880 \/ FF / 8 + 2147450880 + 16 <= a) ->   (* [comment removed for export] *)
            outside [(SQ, SQ + 240); (FF, FF + 128); (FF / 8 + 2147450880, FF / 8 + 2147450880 + 16); (mh_addr mh + 32, mh_addr mh + 36)] a).
  { intros a Ha Hb. cbn. clear -CEILB Ha Hb RH SQR LO0 CE FC FFsh HLO. lia. }
  assert (OUThi : forall a, SQ + 240 <= a -> outside [(SQ, SQ + 240); (FF, FF + 128); (FF / 8 + 2147450880, FF / 8 + 2147450880 + 16); (mh_addr mh + 32, mh_addr mh + 36)] a).
  { intros a Ha. cbn. clear -CEILB Ha RH SQR LO0 CE FC FFsh HLO. lia. }
  assert (HR3 : ahand_rep m3 (h_set_off h 0) mh).
  { pose proof HR2 as ((_ & B1 & B2 & B3 & B4) & LXR2 & DBR2 & BSR2). split; [| split; [| split]].
    - split; [| cbn [h_bytesConsumed h_stack_size h_used h_stack_blk h_set_off]; refine (conj _ (conj B2 (conj B3 B4))); clear; lia].
      exists pew2, pad2. split; [| exact PW2]. unfold hand_cells, hand_head_cells, alloc_cells. cbn [yc_callbacks yc_malloc_w yc_realloc_w yc_free_w ayc app h_bytesConsumed h_stack_size h_set_off].
      unfold wz. replace (h_used (h_set_off h 0)) with (h_used h) by reflexivity. exact HC3.
    - cbn [h_lexer h_set_off]. eapply lexer_rep_agree; [exact AG3| exact LXR2| | |].
      + intros a Ha. unfold SIZEOF_LEXER in Ha. eapply (OUTsep (mh_lexer mh) 48); [clear -CEILB pb_HL0; lia| exact pb_Lff0| clear -CEILB pb_L0; lia| clear -CEILB pb_L0; lia| exact Ha].
      + intros a Ha. unfold SIZEOF_BUF in Ha. eapply (OUTsep (mb_addr (mh_lexbuf mh)) 32); [clear -CEILB pb_HLB0; lia| exact pb_LBff0| clear -CEILB pb_LB0; lia| clear -CEILB pb_LB0; lia| exact Ha].
      + intros HD. exfalso. apply HD. destruct LXI as (_ & _ & _ & _ & _ & _ & E0). cbn [h_lexer h_set_off] in E0. rewrite E0. reflexivity.
    - cbn [h_decbuf h_set_off]. eapply buf_rep_agree; [exact AG3| exact DBR2| |].
      + intros a Ha. unfold SIZEOF_BUF in Ha. eapply (OUTsep (mb_addr (mh_decbuf mh)) 32); [clear -CEILB pb_HDB0; lia| exact pb_DBff0| clear -CEILB pb_DB0; lia| clear -CEILB pb_DB0; lia| exact Ha].
      + intros HD a Ha. destruct (yb_data (h_decbuf h)) as [d|] eqn:Hd; [| exfalso; apply HD; reflexivity].
        assert (DLEN : 0 < yb_len (h_decbuf h)) by (destruct DBI as (D0 & _ & _ & _ & D4 & _); cbn [h_decbuf h_set_off] in D0, D4; pose proof (D4 ltac:(rewrite Hd; discriminate)); lia).
        pose proof (proj2 (BSHY _ _ _ _ _ _ AHK3 (INH _ (yb_in_decdata mh h ltac:(rewrite Hd; discriminate))) ltac:(cbn; exact DLEN))) as DDLO.
        cbn [ab_addr ab_size] in DDLO. unfold amem in DDLO.
        eapply (OUTsep (mb_data (mh_decbuf mh)) (yb_len (h_decbuf h)));
          [pose proof (pb_HDD0 d eq_refl); clear -CEILB H; lia| exact (pb_DDff0 d eq_refl)| exact DDLO| pose proof (pb_DD0 d eq_refl); clear -CEILB H; lia| exact Ha].
    - eapply bs_rep_agree; [exact AG3| | | cbn [h_stack_size h_set_off]; replace (h_used (h_set_off h 0)) with (h_used h) by reflexivity; exact B3].
      + unfold RYajlRep.bs_rep in BSR2 |- *. cbn [h_stack_blk h_stack h_stack_size h_set_off]. replace (h_used (h_set_off h 0)) with (h_used h) by reflexivity. exact BSR2.
      + cbn [h_stack_size h_set_off]. intros a Ha. yshow pb_SBP0. eapply (OUTsep (mh_stack mh) (h_stack_size h)); [clear -CEILB pb_HSB0; lia| exact pb_SBff0| clear -CEILB pb_SB0 pb_SBP0; lia| clear -CEILB pb_SB0; lia| exact Ha]. }
  assert (CXCL3 : forall a, (mh_ctx mh <= a < mh_ctx mh + 8 \/ A_SB + mh_ctx mh / 8 <= a < A_SB + mh_ctx mh / 8 + 1) ->
            outside [(SQ, SQ + 240); (FF, FF + 128); (FF / 8 + 2147450880, FF / 8 + 2147450880 + 16); (mh_addr mh + 32, mh_addr mh + 36)] a).
  { intros a [Ha|Ha].
    - eapply (OUTsep (mh_ctx mh) 8); [clear -CEILB SEPHCX FCXA; lia| clear -CEILB SEPFCX FCXA; lia| clear -CEILB FCX1 FCXA; lia| clear -CEILB FCX2 FCXA; lia| exact Ha].
    - apply OUTlow; revert Ha SEPFCX FCXA FCX1 FCX2 FCX3 FFal CEILB; unfold A_SB; clear; intros; Z.div_mod_to_equations; lia. }
  assert (CXR3 : actx_rep m3 (mh_ctx mh) cx) by (eapply ctx_rep_agree; [exact AG3| exact CXR2| intros a Ha; apply CXCL3; left; exact Ha]).
  assert (OCX3 : oshadow m3 (mh_ctx mh) 8).
  { eapply oshadow_agree; [exact AG3| exact OCX2|]. intros a Ha. apply CXCL3. right. revert Ha. unfold oshw_lo, oshw_hi, A_SB, amem. clear. intros Ha. Z.div_mod_to_equations. lia. }
  assert (TXT3 : atext_at m3 T txt).
  { eapply text_at_agree; [exact AG3| exact TXT2|]. intros a Ha.
    destruct (Z.eq_dec (zlength txt) 0) as [Z0|NZ]; [exfalso; clear -CEILB Ha Z0; lia|].
    assert (Hl : 0 < zlength txt) by (clear -CEILB NZ NL0; lia). openPA PA. cbn [p_txt p_mh p_ff p_T p_OT p_OTn E] in pa_Tsep0, pa_OT0, pa_OTP0.
    destruct (pa_Tsep0 Hl) as (T1 & T2 & T3). pose proof (pa_OT0 Hl) as (_ & T4 & T5 & T6 & T7).
    yshow pa_OTP0. specialize (pa_OTP0 Hl).
    eapply (OUTsep T (zlength txt)); [clear -CEILB T1; lia| clear -CEILB T2; lia| clear -CEILB T4 T5 T6 pa_OTP0 Ha; lia| clear -CEILB T5 T7; lia| exact Ha]. }
  assert (SV3 : rw_cells asegs m3 (bv_unsigned sp + -112) [C8 (reg_get F 8); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { eapply rw_cells_agree; [exact AG3| exact SV2|]. intros a Ha. apply OUThi. revert Ha. cbn [cells_size csize Nat.add]. clear -CEILB SQR. intros Ha. lia. }
  assert (GAP3 : stk asegs m3 (SQ + 240) (bv_unsigned sp + -112)) by (eapply stk_agree; [exact AG3| exact GAP2| intros a Ha; apply OUThi; clear -CEILB Ha; lia]).
  assert (PRES3 : ay_pres REST LF (bv_unsigned sp) [(mh_ctx mh, mh_ctx mh + 8)] m m3).
  { eapply ay_pres_trans; [exact PRES12|]. eapply ay_pres_of_munch; [exact MU3| exact WM3|].
    intros a Ha Hc Hx. destruct Hc as [Hc|[Hc|[Hc|Hc]]].
    - apply OUThi. clear -CEILB Hc SQR. lia.
    - destruct Hc as (b & Hb & Hr).
      assert (NDa : ab_addr b <> mh_addr mh).
      { intros E0. rewrite map_app in ND. eapply (nodup_app_disj _ _ (mh_addr mh) ND).
        - apply in_map_iff. exists (mkABlock (mh_addr mh) SIZEOF_HANDLE). split; [reflexivity| apply yb_in_hand].
        - apply in_map_iff. exists b. split; [exact E0| exact Hb]. }
      pose proof (SEP _ _ ltac:(apply in_or_app; right; exact Hb) (INH _ (yb_in_hand mh h)) NDa) as D1. cbn [ab_addr ab_size] in D1. unfold SIZEOF_HANDLE in D1.
      pose proof (proj1 (LAYFB2 (1, FF) b (or_introl eq_refl) ltac:(apply in_or_app; right; exact Hb))) as D2. cbn [fst snd] in D2. change (ff_bytes 1) with 128 in D2.
      pose proof (proj2 (BSHY _ _ _ _ _ b AHK0 ltac:(apply in_or_app; right; exact Hb) ltac:(clear -CEILB Hr; lia))) as D3. unfold amem in D3.
      pose proof (RNG _ ltac:(apply in_or_app; right; exact Hb)) as Rb. unfold ablock_range in Rb. aceil.
      eapply (OUTsep (ab_addr b) (ab_size b)); [exact D1| clear -CEILB D2; lia| exact D3| clear -CEILB Rb; lia| exact Hr].
    - destruct Hc as (f' & Hf' & Hr).
      pose proof (LAYF0 f' Hf') as (F1' & F2' & F3' & F4' & _). aceil. unfold amem in F1'.
      pose proof (FFfr f' Hf') as D2.
      destruct Hr as [Hr|Hr].
      + (* [comment removed for export] *)
        pose proof (proj1 (LAYFB0 f' _ Hf' (INH _ (yb_in_hand mh h)))) as D1. cbn [ab_addr ab_size] in D1. unfold SIZEOF_HANDLE in D1.
        eapply (OUTsep (snd f') (ff_bytes (fst f'))); [clear -CEILB D1; lia| clear -CEILB D2; lia| exact F1'| clear -CEILB F2'; lia| exact Hr].
      + apply OUTlow; revert Hr F1' F2' F3' F4' D2 CEILB; clear; unfold oshw_lo, oshw_hi, A_SB, amem; intros Hr F1' F2' F3' F4' D2 CEILB;
          assert (E0 : fst f' = 0 \/ fst f' = 1) by lia;
          (destruct E0 as [E0|E0]; rewrite E0 in Hr, F1', F2', F3', D2;
            [change (ff_bytes 0) with 64 in F1', F2', F3', D2; change (Z.shiftl 8 0) with 8 in Hr| change (ff_bytes 1) with 128 in F1', F2', F3', D2; change (Z.shiftl 8 1) with 16 in Hr]);
          Z.div_mod_to_equations; lia.
    - apply OUTlow; unfold ay_static in Hc; clear -CEILB Hc FFsh; [lia| Z.div_mod_to_equations; lia]. }
  assert (UA3 : y_uanchor Y m3 (bv_unsigned sp) ra s0).
  { eapply UFRAME; [| exact UA]. intros a Ha.
    pose proof (proj1 (munch_agree _ _ _ MU WM a ltac:(clear -CEILB Ha SR; lia) ltac:(cbn; clear -CEILB Ha; lia))) as E1.
    pose proof (proj1 (PRES2 a ltac:(clear -CEILB Ha SR; lia) ltac:(left; clear -CEILB Ha SQR; lia) ltac:(intros X; exact X))) as E2.
    pose proof (proj1 (AG3 a ltac:(clear -CEILB Ha SR; lia) ltac:(apply OUThi; clear -CEILB Ha SQR; lia))) as E3.
    rewrite E3, E2, E1. reflexivity. }
  (* [comment removed for export] *)
  assert (HI : phead_inv E fc2 m3 mo3 sa2 [] (h_set_off h 0) mh cx).
  { split; [| split; [exact OK| split; [exact FRM2| left; reflexivity]]].
    exists obw, olw, (y_phi_hand Y (h_set_off h 0) (zlength txt)). split; [| apply (pcr_full YHM E _ _ PA); cbn [p_txt E]; apply Z.le_refl].
    unfold pmem. cbn [p_REST p_LF p_mh p_SQ p_sp p_T p_txt p_ff p_fj1 p_fj2 p_fj3 p_ffp p_lo p_m0 p_RR p_ra p_s0 p_st0 p_mo0 pLF p_fs0 p_s1 p_s2 p_s3 p_s4 p_s5 p_s6 p_s7 p_s8 p_s9 p_s10 p_s11 E].
    split; [apply AYST_split; split; [exact AHK3| exact YS3]|].
    split; [exact HR3|]. split; [exact SAME|]. split; [exact CXR3|]. split; [exact TXT3|].
    split; [exists k0, k224; unfold pframe; cbn [p_SQ p_ff p_mh p_T p_txt E]; unfold wz; exact FR3|].
    split; [unfold psaved; cbn [p_fs0 p_s11 p_s10 p_s9 p_s8 p_s7 p_s6 p_s5 p_s4 p_s3 p_s2 p_s1 p_s0 p_ra E]; replace (bv_unsigned sp - 112) with (bv_unsigned sp + -112) by (clear; lia); exact SV3|].
    split; [unfold pff, pffA, pffZ; cbn [p_ff p_fj1 p_fj2 p_fj3 p_ffp E]; unfold wz;
            refine (conj FFA3 (conj OB3 (conj FJ2 (conj OL3 (conj FFZ3 _))))); replace (FF / 8 + 2147450880) with (FF / 8 + 2147450880) by reflexivity; exact FSH3|].
    split; [exact OCX3|]. split; [exact ST3|]. split; [replace (bv_unsigned sp - 112) with (bv_unsigned sp + -112) by (clear; lia); exact GAP3|]. split; [exact MI3|].
    split; [exact PRES3|]. split; [exact UA3|].
    split; [destruct NONNEG as (_ & _ & NH & _); pose proof (NH (h_set_off h 0) (zlength txt)); clear -CEILB CRED2 H; split; lia|].
    split; [split; [exact SO2| eapply RRT; [exact R1|]; eapply RRT; [exact R2| exact R3]]|]. split; [exact BLK| reflexivity]. }
  pose proof (ploop Y KIPY FRAMEY BLKY BSHY LAYY PERMY RRT NONNEG YHM RELY AFLSEP FLAGY UFRAME phr YSPLIT WREA URA USTEP URA_push URA_lex URA_dec YRP GLOBY
                YCN YCB YCNUM YCS YCSM YCSA YCEA YCEM YCMK YBC YBE YBD YBL YBS YSD YSHAPE YLX E (parse_fuel (zlength txt)) PA
                F2 fc2 m3 mo3 sa2 [] (h_set_off h 0) mh cx (Z_to_bv 64 AY_PRO_RET)) as LX.
  unfold phead, pstate in LX. cbn [p_SQ p_gp p_tp p_sp p_mh p_ff p_K p_txt E] in LX. unfold wz in LX.
  replace (h_used (h_set_off h 0)) with (h_used h) in LX by reflexivity.
  eapply LX; clear LX; [exact HI| apply (ydo_parse_fuel (zlength txt) h cx); [exact NL0| exact HINV]|].
  (* [comment removed for export] *)
  unfold pexit_cont. cbn [p_st0 p_mo0 p_RR p_lo p_sp p_REST p_LF p_mh p_m0 p_T p_txt p_ra p_gp p_tp p_s0 p_s1 p_s2 p_s3 p_s4 p_s5 p_s6 p_s7 p_s8 p_s9 p_s10 p_s11 p_K E].
  intros until LK. intros R' SO' AR' CRED' A0' MI' ST' FRM' PRES' HR' SAME' CXR' TXT' OSL' OSD' OSS' AY' LKL' LKZ'.
  eapply CONT. unfold aydo_parse_rpost.
  split; [exact SO'|]. split; [exact AR'|]. split; [exact CRED'|].
  split; [split; [exact MI'| split; [exact ST'| split; [exact FRM'| split; [exact I| exact PRES']]]]|].
  split; [rewrite ydo_parse_unfold; exact R'|]. split; [exact A0'|].
  split; [exact HR'|]. split; [exact SAME'|]. split; [exact CXR'|]. split; [exact TXT'|].
  split; [exact OSL'|]. split; [exact OSD'|]. split; [exact OSS'|]. split; [exact LKZ'|]. split; [exact AY'| exact LKL'].
Qed.




End W.
End RC__2.
