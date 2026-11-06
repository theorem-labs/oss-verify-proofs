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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim YajlBase YajlLeaf YajlBuf YajlLex YajlParser YajlFactsBuf YajlFactsLex YajlFactsParse YajlFactsLoop.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RY_lib.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA AImages LazyModel NodesA Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import A_iface AYajlRep AYajl_iface AY_rz AY_hand AY_acct_needs AY_parse_kit AY_parse_pol AY_parse_head AY_parse_epi AY_parse_epi2 AY_parse_tails AY_parse_tails2 AY_parse_sep AY_parse_agv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Zify.zify_internal_to_euclidean_division_equations ::= OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA.LiaFastA.zify_fast_euclid3.   (* [comment removed for export] *)
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
Definition J_GV : Z := 0x88a4c.        (* [comment removed for export] *)
Definition PUSH_AT : Z := 0x88b54.     (* [comment removed for export] *)
Definition PUSH_ROOM : Z := 0x88c24.   (* [comment removed for export] *)
Definition PUSH_RET : Z := 0x88c08.    (* [comment removed for export] *)

Section W.
Variable Y : ay_params.
Hypothesis KIPY : AHK_y_kip_stmt Y.
Hypothesis FRAMEY : AHK_y_frame_stmt Y.
Hypothesis BLKY : AHK_y_blocks_stmt Y.
Hypothesis BSHY : AHK_y_block_shadow_stmt Y.
Hypothesis LAYY : AHK_y_layout_stmt Y.
Hypothesis PERMY : AHK_y_perm_stmt Y.
Hypothesis RRT : ayR_trans_stmt Y.
Hypothesis NONNEG : yacct_nonneg_stmt Y.
Hypothesis YHM : yacct_hand_mono_stmt Y.
Hypothesis RELY : AHK_y_fake_release_stmt Y.
Hypothesis AFLSEP : AHK_y_aflsep_stmt Y.
Hypothesis FLAGY : AHK_y_flag_cell_stmt Y.
Hypothesis UFRAME : forall m m' SP ra s0, (forall a, SP <= a < 2^47 -> m' (wa a) = m (wa a)) -> y_uanchor Y m SP ra s0 -> y_uanchor Y m' SP ra s0.
Variable phr : Z -> Z -> Z -> Z -> Z.
Hypothesis YSPLIT : yphi_hand_split_stmt Y phr.
Hypothesis WREA : aywrap_realloc_stmt Y.
Hypothesis YRP : ayreset_parser_stmt.
Variable URA : list Z.
Hypothesis USTEP : forall m SP ra s0 ra' s0', In (bv_unsigned ra) URA -> SP + 16 <= bv_unsigned s0 < 2^47 ->
    rw_cells asegs m (bv_unsigned s0 - 16) [C8 s0'; C8 ra'] -> y_uanchor Y m (bv_unsigned s0) ra' s0' -> y_uanchor Y m SP ra s0.
Hypothesis URA_push : In PUSH_RET URA.

Let YH_shape : yphi_hand_shape_stmt Y := YH_shape Y phr YSPLIT.

(* [comment removed for export] *)
Lemma push_room : forall (E : apE Y) (F : bvmap 5 word) (fc : bv 32) m mo s LK h0 cx0 h mh cx obw olw cr stp
    (rav t0 t1 a0 a1 a2 a3 a4 a5 a6 a7 s2v t3 t4 t5 t6 : word),
  penvA E -> pok E h0 cx0 -> pmem E m mo s LK h mh cx obw olw cr -> frm0 fc ->
  h_used h < h_stack_size h -> h_stack_size h mod 8 = 0 ->
  yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) h0 cx0) (SR_again (h_set_stack h (stp :: h_stack h)) cx) ->
  pcr E (h_set_stack h (stp :: h_stack h)) cr -> plk_ok LK (h_set_stack h (stp :: h_stack h)) -> pagain Y E h0 cx0 LK ->
  realizes_cfg acfg asegs (mkCfg (pstate E PUSH_ROOM F fc m rav t0 t1 (wz (pH E + 48)) a0 a1 a2 a3 a4 a5 a6 a7 s2v (wz (pH E + 64)) (wz (state_code stp)) t3 t4 t5 t6) mo) (p_K E).
Proof. aceil.
  intros until t6. intros PA OK PM FRM UL SZM' YL PCR PLK AG.
  popen OK PM; yhide TB; yhide OTB; yhide LP; yhide FFR0.
  pose proof (proj2 BC3) as US. pose proof (proj1 BC3) as U0'. assert (SZ : 0 < h_stack_size h) by (clear -CEILB UL U0'; lia).
  pose proof (state_code_range stp) as CR.
  pose proof (mk_pblk BLKY LAYY BSHY E s LK h mh h0 cx0 m mo PA OK AHK SAME SB1 SZ) as PB.
  pose proof (pb_HSB _ _ _ PB) as SEPHS; pose proof (pb_SB _ _ _ PB) as RSB; pose proof (pb_SBA PB) as RSBA; pose proof (pb_SBCX _ _ _ PB) as SEPSC.
  openPA PA; clear pa_ffCX0 pa_ffH0 pa_Tsep0 pa_OT0 pa_j0.
  pose proof SAME as (EH & EL & ELB & EDB & ECX).
  assert (IN : forall b, In b (abl (yblocks mh h)) -> In b (abl (yblocks mh h) ++ LK ++ p_REST E)) by (intros b Hb; apply in_or_app; left; exact Hb).
  pose proof (proj1 (BSHY _ _ _ _ _ _ AHK (IN _ (yb_in_hand mh h)) ltac:(cbn; unfold SIZEOF_HANDLE; lia))) as OSH_H; cbn [ab_addr ab_size] in OSH_H.
  pose proof (proj1 (BSHY _ _ _ _ _ _ AHK (IN _ (yb_in_stack mh h SB1)) ltac:(cbn; lia))) as OSH_S; cbn [ab_addr ab_size] in OSH_S.
  unfold oshadow, A_SB, SIZEOF_HANDLE in OSH_H, OSH_S.
  destruct OSH_H as (_ & _ & SHH); destruct OSH_S as (_ & _ & SHS); rewrite EH in SHH.
  remember (blk_shadow 104) as shb eqn:SHHeq in SHH; remember (blk_shadow (h_stack_size h)) as shs eqn:SHSeq in SHS.
  unfold hand_cells, hand_head_cells, alloc_cells in HC; cbn [yc_callbacks yc_malloc_w yc_realloc_w yc_free_w ayc app] in HC; unfold wz in HC; rewrite EH in HC.
  clear TXT LXR DBR FF OCX GAP PRES UA CRED HS HR; yhide SV. unfold wz in FR.
  pose proof BSR as BSR'. unfold RYajlRep.bs_rep in BSR'. destruct (h_stack_blk h) as [sbk|] eqn:HSB in BSR'; [| exfalso; exact (SB1 HSB)].
  destruct BSR' as (SBNZ & junk & SC).
  destruct (u8arr_of_CB2 _ _ _ _ _ _ _ SC) as (ARR & L1 & L2). clear SC.
  assert (LEN : length (zbytes (stack_bytes (h_stack h)) ++ junk) = Z.to_nat (h_stack_size h)) by (rewrite length_app; clear -CEILB L1 L2 US U0'; lia).
  pose proof SHH as SHH0; yhide SHH0. pose proof SHS as SHS0; yhide SHS0. pose proof ARR as ARR0; yhide ARR0.
  pose proof (munch_refl [(mh_addr (p_mh E) + 60, mh_addr (p_mh E) + 64); (mh_stack mh + h_used h, mh_stack mh + h_used h + 1)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  unfold pstate, PUSH_ROOM, wz.
  arz_seg KIPY AHK.
  pose proof (mk_ppol BLKY LAYY BSHY E s LK h mh h0 cx0 m mo _ _ PA OK AHK SAME SB1 SZ LINK) as PP. openPP PP. pose proof (ppol_mark E mh) as PPM.
  unfold pol, AY_IMG_LO, AY_IMG_HI in pp_stk0, pp_H0, pp_Hs0, pp_SBs0, pp_SB0, pp_img0. clear pp_imgsh0 pp_L0 pp_Ls0 pp_DB0 pp_DBs0 pp_CX0 pp_CXs0 pp_ff0 pp_ffs0 pp_T0 pp_Ts0 LINK.
  shH SHH SHHeq MU WM 48 8.                                (* [comment removed for export] *)
  zstepA. iflit2.                                          (* [comment removed for export] *)
  shH SHH SHHeq MU WM 60 4.                                (* [comment removed for export] *)
  zstepA.                                                  (* [comment removed for export] *)
  zstepA. iflit2.                                          (* [comment removed for export] *)
  zstepA. rewrite ?yzx32_small by (clear -CEILB BC3 BC2; lia).   (* [comment removed for export] *)
  zstepA.                                                  (* [comment removed for export] *)
  zstepA.                                                  (* [comment removed for export] *)
  zstepA.                                                  (* [comment removed for export] *)
  yshow SHS0. shS SHS0 SHSeq MU WM (h_used h) (h_stack_size h). (* [comment removed for export] *)
  zstepA. iflit2.                                          (* [comment removed for export] *)
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    pose proof (u8arr_store_ok_at asegs mx (mh_stack mh) _ (h_used h) ARR ltac:(rewrite LEN; clear -CEILB US UL U0'; lia)) as SOK end.
  stepA.                                                   (* [comment removed for export] *)
  lazymatch type of ARR with u8arr _ ?mx _ _ =>
    pose proof (u8arr_write asegs mx (mh_stack mh) _ (h_used h) (Z_to_bv 8 (state_code stp)) ARR ltac:(rewrite LEN; clear -CEILB US UL U0'; lia)) as ARR' end.
  rewrite le1_wz by (clear -CEILB CR; lia). clear ARR. store_done.
  apply evtA_done. intros mo1 Hag1 HLI1 Hh1. destruct (BACK mo1 Hag1 HLI1) as [AHK1 R01].
  lazymatch goal with |- realizes_cfg _ _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ => rename mx into m2 end.
  pose proof (pmem_remodel E m mo mo1 s LK h mh cx obw olw cr PM AHK1 (RRT _ _ _ _ _ _ R1 R01)) as PM1.
  set (h' := h_set_stack h (stp :: h_stack h)) in *.
  assert (EU : h_used h' = h_used h + 1) by (unfold h_used, h'; cbn [h_stack h_set_stack]; unfold zlength; cbn [length]; clear; lia).
  yshow TB. yshow OTB. yshow LP. yshow FFR0. yshow SV.
  assert (PM2 : pmem E m2 mo1 s LK h' mh cx obw olw cr).
  { eapply (pmem_updA BLKY LAYY BSHY FRAMEY UFRAME E m m2 mo1 s LK h mh cx obw olw cr);
      [exact PA| exact OK| exact PM1| exact SZ| exact MU| exact WM| assumption| | reflexivity| reflexivity| reflexivity| reflexivity| exact I| |
      | eapply ctx_rep_agree; [eapply munch_agree; [exact MU| exact WM]| exact CXR| intros a Ha; cbn; clear -CEILB Ha pa_CXH0 SEPSC US UL U0' EH; lia]
      | exists k0, k224; assumption
      | eapply (rw_cells_transport asegs); [exact SV| exact MU| exact WM| unfold psaved; cbn; clear -CEILB pa_SQ0 pa_lo0 pa_ceil0 pa_H0 RSB US UL U0'; lia]
      | assumption ].
    - constructor; [| constructor; [| constructor]]; unfold ownA; cbn [fst snd]; [left; rewrite EH; clear; lia| right; left; clear -CEILB US UL U0'; lia].
    - split; [| rewrite EU; replace (h_bytesConsumed h') with (h_bytesConsumed h) by reflexivity; replace (h_stack_size h') with (h_stack_size h) by reflexivity;
               replace (h_stack_blk h') with (h_stack_blk h) by reflexivity; rewrite HSB;
               split; [exact BC1| split; [exact BC2| split; [clear -CEILB US UL U0'; lia| split; intros; congruence]]]].
      exists pew, pad. split; [| exact PW].
      unfold hand_cells, hand_head_cells, alloc_cells. rewrite EU.
      replace (h_bytesConsumed h') with (h_bytesConsumed h) by reflexivity. replace (h_stack_size h') with (h_stack_size h) by reflexivity.
      cbn [yc_callbacks yc_malloc_w yc_realloc_w yc_free_w ayc app]. unfold wz. rewrite EH.
      lazymatch goal with H0 : rw_cells asegs m2 (mh_addr (p_mh E)) _ |- _ => exact H0 end.
    - unfold RYajlRep.bs_rep. replace (h_stack_blk h') with (h_stack_blk h) by reflexivity. rewrite HSB, EU. split; [exact SBNZ|].
      destruct junk as [|j0 junk']; [exfalso; cbn [length] in L2; clear -CEILB L2 US UL; lia|].
      exists junk'. replace (h_stack_size h') with (h_stack_size h) by reflexivity. replace (h_stack h') with (stp :: h_stack h) by reflexivity.
      apply (CB2_of_u8arr asegs m2 (mh_stack mh) (zbytes (stack_bytes (stp :: h_stack h))) junk').
      + revert ARR'. rewrite stack_bytes_cons, zbytes_app. cbn [zbytes map]. rewrite <- app_assoc. cbn [app].
        rewrite (upd_app_len _ _ _ _ _) by (rewrite zbytes_length, stack_bytes_length; unfold h_used, zlength; clear; lia).
        intros ARR'. exact ARR'.
      + rewrite zbytes_length, stack_bytes_length. cbn [length]. unfold h_used, zlength. clear. lia.
      + cbn [length] in L2. clear -CEILB L2 US UL. lia. }
  pose proof (J_back Y KIPY BLKY BSHY LAYY RRT E F fc m2 mo1 s LK h0 cx0 h' mh cx obw olw cr) as JB. unfold pstate, J_BACK, wz in JB.
  replace (h_used h + 1) with (h_used h') by exact EU.
  eapply JB; [exact PA| exact OK| exact PM2| exact PCR| exact FRM| exact YL| exact SZM'| exact PLK| exact AG].
Qed.
End W.
End RC__1.
