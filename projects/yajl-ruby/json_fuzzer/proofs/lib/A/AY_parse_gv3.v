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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import A_iface AYajlRep AYajl_iface AY_rz AY_hand AY_acct_needs AY_parse_kit AY_parse_pol AY_parse_head AY_parse_epi AY_parse_epi2 AY_parse_tails AY_parse_tails2 AY_parse_sep AY_parse_agv AY_parse_map AY_parse_gv AY_parse_gv2 AY_parse_kitV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac2 small_ctx2 () := if Ltac2.Int.le (Ltac2.List.length (Ltac2.Control.hyps ())) 60 then () else Ltac2.Control.backtrack_tactic_failure "big context".
Definition allow_big_lia : Prop := True.
Ltac small_ctx := first [ match goal with H : allow_big_lia |- _ => idtac end | ltac2:(small_ctx2 ()) ].
Local Ltac lia ::=
  first [ LiaTuning.zify_prune; LiaTuning.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | LiaTuning.zify_prune; Zify.zify; xlia zchecker
        | LiaTuning.zify_lia_keep1
        | small_ctx; Zify.zify; xlia zchecker ].
Local Ltac qlia_sep ::= first [ solve [LiaTuning.zify_prune; Zify.zify; xlia zchecker]
                       | solve [unfold yhide in *; LiaTuning.zify_lia_keep1]
                       | solve [unfold yhide in *; keep_sep; Z.div_mod_to_equations; lia]
                       | unfold yhide in *; Z.div_mod_to_equations; Zify.zify; xlia zchecker ].
Local Open Scope yprog_scope.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac aceil := first [pose proof alloc_ceiling_range as CEILB | idtac].
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
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
Variable URA : list Z.
Hypothesis USTEP : forall m SP ra s0 ra' s0', In (bv_unsigned ra) URA -> SP + 16 <= bv_unsigned s0 < 2^47 ->
    rw_cells asegs m (bv_unsigned s0 - 16) [C8 s0'; C8 ra'] -> y_uanchor Y m (bv_unsigned s0) ra' s0' -> y_uanchor Y m SP ra s0.
Hypothesis URA_push : In PUSH_RET URA.

Hypothesis YRP : ayreset_parser_stmt.
Let YH_shape : yphi_hand_shape_stmt Y := YH_shape Y phr YSPLIT.

(* [comment removed for export] *)
Lemma push_tail : forall (E : apE Y) (F : bvmap 5 word) (fc : bv 32) m mo s h0 cx0 h mh cx obw olw cr stp
    (rav t0 t1 a0 a1 a2 a3 a4 a5 a6 a7 s2v t3 t4 t5 t6 : word),
  penvA E -> pok E h0 cx0 -> pmem E m mo s [] h mh cx obw olw cr -> frm0 fc -> 0 < h_used h ->
  h_stack_size h mod 8 = 0 -> h_stack_size h <= pLEN E + 1 + YAJL_BS_INC ->
  (h_used h < h_stack_size h -> pcr E (h_set_stack h (stp :: h_stack h)) cr) ->
  (h_used h = h_stack_size h ->
      ypushc Y (h_stack_size h) + y_phi_hand Y (h_set_stack3 h (h_stack h) (h_stack_size h + YAJL_BS_INC) None) 0 <= cr /\
      forall p, y_phi_hand Y (h_set_stack3 h (stp :: h_stack h) (h_stack_size h + YAJL_BS_INC) (Some p)) (pLEN E) + ypushc Y (h_stack_size h) <= cr + y_arefund Y (h_stack_size h)) ->
  (forall r, yleaf (r0 <- ybs_push h stp ;; (let '(ok, h2) := r0 in if ok then YRet (SR_again h2 cx) else YRet (SR_done YS_alloc_failed h2 cx))) r ->
             yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) h0 cx0) r) ->
  pagain Y E h0 cx0 [] ->
  pexit_cont E (fun r => let '(st, h', cx') := r in yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) h0 cx0) (SR_done st h' cx')) ->
  realizes_cfg acfg asegs (mkCfg (pstate E PUSH_AT F fc m rav t0 t1 (wz (pH E + 48)) a0 a1 a2 a3 a4 a5 a6 a7 s2v (wz (pH E + 64)) (wz (state_code stp)) t3 t4 t5 t6) mo) (p_K E).
Proof. aceil.
  intros until t6. intros PA OK PM FRM U1 SZM' SZB PCRr PHI2 YGG AG EX.
  popen OK PM; yhide TB; yhide OTB; yhide FFR0; yhide LP.
  pose proof (proj2 BC3) as US. pose proof (proj1 BC3) as U0'. assert (SZ : 0 < h_stack_size h) by (clear -CEILB US U1; lia).
  pose proof (mk_pblk BLKY LAYY BSHY E s [] h mh h0 cx0 m mo PA OK AHK SAME SB1 SZ) as PB. pose proof (pb_SB _ _ _ PB) as RSB. pose proof (pb_SBA PB) as RSBA.
  openPA PA; clear pa_ffCX0 pa_ffH0 pa_Tsep0 pa_OT0 pa_j0 pa_CXH0.
  pose proof SAME as (EH & EL & ELB & EDB & ECX).
  assert (IN : forall b, In b (abl (yblocks mh h)) -> In b (abl (yblocks mh h) ++ [] ++ p_REST E)) by (intros b Hb; apply in_or_app; left; exact Hb).
  pose proof (proj1 (BSHY _ _ _ _ _ _ AHK (IN _ (yb_in_hand mh h)) ltac:(cbn; unfold SIZEOF_HANDLE; lia))) as OSH_H; cbn [ab_addr ab_size] in OSH_H.
  unfold oshadow, A_SB, SIZEOF_HANDLE in OSH_H. destruct OSH_H as (_ & _ & SHH); rewrite EH in SHH.
  remember (blk_shadow 104) as shb eqn:SHHeq in SHH.
  unfold hand_cells, hand_head_cells, alloc_cells in HC; cbn [yc_callbacks yc_malloc_w yc_realloc_w yc_free_w ayc app] in HC; unfold wz in HC; rewrite EH in HC.
  clear TXT LXR DBR GAP PRES UA HR FF OCX SV CRED. unfold wz in FR.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  unfold pstate, PUSH_AT, wz.
  arz_seg KIPY AHK.
  pose proof (mk_ppol BLKY LAYY BSHY E s [] h mh h0 cx0 m mo _ _ PA OK AHK SAME SB1 SZ LINK) as PP. openPP PP. pose proof (ppol_mark E mh) as PPM.
  unfold pol, AY_IMG_LO, AY_IMG_HI in pp_stk0, pp_H0, pp_Hs0, pp_img0. clear pp_imgsh0 pp_L0 pp_Ls0 pp_DB0 pp_DBs0 pp_SB0 pp_SBs0 pp_CX0 pp_CXs0 pp_ff0 pp_ffs0 pp_T0 pp_Ts0 LINK.
  zstepA.                                                  (* [comment removed for export] *)
  shH SHH SHHeq MU WM 56 4.                                (* [comment removed for export] *)
  zstepA. iflit2.                                          (* [comment removed for export] *)
  shH SHH SHHeq MU WM 60 4.                                (* [comment removed for export] *)
  zstepA.                                                  (* [comment removed for export] *)
  zstepA. rewrite ?ysx32_small by (clear -CEILB BC2; lia).       (* [comment removed for export] *)
  zstepA. iflit2.                                          (* [comment removed for export] *)
  zstepA. rewrite ?ysx32_small by (clear -CEILB BC3 BC2; lia).   (* [comment removed for export] *)
  zstepA. if_cases Kc; zify_cond Kc.                       (* [comment removed for export] *)
  - (* [comment removed for export] *)
    apply evtA_done. intros mo1 Hag1 HLI1 Hh1. destruct (BACK mo1 Hag1 HLI1) as [AHK1 R01].
    pose proof (pmem_remodel E m mo mo1 s [] h mh cx obw olw cr PM AHK1 (RRT _ _ _ _ _ _ R1 R01)) as PM1.
    assert (UL : h_used h < h_stack_size h) by (revert Kc; clear -CEILB US; rewrite ?unsigned_lit by lia; intros Kc; lia).
    pose proof (push_room Y KIPY FRAMEY BLKY BSHY LAYY RRT UFRAME E F fc m mo1 s [] h0 cx0 h mh cx obw olw cr stp) as PR. unfold pstate, PUSH_ROOM, wz in PR.
    eapply PR; [exact PA| exact OK| exact PM1| exact FRM| exact UL| exact SZM'| | exact (PCRr UL)| apply plk_ok_nil| exact AG].
    apply YGG. unfold ybs_push. replace (h_stack_size h - h_used h =? 0) with false by (symmetry; apply Z.eqb_neq; clear -CEILB UL; lia). apply yl_ret.
  - (* [comment removed for export] *)
    apply evtA_done. intros mo1 Hag1 HLI1 Hh1. destruct (BACK mo1 Hag1 HLI1) as [AHK1 R01].
    pose proof (pmem_remodel E m mo mo1 s [] h mh cx obw olw cr PM AHK1 (RRT _ _ _ _ _ _ R1 R01)) as PM1.
    assert (FULL : h_used h = h_stack_size h) by (revert Kc; clear -CEILB US BC2; rewrite ?unsigned_lit by lia; intros Kc; lia).
    pose proof (push_realloc Y KIPY FRAMEY BLKY BSHY LAYY PERMY RRT NONNEG YHM UFRAME WREA URA USTEP URA_push
                  E F fc m mo1 s h0 cx0 h mh cx obw olw cr stp) as PG. unfold pstate, PUSH_GROW, wz in PG.
    eapply PG; [exact PA| exact OK| exact PM1| exact FRM| exact U1| exact FULL| exact SZM'| exact SZB| exact (PHI2 FULL)| exact YGG| intros; apply plk_ok_nil| exact AG| exact EX].
Qed.
Definition GV_FIN : Z := 0x88b50.      (* [comment removed for export] *)
Definition GV_RST : Z := 0x88aa4.      (* [comment removed for export] *)

(* [comment removed for export] *)
Definition gv_push (E : apE Y) (h0 : yhandle) (cx0 : yctx) (h1 : yhandle) (cx : yctx) (cr : Z) (s2v s5v : word) (push : option ystate) : Prop :=
  match push with
  | None => bv_unsigned s2v <> 0 /\ pcr E h1 cr /\ yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) h0 cx0) (SR_again h1 cx)
  | Some stp => s2v = wz 0 /\ s5v = wz (state_code stp)
      /\ (h_used h1 < h_stack_size h1 -> pcr E (h_set_stack h1 (stp :: h_stack h1)) cr)
      /\ (h_used h1 = h_stack_size h1 ->
            ypushc Y (h_stack_size h1) + y_phi_hand Y (h_set_stack3 h1 (h_stack h1) (h_stack_size h1 + YAJL_BS_INC) None) 0 <= cr /\
            forall p, y_phi_hand Y (h_set_stack3 h1 (stp :: h_stack h1) (h_stack_size h1 + YAJL_BS_INC) (Some p)) (pLEN E) + ypushc Y (h_stack_size h1) <= cr + y_arefund Y (h_stack_size h1))
      /\ (forall r, yleaf (r0 <- ybs_push h1 stp ;; (let '(ok, h2) := r0 in if ok then YRet (SR_again h2 cx) else YRet (SR_done YS_alloc_failed h2 cx))) r ->
                   yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) h0 cx0) r)
  end.

(* [comment removed for export] *)
Lemma gv_fin : forall (E : apE Y) (F : bvmap 5 word) (fc : bv 32) m mo s h0 cx0 h1 mh cx obw olw cr push
    (rav t0 t1 a0 a1 a2 a3 a4 a5 a6 a7 s2v s5v t3 t4 t5 t6 : word),
  penvA E -> pok E h0 cx0 -> pmem E m mo s [] h1 mh cx obw olw cr -> frm0 fc -> 0 < h_used h1 ->
  h_stack_size h1 mod 8 = 0 -> h_stack_size h1 <= pLEN E + 1 + YAJL_BS_INC ->
  gv_push E h0 cx0 h1 cx cr s2v s5v push -> pagain Y E h0 cx0 [] ->
  pexit_cont E (fun r => let '(st, h', cx') := r in yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) h0 cx0) (SR_done st h' cx')) ->
  realizes_cfg acfg asegs (mkCfg (pstate E GV_FIN F fc m rav t0 t1 (wz (pH E + 48)) a0 a1 a2 a3 a4 a5 a6 a7 s2v (wz (pH E + 64)) s5v t3 t4 t5 t6) mo) (p_K E).
Proof. aceil.
  intros until t6. intros PA OK PM FRM U1 SZM' SZB GP AG EX.
  pose proof PM as (AY & _ & _ & _ & _ & (k0 & k224 & FR) & _ & _ & _ & _ & _ & MI & _ & _ & _ & [_ R1] & _). apply AYST_split in AY. destruct AY as [AHK _].
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  unfold pstate, GV_FIN, wz. arz_seg KIPY AHK. clear LINK.
  zstepA. if_cases Ks; zify_cond Ks.                       (* [comment removed for export] *)
  - (* [comment removed for export] *)
    destruct push as [stp|]; [exfalso; destruct GP as (ES2 & _); rewrite ES2 in Ks; revert Ks CEILB; clear; unfold wz; rewrite ?unsigned_lit by lia; intros Ks CEILB; lia|].
    destruct GP as (_ & PCR & YL).
    apply evtA_done. intros mo1 Hag1 HLI1 Hh1. destruct (BACK mo1 Hag1 HLI1) as [AHK1 R01].
    pose proof (pmem_remodel E m mo mo1 s [] h1 mh cx obw olw cr PM AHK1 (RRT _ _ _ _ _ _ R1 R01)) as PM1.
    pose proof (J_back Y KIPY BLKY BSHY LAYY RRT E F fc m mo1 s [] h0 cx0 h1 mh cx obw olw cr) as JB. unfold pstate, J_BACK, wz in JB.
    eapply JB; [exact PA| exact OK| exact PM1| exact PCR| exact FRM| exact YL| exact SZM'| apply plk_ok_nil| exact AG].
  - (* [comment removed for export] *)
    destruct push as [stp|]; [| exfalso; destruct GP as (NS2 & _); apply NS2; revert Ks CEILB; clear; pose proof (bv_unsigned_in_range 64 s2v); unfold bv_modulus in *; cbn in *; intros Ks CEILB; lia].
    destruct GP as (ES2 & ES5 & PCRr & PHI2 & YGG). subst s5v. unfold wz.
    apply evtA_done. intros mo1 Hag1 HLI1 Hh1. destruct (BACK mo1 Hag1 HLI1) as [AHK1 R01].
    pose proof (pmem_remodel E m mo mo1 s [] h1 mh cx obw olw cr PM AHK1 (RRT _ _ _ _ _ _ R1 R01)) as PM1.
    pose proof (push_tail E F fc m mo1 s h0 cx0 h1 mh cx obw olw cr stp) as PT. unfold pstate, PUSH_AT, wz in PT.
    eapply PT; [exact PA| exact OK| exact PM1| exact FRM| exact U1| exact SZM'| exact SZB| exact PCRr| exact PHI2| exact YGG| exact AG| exact EX].
Qed.

(* [comment removed for export] *)
Lemma gv_rst : forall (E : apE Y) (F : bvmap 5 word) (fc : bv 32) m mo s h0 cx0 h1 mh cx obw olw cr push
    (rav t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2v s5v t3 t4 t5 t6 : word),
  penvA E -> pok E h0 cx0 -> pmem E m mo s [] h1 mh cx obw olw cr -> frm0 fc -> 0 < h_used h1 ->
  h_stack_size h1 mod 8 = 0 -> h_stack_size h1 <= pLEN E + 1 + YAJL_BS_INC ->
  gv_push E h0 cx0 h1 cx cr s2v s5v push -> pagain Y E h0 cx0 [] ->
  pexit_cont E (fun r => let '(st, h', cx') := r in yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) h0 cx0) (SR_done st h' cx')) ->
  realizes_cfg acfg asegs (mkCfg (pstate E GV_RST F fc m rav t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2v (wz (pH E + 64)) s5v t3 t4 t5 t6) mo) (p_K E).
Proof. aceil.
  intros until t6. intros PA OK PM FRM U1 SZM' SZB GP AG EX.
  pose proof PM as (AY & _ & _ & _ & _ & (k0 & k224 & FR) & _ & _ & _ & _ & _ & MI & _ & _ & _ & [_ R1] & _). apply AYST_split in AY. destruct AY as [AHK _].
  unfold pframe, wz in FR. openPA PA.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  unfold pstate, GV_RST, wz. arz_seg KIPY AHK.
  pose proof (aypol_stack Y _ _ _ _ LINK (p_lo E) (pSP E) ltac:(clear -CEILB pa_ceil0; aceil; lia) ltac:(clear -CEILB pa_sp0; lia)) as PSTK.
  unfold pol in PSTK. pose proof (ppol_mark E mh) as PPM. clear LINK.
  zstepA.                                                  (* [comment removed for export] *)
  zstepA. if_cases Ks; zify_cond Ks.                       (* [comment removed for export] *)
  - (* [comment removed for export] *)
    destruct push as [stp|]; [| exfalso; destruct GP as (NS2 & _); apply NS2; revert Ks CEILB; clear; unfold wz; rewrite ?unsigned_lit by lia; intros Ks CEILB; first [exact Ks | lia]].
    destruct GP as (ES2 & ES5 & PCRr & PHI2 & YGG). subst s5v. unfold wz.
    apply evtA_done. intros mo1 Hag1 HLI1 Hh1. destruct (BACK mo1 Hag1 HLI1) as [AHK1 R01].
    pose proof (pmem_remodel E m mo mo1 s [] h1 mh cx obw olw cr PM AHK1 (RRT _ _ _ _ _ _ R1 R01)) as PM1.
    pose proof (push_tail E F fc m mo1 s h0 cx0 h1 mh cx obw olw cr stp) as PT. unfold pstate, PUSH_AT, wz in PT.
    eapply PT; [exact PA| exact OK| exact PM1| exact FRM| exact U1| exact SZM'| exact SZB| exact PCRr| exact PHI2| exact YGG| exact AG| exact EX].
  - (* [comment removed for export] *)
    destruct push as [stp|]; [exfalso; destruct GP as (ES2 & _); rewrite ES2 in Ks; revert Ks CEILB; clear; unfold wz; rewrite ?unsigned_lit by lia; intros Ks CEILB; lia|].
    destruct GP as (_ & PCR & YL).
    zstepA.                                                (* [comment removed for export] *)
    apply evtA_done. intros mo1 Hag1 HLI1 Hh1. destruct (BACK mo1 Hag1 HLI1) as [AHK1 R01].
    pose proof (pmem_remodel E m mo mo1 s [] h1 mh cx obw olw cr PM AHK1 (RRT _ _ _ _ _ _ R1 R01)) as PM1.
    pose proof (J_back Y KIPY BLKY BSHY LAYY RRT E F fc m mo1 s [] h0 cx0 h1 mh cx obw olw cr) as JB. unfold pstate, J_BACK, wz in JB.
    eapply JB; [exact PA| exact OK| exact PM1| exact PCR| exact FRM| exact YL| exact SZM'| apply plk_ok_nil| exact AG].
Qed.
Definition val_state (st : ystate) : bool :=
  match st with ST_start | ST_map_need_val | ST_array_start | ST_array_need_val => true | _ => false end.

Definition gv_handle (h : yhandle) (st : ystate) (rest : list ystate) : yhandle :=
  match st with
  | ST_start => h_set_lexer h (lex_reset (h_lexer h))
  | ST_map_need_val => h_set_stack h (ST_map_got_val :: rest)
  | _ => h_set_stack h (ST_array_got_val :: rest)
  end.

(* [comment removed for export] *)
Lemma J_gotval : forall (E : apE Y) (F : bvmap 5 word) (fc : bv 32) m mo s h0 cx0 h mh cx obw olw cr st rest push
    (rav t0 t1 a0 a1 a2 a3 a4 a5 a6 a7 s2v s5v t3 t4 t5 t6 : word),
  penvA E -> pok E h0 cx0 -> pmem E m mo s [] h mh cx obw olw cr -> frm0 fc ->
  h_stack h = st :: rest -> val_state st = true -> h_stack_size h mod 8 = 0 -> lex_inv (h_lexer h) -> h_stack_size h <= pLEN E + 1 + YAJL_BS_INC ->
  gv_push E h0 cx0 (gv_handle h st rest) cx cr s2v s5v push -> pagain Y E h0 cx0 [] ->
  pexit_cont E (fun r => let '(st, h', cx') := r in yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) h0 cx0) (SR_done st h' cx')) ->
  realizes_cfg acfg asegs (mkCfg (pstate E J_GV F fc m rav t0 t1 (wz (pH E + 48)) a0 a1 a2 a3 a4 a5 a6 a7 s2v (wz (pH E + 64)) s5v t3 t4 t5 t6) mo) (p_K E).
Proof. aceil.
  intros until t6. intros PA OK PM FRM HST VS SZM' LXI SZB GP AG EX.
  popen OK PM; yhide TB; yhide OTB; yhide LP; yhide FFR0.
  assert (USED : h_used h = zlength rest + 1) by (unfold h_used; rewrite HST; unfold zlength; cbn [length]; lia).
  assert (Z0 : 0 <= zlength rest) by (unfold zlength; clear; lia).
  pose proof (proj2 BC3) as US. assert (U1 : 0 < h_used h) by (clear -CEILB USED Z0; lia). assert (SZ : 0 < h_stack_size h) by (clear -CEILB USED Z0 US; lia).
  pose proof (mk_pblk BLKY LAYY BSHY E s [] h mh h0 cx0 m mo PA OK AHK SAME SB1 SZ) as PB.
  pose proof (pb_HSB _ _ _ PB) as SEPHS; pose proof (pb_SB _ _ _ PB) as RSB; pose proof (pb_SBA PB) as RSBA; pose proof (pb_L _ _ _ PB) as RL; pose proof (pb_LB _ _ _ PB) as RLB.
  pose proof (pb_HL _ _ _ PB) as SEPHL; pose proof (pb_HLB _ _ _ PB) as SEPHLB; pose proof (pb_LSB _ _ _ PB) as SEPLSB; pose proof (pb_LBSB _ _ _ PB) as SEPLBSB.
  pose proof (pl_LLB _ _ _ _ _ (mk_plex BLKY E s [] h mh h0 cx0 m mo PA OK AHK SAME SB1)) as SEPLLB.
  openPA PA; clear pa_ffCX0 pa_ffH0 pa_Tsep0 pa_OT0 pa_j0 pa_CXH0.
  pose proof SAME as (EH & EL & ELB & EDB & ECX).
  assert (IN : forall b, In b (abl (yblocks mh h)) -> In b (abl (yblocks mh h) ++ [] ++ p_REST E)) by (intros b Hb; apply in_or_app; left; exact Hb).
  pose proof (proj1 (BSHY _ _ _ _ _ _ AHK (IN _ (yb_in_hand mh h)) ltac:(cbn; unfold SIZEOF_HANDLE; lia))) as OSH_H; cbn [ab_addr ab_size] in OSH_H.
  assert (OHH : oshw_hi 0 (2^47) <= mh_addr mh) by (revert pa_H0 EH; clear; unfold oshw_hi, A_SB; cbn; intros; lia).
  pose proof (BSHY _ _ _ _ _ _ AHK (IN _ (yb_in_stack mh h SB1)) ltac:(cbn; lia)) as [OSH_S _]; cbn [ab_addr ab_size] in OSH_S.
  pose proof (proj1 (BSHY _ _ _ _ _ _ AHK (IN _ (yb_in_lexer mh h)) ltac:(cbn; unfold SIZEOF_LEXER; lia))) as OSH_L; cbn [ab_addr ab_size] in OSH_L.
  assert (OHL : oshw_hi 0 (2^47) <= mh_lexer mh) by (revert RL; clear; unfold oshw_hi, A_SB; cbn; intros; lia).
  pose proof (proj1 (BSHY _ _ _ _ _ _ AHK (IN _ (yb_in_lexbuf mh h)) ltac:(cbn; unfold SIZEOF_BUF; lia))) as OSH_LB; cbn [ab_addr ab_size] in OSH_LB.
  assert (OHLB : oshw_hi 0 (2^47) <= mb_addr (mh_lexbuf mh)) by (revert RLB; clear; unfold oshw_hi, A_SB; cbn; intros; lia).
  pose proof OSH_H as OSH_H'. pose proof OSH_S as OSH_S'. unfold oshadow, A_SB, SIZEOF_HANDLE in OSH_H', OSH_S'.
  destruct OSH_H' as (_ & _ & SHH); destruct OSH_S' as (_ & _ & SHS); rewrite EH in SHH.
  remember (blk_shadow 104) as shb eqn:SHHeq in SHH; remember (blk_shadow (h_stack_size h)) as shs eqn:SHSeq in SHS.
  pose proof YS as (_ & _ & _ & STA).
  unfold hand_cells, hand_head_cells, alloc_cells in HC; cbn [yc_callbacks yc_malloc_w yc_realloc_w yc_free_w ayc app] in HC; unfold wz in HC; rewrite EH in HC.
  clear TXT DBR FF OCX GAP PRES UA CRED HR; yhide SV. unfold wz in FR.
  pose proof BSR as BSR'. unfold RYajlRep.bs_rep in BSR'. destruct (h_stack_blk h) as [sbk|] eqn:HSB in BSR'; [| exfalso; exact (SB1 HSB)].
  destruct BSR' as (SBNZ & junk & SC).
  destruct (u8arr_of_CB2 _ _ _ _ _ _ _ SC) as (ARR & L1 & L2). clear SC.
  pose proof ARR as ARR0. rewrite HST in ARR0.
  pose proof (u8arr_read asegs m (mh_stack mh) _ (zlength rest) (Z_to_bv 8 (state_code st)) _ ARR0 ltac:(apply stack_top_byte) ltac:(clear -CEILB Z0; lia) eq_refl) as RK. clear ARR0.
  assert (LEN : length (zbytes (stack_bytes (h_stack h)) ++ junk) = Z.to_nat (h_stack_size h)) by (rewrite length_app; clear -CEILB L1 L2 US U1; lia).
  pose proof (state_code_range st) as CR.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (USQ : bv_unsigned (Z_to_bv 64 (p_SQ E)) = p_SQ E) by (apply unsigned_lit; clear -CEILB pa_SQ0 pa_lo0 pa_ceil0 pa_sp0; lia).
  yhide LXR. yhide OSH_L. yhide OSH_LB. yhide OSH_H. yhide OHL. yhide OHLB. yhide OHH. yhide SEPLLB. yhide SEPHL. yhide SEPHLB.
  unfold pstate, J_GV, wz.
  arz_seg KIPY AHK.
  pose proof (mk_ppol BLKY LAYY BSHY E s [] h mh h0 cx0 m mo _ _ PA OK AHK SAME SB1 SZ LINK) as PP. openPP PP. pose proof (ppol_mark E mh) as PPM.
  destruct (aypol_opol_block Y _ _ _ _ LINK (mkABlock (mb_addr (mh_lexbuf mh)) SIZEOF_BUF) (IN _ (yb_in_lexbuf mh h))
              ltac:(cbn; clear -CEILB RLB; lia) ltac:(cbn; unfold oshw_lo, A_SB; clear -CEILB RLB; lia)
              ltac:(cbn; unfold oshw_hi, A_SB, amem, SIZEOF_BUF; clear -CEILB RLB; Z.div_mod_to_equations; lia) ltac:(cbn; unfold SIZEOF_BUF; clear -CEILB RLB; aceil; lia)) as [PLB PLBs].
  cbn [ab_addr ab_size] in PLB, PLBs. yhide PLB. yhide PLBs.
  unfold pol, AY_IMG_LO, AY_IMG_HI in pp_stk0, pp_H0, pp_Hs0, pp_SBs0, pp_SB0, pp_img0, pp_L0, pp_Ls0. clear pp_imgsh0 pp_DB0 pp_DBs0 pp_CX0 pp_CXs0 pp_ff0 pp_ffs0 pp_T0 pp_Ts0 LINK.
  yhide pp_L0. yhide pp_Ls0.
  shH SHH SHHeq MU WM 60 4.                                (* [comment removed for export] *)
  zstepA. iflit2.                                          (* [comment removed for export] *)
  zstepA. rewrite ?ysx32_small by (clear -CEILB BC3 BC2; lia).   (* [comment removed for export] *)
  zstepA. if_cases KU; zify_cond KU; bkill KU BC2 BC3 US USED Z0.   (* [comment removed for export] *)
  shH SHH SHHeq MU WM 48 8.                                (* [comment removed for export] *)
  zstepA. iflit2.                                          (* [comment removed for export] *)
  zstepA.                                                  (* [comment removed for export] *)
  zstepA. zstepA. zstepA. rewrite land_M32_small by (clear -CEILB USED Z0 US BC2; lia).   (* [comment removed for export] *)
  zstepA.                                                  (* [comment removed for export] *)
  shS SHS SHSeq MU WM (h_used h + -1) (h_stack_size h).    (* [comment removed for export] *)
  zstepA. iflit2.                                          (* [comment removed for export] *)
  replace (mh_stack mh + (h_used h + -1)) with (mh_stack mh + zlength rest) by (clear -CEILB USED; lia).
  change (wa (mh_stack mh + zlength rest)) with (Z_to_bv 64 (mh_stack mh + zlength rest)) in RK.
  zstepA. clear RK. cbv beta. rewrite (u8_val (state_code st)) by (clear -CEILB CR; lia).   (* [comment removed for export] *)
  zstepA.                                                  (* [comment removed for export] *)
  destruct st; try discriminate VS; cbn [state_code Z.eqb Pos.eqb] in GP |- *.
  - (* [comment removed for export] *)
    zstepA. iflit2.                                        (* [comment removed for export] *)
    zstepA. iflit2.                                        (* [comment removed for export] *)
    zstepA.                                                (* [comment removed for export] *)
    zstepA.                                                (* [comment removed for export] *)
    clear MU. pose proof (munch_refl [(p_lo E, bv_unsigned (Z_to_bv 64 (p_SQ E))); (mh_addr mh + 16, mh_addr mh + 24); (mh_lexer mh, mh_lexer mh + 48); (mb_addr (mh_lexbuf mh), mb_addr (mh_lexbuf mh) + 32)] m) as MU.
    yshow LXR. yshow OSH_L. yshow OSH_LB. yshow OSH_H. yhide SEPHS. yhide SEPLSB. yhide SEPLBSB. clear ARR SHS.
    pose proof LXI as (_ & _ & _ & _ & _ & _ & LBZ).
    lazymatch goal with |- evtA _ ?P _ _ => pose proof (YRP P h mh (p_lo E)) as CB end. unfold ayreset_parser_rpost in CB.
    try clear HC. try clear SHH. call_spA CB; rewrite ?USQ.
    + exact STA.
    + exact HS.
    + exact LXR.
    + rewrite LBZ. reflexivity.
    + rewrite LBZ. apply buf_inv_zero.
    + rewrite LBZ. reflexivity.
    + clear -CEILB pa_H0 EH; lia.
    + clear -CEILB RL; lia.
    + clear -CEILB RLB; lia.
    + exact OSH_H.
    + exact OSH_L.
    + exact OSH_LB.
    + yshow OHH; exact OHH.
    + unfold SIZEOF_HANDLE; aceil; clear -CEILB pa_H0 EH; lia.
    + yshow OHL; exact OHL.
    + unfold SIZEOF_LEXER; aceil; clear -CEILB RL; lia.
    + yshow OHLB; exact OHLB.
    + unfold SIZEOF_BUF; aceil; clear -CEILB RLB; lia.
    + yshow SEPLLB. unfold SIZEOF_LEXER, SIZEOF_BUF. clear -CEILB SEPLLB. lia.
    + yshow SEPHL. unfold SIZEOF_HANDLE, SIZEOF_LEXER. rewrite EH. clear -CEILB SEPHL. lia.
    + yshow SEPHLB. unfold SIZEOF_HANDLE, SIZEOF_BUF. rewrite EH. clear -CEILB SEPHLB. lia.
    + exact MI.
    + exact STK.
    + clear -CEILB pa_ceil0; aceil; lia.
    + unfold AY_RESET_STACK, AY_LEX_REALLOC_STACK, AY_BUF_SMALL_STACK. clear -CEILB pa_SQ0 pa_lo0; lia.
    + clear -CEILB pa_SQ0 pa_sp0; lia.
    + rewrite EH; reflexivity.
    + intros a k Ha Hk. apply pp_stk0; [exact Ha|]. clear -CEILB Hk pa_SQ0; lia.
    + intros a k Ha Hk. apply pp_img0; [exact Ha| exact Hk].
    + unfold opol, oshw_lo, oshw_hi, A_SB, amem, SIZEOF_HANDLE; rewrite EH; split; intros a k Ha Hk; [apply pp_H0| apply pp_Hs0]; first [exact Ha| exact Hk| revert Hk; clear; cbn; intros; lia].
    + yshow pp_L0. yshow pp_Ls0. unfold opol, oshw_lo, oshw_hi, A_SB, amem, SIZEOF_LEXER; split; intros a k Ha Hk; [apply pp_L0| apply pp_Ls0]; first [exact Ha| exact Hk| revert Hk; clear; cbn; intros; lia].
    + yshow PLB. yshow PLBs. unfold opol, oshw_lo, oshw_hi, A_SB, amem. split; [exact PLB| exact PLBs].
    + (* [comment removed for export] *)
      lazymatch goal with H : stk asegs ?mx (p_lo E) _ |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename H into ST2; rewrite ?USQ in ST2 end.
      lazymatch goal with H : ahand_struct ?mx h mh |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename H into HS2 end.
      lazymatch goal with H : alexer_rep ?mx _ (lex_reset _) _ _ |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename H into LXR2 end.
      lazymatch goal with H : mem_inv asegs ?mx |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename H into MI2 end.
      apply evtA_done. intros mo1 Hag1 HLI1 Hh1. destruct (BACK mo1 Hag1 HLI1) as [AHK1 R01].
      lazymatch goal with |- realizes_cfg _ _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ => rename mx into m2 end.
      pose proof (pmem_remodel E m mo mo1 s [] h mh cx obw olw cr PM AHK1 (RRT _ _ _ _ _ _ R1 R01)) as PM1.
      rewrite USQ in MU. yshow TB. yshow OTB. yshow LP. yshow FFR0. yshow SV.
      assert (PM2 : pmem E m2 mo1 s [] (h_set_lexer h (lex_reset (h_lexer h))) mh cx obw olw cr).
      { eapply (pmem_updL BLKY LAYY BSHY FRAMEY UFRAME E m m2 mo1 s [] h mh cx obw olw cr _ h0 cx0);
          [exact PA| exact OK| exact PM1| exact SZ| exact MU| exact WM| exact MI2| | | | exact HS2| exact LXR2| exact ST2].
        - constructor; [| constructor; [| constructor; [| constructor; [| constructor]]]]; unfold ownL; cbn [fst snd];
            [left; clear; lia| right; left; clear; lia| right; right; left; clear; lia| right; right; right; clear; lia].
        - reflexivity.
        - reflexivity. }
      pose proof (gv_rst E F fc m2 mo1 s h0 cx0 (h_set_lexer h (lex_reset (h_lexer h))) mh cx obw olw cr push) as GR. unfold pstate, GV_RST, wz in GR.
      eapply GR; [exact PA| exact OK| exact PM2| exact FRM| exact U1| exact SZM'| exact SZB| exact GP| exact AG| exact EX].
  - (* [comment removed for export] *)
    zstepA. iflit2.                                        (* [comment removed for export] *)
    clear MU. pose proof (munch_refl [(mh_stack mh + (h_used h - 1), mh_stack mh + (h_used h - 1) + 1)] m) as MU.
    shH SHH SHHeq MU WM 60 4.                              (* [comment removed for export] *)
    zstepA. iflit2.                                        (* [comment removed for export] *)
    zstepA. rewrite ?ysx32_small by (clear -CEILB BC3 BC2; lia). (* [comment removed for export] *)
    zstepA. if_cases KU2; zify_cond KU2; bkill KU2 BC2 BC3 US USED Z0.   (* [comment removed for export] *)
    zstepA.                                                (* [comment removed for export] *)
    shH SHH SHHeq MU WM 56 4.                              (* [comment removed for export] *)
    zstepA. iflit2.                                        (* [comment removed for export] *)
    zstepA.                                                (* [comment removed for export] *)
    zstepA. rewrite ?ysx32_small by (clear -CEILB BC2; lia).     (* [comment removed for export] *)
    zstepA. if_cases KS2; zify_cond KS2; bkill KS2 BC2 BC3 US USED Z0.   (* [comment removed for export] *)
    zstepA. zstepA. zstepA. rewrite land_M32_small by (clear -CEILB USED Z0 US BC2; lia).   (* [comment removed for export] *)
    zstepA.                                                (* [comment removed for export] *)
    shS SHS SHSeq MU WM (h_used h + -1) (h_stack_size h).  (* [comment removed for export] *)
    zstepA. iflit2.                                        (* [comment removed for export] *)
    zstepA. zstepA.                                        (* [comment removed for export] *)
    lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
      pose proof (u8arr_store_ok_at asegs mx (mh_stack mh) _ (h_used h + -1) ARR ltac:(rewrite LEN; clear -CEILB US USED Z0; lia)) as SOK end.
    stepA.                                                 (* [comment removed for export] *)
    lazymatch type of ARR with u8arr _ ?mx _ _ =>
      pose proof (u8arr_write asegs mx (mh_stack mh) _ (h_used h + -1) (Z_to_bv 8 7) ARR ltac:(rewrite LEN; clear -CEILB US USED Z0; lia)) as ARR' end.
    rewrite le1_wz by (clear; lia). clear ARR. yhide SHS. yhide SHH. store_done.
    apply evtA_done. intros mo1 Hag1 HLI1 Hh1. destruct (BACK mo1 Hag1 HLI1) as [AHK1 R01].
    lazymatch goal with |- realizes_cfg _ _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ => rename mx into m2 end.
    pose proof (pmem_remodel E m mo mo1 s [] h mh cx obw olw cr PM AHK1 (RRT _ _ _ _ _ _ R1 R01)) as PM1.
    assert (PM2 : pmem E m2 mo1 s [] (h_set_stack h (ST_map_got_val :: rest)) mh cx obw olw cr).
    { eapply (pmem_setb Y FRAMEY BLKY BSHY LAYY UFRAME E m m2 mo1 s [] h0 cx0 h mh cx obw olw cr ST_map_need_val rest ST_map_got_val junk);
        [exact PA| exact OK| exact PM1| exact HST| exact SZ| exact MU| exact WM| assumption| | clear -CEILB L2; lia].
      replace (h_used h - 1) with (h_used h + -1) by (clear; lia). cbn [state_code]. exact ARR'. }
    pose proof (gv_fin E F fc m2 mo1 s h0 cx0 (h_set_stack h (ST_map_got_val :: rest)) mh cx obw olw cr push) as GF. unfold pstate, GV_FIN, wz in GF.
    eapply GF; [exact PA| exact OK| exact PM2| exact FRM| unfold h_used; cbn [h_stack h_set_stack]; unfold zlength; cbn [length]; clear; lia| exact SZM'| exact SZB| exact GP| exact AG| exact EX].
  - (* [comment removed for export] *)
    zstepA. iflit2.                                        (* [comment removed for export] *)
    zstepA. iflit2.                                        (* [comment removed for export] *)
    clear MU. pose proof (munch_refl [(mh_stack mh + (h_used h - 1), mh_stack mh + (h_used h - 1) + 1)] m) as MU.
    shH SHH SHHeq MU WM 60 4.                              (* [comment removed for export] *)
    zstepA. iflit2.                                        (* [comment removed for export] *)
    zstepA. rewrite ?ysx32_small by (clear -CEILB BC3 BC2; lia). (* [comment removed for export] *)
    zstepA. if_cases KU2; zify_cond KU2; bkill KU2 BC2 BC3 US USED Z0.   (* [comment removed for export] *)
    zstepA.                                                (* [comment removed for export] *)
    shH SHH SHHeq MU WM 56 4.                              (* [comment removed for export] *)
    zstepA. iflit2.                                        (* [comment removed for export] *)
    zstepA.                                                (* [comment removed for export] *)
    zstepA. rewrite ?ysx32_small by (clear -CEILB BC2; lia).     (* [comment removed for export] *)
    zstepA. if_cases KS2; zify_cond KS2; bkill KS2 BC2 BC3 US USED Z0.   (* [comment removed for export] *)
    zstepA. zstepA. zstepA. rewrite land_M32_small by (clear -CEILB USED Z0 US BC2; lia).   (* [comment removed for export] *)
    zstepA.                                                (* [comment removed for export] *)
    shS SHS SHSeq MU WM (h_used h + -1) (h_stack_size h).  (* [comment removed for export] *)
    zstepA. iflit2.                                        (* [comment removed for export] *)
    zstepA.                                                (* [comment removed for export] *)
    lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
      pose proof (u8arr_store_ok_at asegs mx (mh_stack mh) _ (h_used h + -1) ARR ltac:(rewrite LEN; clear -CEILB US USED Z0; lia)) as SOK end.
    stepA.                                                 (* [comment removed for export] *)
    lazymatch type of ARR with u8arr _ ?mx _ _ =>
      pose proof (u8arr_write asegs mx (mh_stack mh) _ (h_used h + -1) (Z_to_bv 8 10) ARR ltac:(rewrite LEN; clear -CEILB US USED Z0; lia)) as ARR' end.
    rewrite le1_wz by (clear; lia). clear ARR. yhide SHS. yhide SHH. store_done.
    apply evtA_done. intros mo1 Hag1 HLI1 Hh1. destruct (BACK mo1 Hag1 HLI1) as [AHK1 R01].
    lazymatch goal with |- realizes_cfg _ _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ => rename mx into m2 end.
    pose proof (pmem_remodel E m mo mo1 s [] h mh cx obw olw cr PM AHK1 (RRT _ _ _ _ _ _ R1 R01)) as PM1.
    assert (PM2 : pmem E m2 mo1 s [] (h_set_stack h (ST_array_got_val :: rest)) mh cx obw olw cr).
    { eapply (pmem_setb Y FRAMEY BLKY BSHY LAYY UFRAME E m m2 mo1 s [] h0 cx0 h mh cx obw olw cr ST_array_start rest ST_array_got_val junk);
        [exact PA| exact OK| exact PM1| exact HST| exact SZ| exact MU| exact WM| assumption| | clear -CEILB L2; lia].
      replace (h_used h - 1) with (h_used h + -1) by (clear; lia). cbn [state_code]. exact ARR'. }
    pose proof (gv_fin E F fc m2 mo1 s h0 cx0 (h_set_stack h (ST_array_got_val :: rest)) mh cx obw olw cr push) as GF. unfold pstate, GV_FIN, wz in GF.
    eapply GF; [exact PA| exact OK| exact PM2| exact FRM| unfold h_used; cbn [h_stack h_set_stack]; unfold zlength; cbn [length]; clear; lia| exact SZM'| exact SZB| exact GP| exact AG| exact EX].
  - (* [comment removed for export] *)
    zstepA. iflit2.                                        (* [comment removed for export] *)
    zstepA. iflit2.                                        (* [comment removed for export] *)
    clear MU. pose proof (munch_refl [(mh_stack mh + (h_used h - 1), mh_stack mh + (h_used h - 1) + 1)] m) as MU.
    shH SHH SHHeq MU WM 60 4.                              (* [comment removed for export] *)
    zstepA. iflit2.                                        (* [comment removed for export] *)
    zstepA. rewrite ?ysx32_small by (clear -CEILB BC3 BC2; lia). (* [comment removed for export] *)
    zstepA. if_cases KU2; zify_cond KU2; bkill KU2 BC2 BC3 US USED Z0.   (* [comment removed for export] *)
    zstepA.                                                (* [comment removed for export] *)
    shH SHH SHHeq MU WM 56 4.                              (* [comment removed for export] *)
    zstepA. iflit2.                                        (* [comment removed for export] *)
    zstepA.                                                (* [comment removed for export] *)
    zstepA. rewrite ?ysx32_small by (clear -CEILB BC2; lia).     (* [comment removed for export] *)
    zstepA. if_cases KS2; zify_cond KS2; bkill KS2 BC2 BC3 US USED Z0.   (* [comment removed for export] *)
    zstepA. zstepA. zstepA. rewrite land_M32_small by (clear -CEILB USED Z0 US BC2; lia).   (* [comment removed for export] *)
    zstepA.                                                (* [comment removed for export] *)
    shS SHS SHSeq MU WM (h_used h + -1) (h_stack_size h).  (* [comment removed for export] *)
    zstepA. iflit2.                                        (* [comment removed for export] *)
    zstepA.                                                (* [comment removed for export] *)
    lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
      pose proof (u8arr_store_ok_at asegs mx (mh_stack mh) _ (h_used h + -1) ARR ltac:(rewrite LEN; clear -CEILB US USED Z0; lia)) as SOK end.
    stepA.                                                 (* [comment removed for export] *)
    lazymatch type of ARR with u8arr _ ?mx _ _ =>
      pose proof (u8arr_write asegs mx (mh_stack mh) _ (h_used h + -1) (Z_to_bv 8 10) ARR ltac:(rewrite LEN; clear -CEILB US USED Z0; lia)) as ARR' end.
    rewrite le1_wz by (clear; lia). clear ARR. try clear SHS. try clear SHH. store_done.
    apply evtA_done. intros mo1 Hag1 HLI1 Hh1. destruct (BACK mo1 Hag1 HLI1) as [AHK1 R01].
    lazymatch goal with |- realizes_cfg _ _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ => rename mx into m2 end.
    pose proof (pmem_remodel E m mo mo1 s [] h mh cx obw olw cr PM AHK1 (RRT _ _ _ _ _ _ R1 R01)) as PM1.
    assert (PM2 : pmem E m2 mo1 s [] (h_set_stack h (ST_array_got_val :: rest)) mh cx obw olw cr).
    { eapply (pmem_setb Y FRAMEY BLKY BSHY LAYY UFRAME E m m2 mo1 s [] h0 cx0 h mh cx obw olw cr ST_array_need_val rest ST_array_got_val junk);
        [exact PA| exact OK| exact PM1| exact HST| exact SZ| exact MU| exact WM| assumption| | clear -CEILB L2; lia].
      replace (h_used h - 1) with (h_used h + -1) by (clear; lia). cbn [state_code]. exact ARR'. }
    pose proof (gv_fin E F fc m2 mo1 s h0 cx0 (h_set_stack h (ST_array_got_val :: rest)) mh cx obw olw cr push) as GF. unfold pstate, GV_FIN, wz in GF.
    eapply GF; [exact PA| exact OK| exact PM2| exact FRM| unfold h_used; cbn [h_stack h_set_stack]; unfold zlength; cbn [length]; clear; lia| exact SZM'| exact SZB| exact GP| exact AG| exact EX].
Qed.
End W.
End RC__1.
