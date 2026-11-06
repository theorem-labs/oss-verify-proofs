(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import B_iface BYajlRep BYajl_iface BY_rz BY_hand BY_acct_needs BY_parse_kit BY_parse_pol BY_parse_head BY_parse_epi BY_parse_epi2 BY_parse_tails BY_parse_tails2 BY_parse_sep BY_parse_agv BY_parse_gv.
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
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac lia1 := LiaTuning.zify_prune; LiaTuning.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker.
Local Ltac solve_cond_base1 :=
  first [ reflexivity
        | apply Z.ltb_lt; lia1 | apply Z.ltb_ge; lia1
        | apply Z.leb_le; lia1 | apply Z.leb_gt; lia1
        | apply Z.eqb_eq; lia1 | apply Z.eqb_neq; lia1 ].
Local Ltac solve_cond_rec1 :=
  lazymatch goal with
  | |- negb _ = true => apply (proj2 (Bool.negb_true_iff _)); solve_cond_rec1
  | |- negb _ = false => apply (proj2 (Bool.negb_false_iff _)); solve_cond_rec1
  | _ => solve_cond_base1
  end.
Local Ltac solve_cond1 := unfold_cond; fold_lit_ux; solve_cond_rec1.
Local Ltac if_true1 := let c := goal_cond in replace c with true; [cbv iota| symmetry; solve_cond1].
Local Ltac if_false1 := let c := goal_cond in replace c with false; [cbv iota| symmetry; solve_cond1].
(* [comment removed for export] *)
Local Ltac if_litc1 := let c := goal_cond in let v := eval vm_compute in c in
  lazymatch v with true => change c with true | false => change c with false end; cbv iota.
(* [comment removed for export] *)
Local Ltac iflit2 := first [if_litc1 | if_true1 | if_false1 | if_true | if_false].
(* [comment removed for export] *)
Lemma zext32_shl_shr : forall x, 0 <= x < 4294967296 ->
  Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl x 32))) 32) = Z_to_bv 64 x.
Proof.
  intros x Hx. f_equal. rewrite unsigned_lit_wrap. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  rewrite Z.mod_small by lia. rewrite Z.div_mul by lia. reflexivity.
Qed.
(* [comment removed for export] *)
Local Ltac shH SHH SHHeq MU WM k w ::=
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    lazymatch type of SHH with u8arr _ ?m0 (2147450880 + ?H / 8) ?shb =>
      let R := fresh "SHR" in
      assert (R : ov_read_bytes bsegs mx (Z_to_bv 64 ((H + k) / 8 + 2147450880)) 1 = Some [Z_to_bv 8 0]);
      [ replace ((H + k) / 8 + 2147450880) with (2147450880 + (H + k) / 8) by qlia0;
        apply (block_shadow_read0_u bsegs mx 2147450880 H 104 (H + k) w);
        [ qliaH | qlia0 | rewrite <- SHHeq; first [exact SHH | eapply (u8arr_transport bsegs); [exact SHH| exact MU| exact WM| rewrite SHHeq, (blk_shadow_length 104) by qlia0; cbn [disjoint_from fst snd]; qlia_sep]]
        | qlia0 | qlia0 | qlia0 | qliaH ]
      | zstepA; clear R; rewrite ?zxb_small, ?sxb_small by qlia0 ]
    end end.
Local Ltac shH0 SHH SHHeq MU WM w ::=
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    lazymatch type of SHH with u8arr _ ?m0 (2147450880 + ?H / 8) ?shb =>
      let R := fresh "SHR" in
      assert (R : ov_read_bytes bsegs mx (Z_to_bv 64 (H / 8 + 2147450880)) 1 = Some [Z_to_bv 8 0]);
      [ replace (H / 8 + 2147450880) with (2147450880 + H / 8) by qlia0;
        apply (block_shadow_read0_u bsegs mx 2147450880 H 104 H w);
        [ qliaH | qlia0 | rewrite <- SHHeq; first [exact SHH | eapply (u8arr_transport bsegs); [exact SHH| exact MU| exact WM| rewrite SHHeq, (blk_shadow_length 104) by qlia0; cbn [disjoint_from fst snd]; qlia_sep]]
        | qlia0 | qlia0 | qlia0 | qliaH ]
      | zstepA; clear R; rewrite ?zxb_small, ?sxb_small by qlia0 ]
    end end.
Local Ltac qliaB := first [solve [keep_bsg; Z.div_mod_to_equations; lia] | Z.div_mod_to_equations; lia].
Local Ltac shS SHS SHSeq MU WM i size ::=
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    lazymatch type of SHS with u8arr _ ?m0 (2147450880 + ?B / 8) ?shb =>
      let R := fresh "SHR" in
      assert (R : ov_read_bytes bsegs mx (Z_to_bv 64 ((B + i) / 8 + 2147450880)) 1 = Some [Z_to_bv 8 0]);
      [ replace ((B + i) / 8 + 2147450880) with (2147450880 + (B + i) / 8) by qlia0;
        apply (block_shadow_read0_u bsegs mx 2147450880 B size (B + i) 1);
        [ qliaS | qliaB | rewrite <- SHSeq; first [exact SHS | eapply (u8arr_transport bsegs); [exact SHS| exact MU| exact WM| rewrite SHSeq, (blk_shadow_length size) by qliaB; cbn [disjoint_from fst snd]; qlia_sep]]
        | qliaB | qlia0 | qliaB | first [solve [clear; Z.div_mod_to_equations; lia] | qliaB] ]
      | zstepA; try shadow_addr; zstepA; zstepA; clear R; rewrite ?zxb_small, ?sxb_small by qlia0 ]
    end end.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition PUSH_GROW : Z := 0x8972c.   (* [comment removed for export] *)

Definition mh_set_stack (mh : mhand) (sb : Z) : mhand :=
  mkMH (mh_id mh) (mh_addr mh) (mh_lid mh) (mh_lexer mh) (mh_lexbuf mh) (mh_decbuf mh) (mh_sid mh) sb (mh_ctx mh).

Lemma abl_yblocks_split : forall mh h sid SZ,
  h_stack_blk h = Some sid ->
  abl (yblocks mh h) = abl (yblocks (mh_set_stack mh 0) (h_set_stack3 h (h_stack h) SZ None)) ++ [mkABlock (mh_stack mh) (h_stack_size h)].
Proof. aceil.
  intros mh h sid SZ HS. unfold yblocks, lexer_blocks, bs_blocks, abl.
  cbn [mh_set_stack mh_id mh_addr mh_lid mh_lexer mh_lexbuf mh_decbuf mh_sid mh_stack h_set_stack3 h_stack_blk h_lexer h_decbuf h_stack_size map app].
  rewrite HS. rewrite !map_app. cbn [map app MallocBlocks.blk_addr MallocBlocks.blk_size fst snd]. rewrite app_nil_r, <- !app_assoc. reflexivity.
Qed.
Lemma abl_yblocks_nostack : forall mh h SB SB' st st' SZ SZ',
  abl (yblocks (mh_set_stack mh SB) (h_set_stack3 h st SZ None)) = abl (yblocks (mh_set_stack mh SB') (h_set_stack3 h st' SZ' None)).
Proof. aceil. intros. reflexivity. Qed.

Lemma gnbig_app : forall l1 l2, nbig (l1 ++ l2) = nbig l1 + nbig l2.
Proof. aceil. intros. unfold nbig. rewrite List.filter_app, length_app. lia. Qed.
Lemma gnbig_le_len : forall l, nbig l <= Z.of_nat (length l).
Proof. aceil. intros l. unfold nbig. induction l as [|b l IH]; cbn; [lia|]. destruct (64512 <? ab_size b); cbn; lia. Qed.
Lemma gnbig_yblocks : forall mh h, nbig (abl (yblocks mh h)) <= 7.
Proof. aceil.
  intros mh h. eapply Z.le_trans; [apply gnbig_le_len|]. unfold yblocks, lexer_blocks, buf_blocks, bs_blocks, abl.
  rewrite !length_map.
  destruct (yb_data (lx_buf (h_lexer h))); destruct (yb_data (h_decbuf h)); destruct (h_stack_blk h); cbn -[Z.le]; lia.
Qed.

Lemma gland_M64 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551615 = x.
Proof. aceil. intros x Hx. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.

(* [comment removed for export] *)
End RC__1.
Ltac statics_via YS MU WM :=
  let X := fresh "YSX" in
  lazymatch goal with |- ay_statics ?mx =>
    enough (X : aystatics mx) by exact (proj2 (proj2 (proj2 X)));
    eapply aystatics_munch; [exact YS| exact MU| exact WM|]
  end.

Section RC__2.
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
    rw_cells bsegs m (bv_unsigned s0 - 16) [C8 s0'; C8 ra'] -> y_uanchor Y m (bv_unsigned s0) ra' s0' -> y_uanchor Y m SP ra s0.
Hypothesis URA_push : In PUSH_RET URA.

Let YH_shape : yphi_hand_shape_stmt Y := YH_shape Y phr YSPLIT.

(* [comment removed for export] *)
Lemma push_realloc : forall (E : apE Y) (F : bvmap 5 word) (fc : bv 32) m mo s h0 cx0 h mh cx obw olw cr stp
    (rav t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2v t3 t4 t5 t6 : word),
  penvA E -> pok E h0 cx0 -> pmem E m mo s [] h mh cx obw olw cr -> frm0 fc -> 0 < h_used h ->
  h_used h = h_stack_size h -> h_stack_size h mod 8 = 0 -> h_stack_size h <= pLEN E + 1 + YAJL_BS_INC ->
  (ypushc Y (h_stack_size h) + y_phi_hand Y (h_set_stack3 h (h_stack h) (h_stack_size h + YAJL_BS_INC) None) 0 <= cr /\
   forall p, y_phi_hand Y (h_set_stack3 h (stp :: h_stack h) (h_stack_size h + YAJL_BS_INC) (Some p)) (pLEN E) + ypushc Y (h_stack_size h) <= cr + y_arefund Y (h_stack_size h)) ->
  (forall r, yleaf (r0 <- ybs_push h stp ;; (let '(ok, h2) := r0 in if ok then YRet (SR_again h2 cx) else YRet (SR_done YS_alloc_failed h2 cx))) r ->
             yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) h0 cx0) r) ->
  (forall blk, plk_ok [] (h_set_stack3 h (stp :: h_stack h) (h_stack_size h + YAJL_BS_INC) blk)) ->
  pagain Y E h0 cx0 [] ->
  pexit_cont E (fun r => let '(st, h', cx') := r in yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) h0 cx0) (SR_done st h' cx')) ->
  realizes_cfg acfg bsegs (mkCfg (pstate E PUSH_GROW F fc m rav t0 t1 t2 (wz (h_stack_size h)) a1 a2 a3 a4 a5 a6 a7 s2v (wz (p_ff E)) (wz (state_code stp)) t3 t4 t5 t6) mo) (p_K E).
Proof. aceil.
  intros until t6. intros PA OK PM FRM U1 FULL SZM' SZB [PHIL PHI2] YGG PLK AG EX.
  popen OK PM; yhide TB; yhide OTB; yhide FFR0.
  pose proof (proj2 BC3) as US. pose proof (proj1 BC3) as U0'. assert (SZ : 0 < h_stack_size h) by (clear -CEILB FULL U1; lia).
  pose proof (state_code_range stp) as CR.
  pose proof (mk_pblk BLKY LAYY BSHY E s [] h mh h0 cx0 m mo PA OK AHK SAME SB1 SZ) as PB.
  pose proof (pb_HSB _ _ _ PB) as SEPHS; pose proof (pb_SB _ _ _ PB) as RSB; pose proof (pb_SBA PB) as RSBA; pose proof (pb_SBCX _ _ _ PB) as SEPSC.
  openPA PA; clear pa_ffCX0 pa_OT0.
  pose proof SAME as (EH & EL & ELB & EDB & ECX).
  assert (IN : forall b, In b (abl (yblocks mh h)) -> In b (abl (yblocks mh h) ++ [] ++ p_REST E)) by (intros b Hb; apply in_or_app; left; exact Hb).
  pose proof (proj1 (BSHY _ _ _ _ _ _ AHK (IN _ (yb_in_hand mh h)) ltac:(cbn; unfold SIZEOF_HANDLE; lia))) as OSH_H; cbn [ab_addr ab_size] in OSH_H.
  assert (OHH : oshw_hi 0 (2^47) <= mh_addr mh) by (revert pa_H0 EH; clear; unfold oshw_hi, A_SB; cbn; intros; lia).
  pose proof OSH_H as OSH_H'. unfold oshadow, A_SB, SIZEOF_HANDLE in OSH_H'. destruct OSH_H' as (_ & _ & SHH); rewrite EH in SHH.
  remember (blk_shadow 104) as shb eqn:SHHeq in SHH. pose proof SHH as SHH0; yhide SHH0.
  pose proof YS as (_ & _ & _ & STA).
  unfold hand_cells, hand_head_cells, alloc_cells in HC; cbn [yc_callbacks yc_malloc_w yc_realloc_w yc_free_w ayc app] in HC; unfold AY_REALLOC_W, wz in HC; rewrite EH in HC.
  pose proof BSR as BSR'. unfold RYajlRep.bs_rep in BSR'. destruct (h_stack_blk h) as [sbk|] eqn:HSB in BSR'; [| exfalso; exact (SB1 HSB)].
  destruct BSR' as (SBNZ & junk & SC).
  pose proof (rw_cells_bytes_at _ _ _ _ SC) as OLD. cbn [cells_bytes cbytes] in OLD. rewrite app_nil_r in OLD.
  pose proof (proj1 (proj1 SC)) as WFS. cbn [cells_wf cell_wf] in WFS. destruct WFS as (L1 & L2 & _).
  clear OLD.
  pose proof (sub_chunk m _ [C8 (p_fs0 E); C8 (p_s11 E); C8 (p_s10 E); C8 (p_s9 E); C8 (p_s8 E); C8 (p_s7 E); C8 (p_s6 E); C8 (p_s5 E); C8 (p_s4 E); C8 (p_s3 E); C8 (p_s2 E); C8 (p_s1 E)]
               [C8 (p_s0 E); C8 (p_ra E)] [] ltac:(rewrite app_nil_r; exact SV)) as SV16.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in SV16. replace (bv_unsigned (p_sp E) - 112 + 96) with (bv_unsigned (p_sp E) - 16) in SV16 by lia. yhide SV16.
  pose proof (bv_unsigned_in_range 64 (p_sp E)) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  clear HR. unfold wz in FR.
  set (hN := h_set_stack3 h (h_stack h) (h_stack_size h + 128) None). set (mhN := mh_set_stack mh 0).
  set (REST0 := abl (yblocks mhN hN) ++ p_REST E).
  assert (PERM0 : forall SB hx sid, h_stack_blk hx = Some sid -> h_lexer hx = h_lexer h -> h_decbuf hx = h_decbuf h ->
            Permutation (abl (yblocks (mh_set_stack mh SB) hx) ++ [] ++ p_REST E) (mkABlock SB (h_stack_size hx) :: REST0)).
  { intros SB hx sid H1 H3 H4. rewrite (abl_yblocks_split _ _ sid 0 H1). unfold REST0.
    replace (abl (yblocks (mh_set_stack (mh_set_stack mh SB) 0) (h_set_stack3 hx (h_stack hx) 0 None))) with (abl (yblocks mhN hN))
      by (unfold mhN, hN, yblocks, lexer_blocks, bs_blocks; cbn [mh_set_stack mh_id mh_addr mh_lid mh_lexer mh_lexbuf mh_decbuf mh_sid mh_stack h_set_stack3 h_stack_blk h_lexer h_decbuf]; rewrite H3, H4; reflexivity).
    cbn [mh_stack mh_set_stack app]. rewrite <- app_assoc. cbn [app]. symmetry. apply Permutation_middle. }
  (* [comment removed for export] *)
  set (Q0 := fun a : Z => (a < mh_addr (p_mh E) + 48 \/ mh_addr (p_mh E) + 60 <= a) /\ (ay_client_addr REST0 (pLF E) (p_SQ E) a /\ ~ yin_ivs [] a)).
  assert (XFER : forall mB, agree_on bsegs Q0 m mB ->
            alexer_rep mB (mh_lexer mh) (h_lexer h) (mh_lexbuf mh) (mh_addr mh + 72) /\ abuf_rep mB (mh_decbuf mh) (h_decbuf h) (mh_addr mh + 72)
            /\ actx_rep mB (pCX E) cx /\ atext_at mB (p_T E) (p_txt E)
            /\ (exists k0 k224, rw_cells bsegs mB (p_SQ E) (pframe E k0 k224)) /\ rw_cells bsegs mB (pSP E - 112) (psaved E) /\ pff E mB obw olw
            /\ oshadow mB (pCX E) 8 /\ stk bsegs mB (p_SQ E + 240) (pSP E - 112) /\ y_uanchor Y mB (pSP E) (p_ra E) (p_s0 E)).
  { intros mB AGQ. openPB PB.
    assert (INR0 : forall b, In b (abl (yblocks mhN hN)) -> In b REST0) by (intros b Hb; unfold REST0; apply in_or_app; left; exact Hb).
    assert (RCL : forall b a, In b REST0 -> ab_addr b <= a < ab_addr b + ab_size b -> (a < mh_addr (p_mh E) + 48 \/ mh_addr (p_mh E) + 60 <= a) -> Q0 a).
    { intros b a Hb Ha Ho. split; [exact Ho|]. split; [right; left; exists b; split; [exact Hb| exact Ha]| cbn; clear; tauto]. }
    assert (HICL : forall a, p_SQ E <= a -> Q0 a).
    { intros a Ha. split; [clear -CEILB Ha pa_H0 pa_ceil0 pa_SQ0 pa_lo0; lia|]. split; [left; exact Ha| cbn; clear; tauto]. }
    assert (CXCL : forall a, (mh_ctx (p_mh E) <= a < mh_ctx (p_mh E) + 8 \/ A_SB + mh_ctx (p_mh E) / 8 <= a < A_SB + mh_ctx (p_mh E) / 8 + 1) -> Q0 a).
    { intros a Ha. split; [clear -CEILB Ha pa_CXH0 pa_H0 pa_CX0; unfold A_SB in *; Z.div_mod_to_equations; lia|]. split; [| cbn; clear; tauto].
      right; right; left. exists f. split; [right; exact FIN|]. rewrite FCL. unfold ff_bytes. change (Z.shiftl 64 1) with 128. change (Z.shiftl 8 1) with 16.
      clear -CEILB Ha FCX pa_CX0. unfold A_SB in *. Z.div_mod_to_equations. lia. }
    assert (FFCL : forall a, ((p_ff E <= a < p_ff E + 128) \/ (p_ff E / 8 + 2147450880 <= a < p_ff E / 8 + 2147450880 + 16)) -> Q0 a).
    { intros a Ha. split; [clear -CEILB Ha pa_ffH0 pa_H0 pa_ff0; Z.div_mod_to_equations; lia|]. split; [| cbn; clear; tauto].
      right; right; left. exists (1, p_ff E). split; [left; reflexivity|]. cbn [fst snd]. unfold ff_bytes, A_SB. change (Z.shiftl 64 1) with 128. change (Z.shiftl 8 1) with 16.
      clear -CEILB Ha pa_ff0. lia. }
    split.
    { eapply lexer_rep_agree; [exact AGQ| exact LXR| | |].
      - intros a Ha. eapply RCL; [apply INR0; apply yb_in_lexer| unfold mhN; cbn [ab_addr ab_size mh_set_stack mh_lexer]; clear -CEILB Ha; lia| unfold SIZEOF_LEXER in Ha; clear -CEILB Ha pb_HL0; lia].
      - intros a Ha. eapply RCL; [apply INR0; apply yb_in_lexbuf| unfold mhN; cbn [ab_addr ab_size mh_set_stack mh_lexbuf]; clear -CEILB Ha; lia| unfold SIZEOF_BUF in Ha; clear -CEILB Ha pb_HLB0; lia].
      - intros HD a Ha. destruct (yb_data (lx_buf (h_lexer h))) as [d|] eqn:Hd; [| exfalso; apply HD; reflexivity].
        eapply RCL; [apply INR0; apply (yb_in_lexdata mhN hN); unfold hN; cbn; rewrite Hd; discriminate| unfold mhN, hN; cbn [ab_addr ab_size mh_set_stack mh_lexbuf h_set_stack3 h_lexer]; clear -CEILB Ha; lia| pose proof (pb_HLD0 d eq_refl) as X; clear -CEILB Ha X; lia]. }
    split.
    { eapply buf_rep_agree; [exact AGQ| exact DBR| |].
      - intros a Ha. eapply RCL; [apply INR0; apply yb_in_decbuf| unfold mhN; cbn [ab_addr ab_size mh_set_stack mh_decbuf]; clear -CEILB Ha; lia| unfold SIZEOF_BUF in Ha; clear -CEILB Ha pb_HDB0; lia].
      - intros HD a Ha. destruct (yb_data (h_decbuf h)) as [d|] eqn:Hd; [| exfalso; apply HD; reflexivity].
        eapply RCL; [apply INR0; apply (yb_in_decdata mhN hN); unfold hN; cbn; rewrite Hd; discriminate| unfold mhN, hN; cbn [ab_addr ab_size mh_set_stack mh_decbuf h_set_stack3 h_decbuf]; clear -CEILB Ha; lia| pose proof (pb_HDD0 d eq_refl) as X; clear -CEILB Ha X; lia]. }
    split. { eapply ctx_rep_agree; [exact AGQ| exact CXR|]. intros a Ha. apply CXCL. left. exact Ha. }
    split.
    { eapply text_at_agree; [exact AGQ| exact TXT|]. intros a Ha. yshow TB.
      destruct TB as [(bt & Hbt & B1 & B2)| Z0]; [| exfalso; clear -CEILB Ha Z0; lia].
      pose proof (pa_Tsep0 ltac:(clear -CEILB Ha; lia)) as (TH & _ & _).
      eapply (RCL bt); [unfold REST0; apply in_or_app; right; exact Hbt| clear -CEILB Ha B1 B2; lia| clear -CEILB Ha TH; lia]. }
    split. { exists k0, k224. eapply rw_cells_agree; [exact AGQ| exact FR|]. intros a Ha. apply HICL. clear -CEILB Ha. lia. }
    split. { yshow SV. eapply rw_cells_agree; [exact AGQ| exact SV|]. intros a Ha. apply HICL. clear -CEILB Ha pa_SQ0. lia. }
    split.
    { destruct pa_j0 as (J1 & J2 & J3). pose proof FF as (FFA & FOB & FJ2 & FOL & FJ3 & FSH).
      split; [eapply rw_cells_agree; [exact AGQ| exact FFA| intros a Ha; apply FFCL; unfold pffA in Ha; cbn [cells_size csize Nat.add] in Ha; clear -CEILB Ha; lia]|].
      split; [eapply rw_cells_agree; [exact AGQ| exact FOB| intros a Ha; apply FFCL; cbn [cells_size csize Nat.add] in Ha; clear -CEILB Ha; lia]|].
      split; [eapply rw_cells_agree; [exact AGQ| exact FJ2| intros a Ha; apply FFCL; cbn [cells_size csize Nat.add] in Ha; clear -CEILB Ha; lia]|].
      split; [eapply rw_cells_agree; [exact AGQ| exact FOL| intros a Ha; apply FFCL; cbn [cells_size csize Nat.add] in Ha; clear -CEILB Ha; lia]|].
      split; [eapply rw_cells_agree; [exact AGQ| exact FJ3| intros a Ha; apply FFCL; unfold pffZ in Ha; cbn [cells_size csize Nat.add] in Ha; clear -CEILB Ha; lia]|].
      eapply rw_cells_agree; [exact AGQ| exact FSH| intros a Ha; apply FFCL; unfold pffsh in Ha; cbn [cells_size csize Nat.add] in Ha; clear -CEILB Ha; lia]. }
    split. { eapply oshadow_agree; [exact AGQ| exact OCX|]. intros a Ha. apply CXCL. right. revert Ha. unfold oshw_lo, oshw_hi, A_SB, amem. clear. intros Ha. Z.div_mod_to_equations. lia. }
    split. { eapply stk_agree; [exact AGQ| exact GAP|]. intros a Ha. apply HICL. clear -CEILB Ha pa_SQ0 pa_ff0 pa_ceil0 pa_lo0. lia. }
    eapply UFRAME; [| exact UA]. intros a Ha. apply (proj1 (AGQ a ltac:(clear -CEILB Ha SPR; lia) (HICL a ltac:(clear -CEILB Ha pa_SQ0; lia)))). }
  clear TXT LXR DBR GAP. yhide SV. yhide PRES. yhide XFER.
  assert (USQ : bv_unsigned (Z_to_bv 64 (p_SQ E)) = p_SQ E) by (apply unsigned_lit; clear -CEILB pa_SQ0 pa_lo0 pa_ceil0 pa_sp0; lia).
  unfold YAJL_BS_INC in SZB, PHI2, PHIL, PLK. yhide PHI2. yhide PHIL. yhide PLK. yhide CRED.
  pose proof (munch_refl [(mh_addr (p_mh E) + 56, mh_addr (p_mh E) + 60)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  unfold pstate, PUSH_GROW, wz.
  arz_seg KIPY AHK.
  pose proof (mk_ppol BLKY LAYY BSHY E s [] h mh h0 cx0 m mo _ _ PA OK AHK SAME SB1 SZ LINK) as PP. openPP PP. pose proof (ppol_mark E mh) as PPM.
  unfold pol, AY_IMG_LO, AY_IMG_HI in pp_stk0, pp_H0, pp_Hs0, pp_img0. clear pp_imgsh0 pp_L0 pp_Ls0 pp_DB0 pp_DBs0 pp_SB0 pp_SBs0 pp_CX0 pp_CXs0 pp_ff0 pp_ffs0 pp_T0 pp_Ts0 LINK.
  zstepA.                                                  (* [comment removed for export] *)
  zstepA.                                                  (* [comment removed for export] *)
  zstepA. if_cases Kb; zify_cond Kb; [exfalso; revert Kb; clear -CEILB BC2; rewrite ?unsigned_lit by lia; intros Kb; lia| clear Kb].   (* [comment removed for export] *)
  zstepA.                                                  (* [comment removed for export] *)
  shH SHH SHHeq MU WM 56 4.                                (* [comment removed for export] *)
  zstepA. iflit2.                                          (* [comment removed for export] *)
  zstepA. rewrite (swrap32_small (h_stack_size h + 128)) by (clear -CEILB BC2 SZB pa_len0; lia).   (* [comment removed for export] *)
  zstepA.                                                  (* [comment removed for export] *)
  zstepA. shadow_addr.                                     (* [comment removed for export] *)
  zstepA.                                                  (* [comment removed for export] *)
  clear SHH. (* [comment removed for export] *) zstepA.                                                  (* [comment removed for export] *)
  zstepA.                                                  (* [comment removed for export] *)
  yshow SHH0. shH SHH0 SHHeq MU WM 64 8.                   (* [comment removed for export] *)
  zstepA. iflit2.                                          (* [comment removed for export] *)
  zstepA.                                                  (* [comment removed for export] *)
  ugd_bsN. zstepA. ugd_bsN.                                (* [comment removed for export] *)
  zstepA.                                                  (* [comment removed for export] *)
  zstepA. shadow_addr. zstepA.                             (* [comment removed for export] *)
  shH SHH0 SHHeq MU WM 80 8.                               (* [comment removed for export] *)
  zstepA. iflit2.                                          (* [comment removed for export] *)
  zstepA.                                                  (* [comment removed for export] *)
  zstepA. shadow_addr. zstepA.                             (* [comment removed for export] *)
  shH SHH0 SHHeq MU WM 96 8.                               (* [comment removed for export] *)
  zstepA. iflit2.                                          (* [comment removed for export] *)
  shH SHH0 SHHeq MU WM 48 8. yhide SHH0.                   (* [comment removed for export] *)
  zstepA. iflit2.                                          (* [comment removed for export] *)
  zstepA.                                                  (* [comment removed for export] *)
  zstepA.                                                  (* [comment removed for export] *)
  zstepA.                                                  (* [comment removed for export] *)
  zstepA.                                                  (* [comment removed for export] *)
  apply evtA_done. intros mo1 Hag1 HLI1 Hh1. destruct (BACK mo1 Hag1 HLI1) as [AHK1m R01].
  lazymatch goal with |- realizes_cfg _ _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ => rename mx into m1 end.
  lazymatch goal with H : mem_inv bsegs m1 |- _ => rename H into MI1 end.
  lazymatch goal with H : stk bsegs m1 (p_lo E) (p_SQ E) |- _ => rename H into ST1 end.
  lazymatch goal with H : rw_cells bsegs m1 (mh_addr (p_mh E)) _ |- _ => rename H into HC1 end.
  (* [comment removed for export] *)
  assert (MHS : mh_set_stack mh (mh_stack mh) = mh) by (destruct mh; reflexivity).
  assert (AHK1 : y_AHK Y s (mkABlock (mh_stack mh) (h_stack_size h) :: REST0) (pLF E) m1 mo1).
  { eapply PERMY; [| apply (PERM0 (mh_stack mh) h sbk HSB eq_refl eq_refl)| apply Permutation_refl]. rewrite MHS.
    eapply FRAMEY; [exact AHK1m| exact MU| exact WM|]. constructor; [| constructor]. right; left.
    exists (mkABlock (mh_addr mh) SIZEOF_HANDLE). split; [apply IN; apply yb_in_hand| cbn; unfold SIZEOF_HANDLE; rewrite EH; clear; lia]. }
  clear AHK1m.
  pose proof (aystatics_munch _ _ _ YS MU WM ltac:(constructor; [cbn [fst snd]; clear -CEILB pa_H0; lia| constructor])) as YS1.
  pose proof (rw_cells_bytes_at _ _ _ _ SC) as OLD1. cbn [cells_bytes cbytes] in OLD1. rewrite app_nil_r in OLD1.
  yshow PHIL. yshow CRED. yshow SV16. yshow UA.
  assert (PHI0 : forall hx L, 0 <= y_phi_hand Y hx L) by (destruct NONNEG as (_ & _ & NH & _); exact NH).
  pose proof PHIL as PHI2'.
  set (cr2 := cr - ypushc Y (h_stack_size h)) in *.
  eapply (WREA (mh_stack mh) (h_stack_size h) (h_stack_size h + 128) (zbytes (stack_bytes (h_stack h)) ++ junk)
               (mkABlock (mh_stack mh) (h_stack_size h) :: REST0) (pLF E) (p_lo E) (p_RR E + cr2) (p_K E));
    [ exact K0
    | apply AYST_split; split; [exact AHK1| exact YS1]
    | left; reflexivity
    | exact OLD1
    | rewrite length_app, L1, L2; clear -CEILB US U0'; lia
    | reflexivity
    | reflexivity
    | clear -CEILB SZB pa_len0 SZ; lia
    | unfold cr2, ypushc, YAJL_BS_INC; clear -CEILB CRED; lia
    | lazymatch type of PHI2' with _ + y_phi_hand Y ?hx ?L <= _ => pose proof (PHI0 hx L) as Q end; unfold cr2; clear -CEILB RR0 PHI2' Q; lia
    | unfold REST0; pose proof (nbig_cons_le (mkABlock (mh_stack mh) (h_stack_size h)) (abl (yblocks mhN hN) ++ p_REST E)) as Q1;
      rewrite gnbig_app in Q1; pose proof (gnbig_yblocks mhN hN) as Q2; unfold AY_NBIG_REST in NBIG; clear -CEILB Q1 Q2 NBIG; lia
    | unfold ayframe_pre, AY_WRAP_STACK, AMALLOC_STACK; aceil;
      rewrite unsigned_lit by (clear -CEILB pa_SQ0 pa_ceil0 pa_lo0 SPR; lia);
      split; [exact ST1|]; split; [clear -CEILB pa_ceil0; lia|]; split; [clear -CEILB pa_SQ0 pa_lo0; lia|]; split; [clear -CEILB pa_SQ0 pa_sp0; lia|];
      split; [clear -CEILB pa_SQ0; Z.div_mod_to_equations; lia|]; split; [exact MI1|]; split; [exact TP| exact FRM]
    | rewrite unsigned_lit by (clear -CEILB pa_SQ0 pa_ceil0 pa_lo0 SPR; lia);
      eapply USTEP; [unfold PUSH_RET; rewrite unsigned_lit by (clear; lia); exact URA_push
                    | clear -CEILB pa_SQ0 pa_sp0; lia
                    | eapply (rw_cells_transport bsegs); [exact SV16| exact MU| exact WM| cbn; clear -CEILB pa_H0 pa_ceil0 pa_lo0; lia]
                    | eapply UFRAME; [| exact UA]; intros a Ha; apply MU; rewrite wa_unsigned by (clear -CEILB Ha SPR; lia); cbn; clear -CEILB Ha pa_H0 pa_ceil0 pa_lo0; lia ]
    | ].
  cbv beta. intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F2 fc2 m2 mo2 s2' A' (MI2 & ST2 & FRM2 & _ & PRES2) SO2 R2 CRED2 RES.
  rewrite ab_remove_head in PRES2, RES. rewrite unsigned_lit in ST2, PRES2 by (clear -CEILB pa_SQ0 pa_ceil0 pa_lo0 SPR; lia).
  unfold PUSH_RET. rewrite (ret_pc_even 563140) by (clear; lia).
  (* [comment removed for export] *)
  pose proof (ay_pres_agree _ _ _ _ _ _ PRES2) as AG2.
  assert (IHR0 : In (mkABlock (mh_addr mh) SIZEOF_HANDLE) REST0) by (unfold REST0; apply in_or_app; left; apply (yb_in_hand mhN hN)).
  lazymatch type of HC1 with rw_cells _ _ _ ?cs => assert (HC2 : rw_cells bsegs m2 (mh_addr (p_mh E)) cs) end.
  { eapply rw_cells_agree; [exact AG2| exact HC1|]. intros a Ha. split; [| cbn; clear; tauto]. right; left. exists (mkABlock (mh_addr mh) SIZEOF_HANDLE).
    split; [exact IHR0| cbn [ab_addr ab_size]; unfold SIZEOF_HANDLE; rewrite EH; revert Ha; cbn [cells_size csize Nat.add]; clear; intros; lia]. }
  clear HC1.
  (* [comment removed for export] *)
  assert (AGQ2 : forall m3 W3, munch W3 m2 m3 -> wmono bsegs m2 m3 -> (forall a, Q0 a -> outside W3 a) -> agree_on bsegs Q0 m m3).
  { intros m3 W3 MU3 WM3 HW a Ha HQ. pose proof HQ as [HO HCl].
    destruct (munch_agree _ _ _ MU WM a Ha ltac:(cbn; clear -CEILB HO; lia)) as [E1 W1].
    destruct (AG2 a Ha HCl) as [E2 W2]. destruct (munch_agree _ _ _ MU3 WM3 a Ha (HW a HQ)) as [E3 W3'].
    split; [congruence| intros X; apply W3'; apply W2; apply W1; exact X]. }
  (* [comment removed for export] *)
  destruct (BLKY _ _ _ _ _ AHK) as (RNG & SEP & ND). destruct (LAYY _ _ _ _ _ AHK) as (LAYF & LAYFB & LAYFF).
  assert (HSEP : asep_from (mkABlock (mh_addr mh) SIZEOF_HANDLE) (tl (abl (yblocks mh h) ++ [] ++ p_REST E))) by exact (proj1 (ay_all_sep Y BLKY _ _ _ _ _ AHK)).
  assert (TLE : tl (abl (yblocks mh h) ++ [] ++ p_REST E) = tl (abl (yblocks mh h)) ++ p_REST E) by reflexivity.
  assert (CQ0 : forall a, ay_client_addr (p_REST E) (p_LF E) (pSP E) a -> ~ yin_ivs [(pCX E, pCX E + 8)] a -> Q0 a).
  { intros a Hc Hx. destruct Hc as [Hc|[Hc|[Hc|Hc]]].
    - split; [clear -CEILB Hc pa_H0 pa_ceil0 pa_lo0; lia|]. split; [left; clear -CEILB Hc pa_SQ0; lia| cbn; clear; tauto].
    - destruct Hc as (b & Hb & Hr). split.
      + pose proof (asep_from_In _ _ b HSEP ltac:(rewrite TLE; apply in_or_app; right; exact Hb)) as D.
        unfold absep in D. cbn [ab_addr ab_size] in D. unfold SIZEOF_HANDLE in D. rewrite EH in D. clear -CEILB D Hr. lia.
      + split; [right; left; exists b; split; [unfold REST0; apply in_or_app; right; exact Hb| exact Hr]| cbn; clear; tauto].
    - destruct Hc as (f' & Hf' & Hr). split.
      + pose proof (proj1 (LAYFB f' _ (or_intror Hf') (IN _ (yb_in_hand mh h)))) as D. cbn [ab_addr ab_size] in D. unfold SIZEOF_HANDLE in D. rewrite EH in D.
        pose proof (LAYF f' (or_intror Hf')) as (F1' & F2' & F3' & F4' & _). aceil.
        revert Hr D F1' F2' F4' pa_H0 CEILB. clear. unfold oshw_lo, oshw_hi, A_SB, amem. intros Hr D F1' F2' F4' PH0 CEILB.
        assert (E0 : fst f' = 0 \/ fst f' = 1) by lia.
        destruct E0 as [E0|E0]; rewrite E0 in Hr, F1', D, F2'; [change (ff_bytes 0) with 64 in F1', Hr, D, F2'; change (Z.shiftl 8 0) with 8 in Hr| change (ff_bytes 1) with 128 in F1', Hr, D, F2'; change (Z.shiftl 8 1) with 16 in Hr]; lia.
      + split; [right; right; left; exists f'; split; [right; exact Hf'| exact Hr]| cbn; clear; tauto].
    - split; [unfold ay_static in Hc; clear -CEILB Hc pa_H0; lia|]. split; [right; right; right; exact Hc| cbn; clear; tauto]. }
  yhide CQ0. yhide AGQ2.
  (* [comment removed for export] *)
  - (* [comment removed for export] *)
    destruct RES as (EA0 & ARNG & AHI & _ & OSH_A & (junk2 & NEW) & AY2 & REF2). subst a0'. unfold wz.
    unfold ablock_range, ACONSTS in ARNG. cbn [c_img_hi] in ARNG. aceil.
    replace (Z.min (h_stack_size h + 128) (h_stack_size h)) with (h_stack_size h) in NEW by (clear -CEILB SZ; lia).
    rewrite firstn_all2 in NEW by (rewrite length_app, L1, L2; clear -CEILB US U0'; lia).
    replace (h_stack_size h + 128 - h_stack_size h) with 128 in NEW by (clear; lia).
    apply AYST_split in AY2. destruct AY2 as [AHK2 YS2].
    set (h1 := h_set_stack3 h (h_stack h) (h_stack_size h + 128) (Some 0%nat)). set (mh1 := mh_set_stack mh A').
    assert (AHK2' : y_AHK Y s2' (abl (yblocks mh1 h1) ++ [] ++ p_REST E) (pLF E) m2 mo2).
    { eapply PERMY; [exact AHK2| | apply Permutation_refl]. apply Permutation_sym. apply (PERM0 A' h1 0%nat); reflexivity. }
    (* [comment removed for export] *)
    destruct (BLKY _ _ _ _ _ AHK2) as (_ & SEP2 & ND2).
    pose proof (SEP2 _ _ (or_introl eq_refl) (or_intror IHR0) (nd_head_ne _ _ _ ND2 IHR0)) as SEPAH. cbn [ab_addr ab_size] in SEPAH. unfold SIZEOF_HANDLE in SEPAH. rewrite EH in SEPAH.
    clear SEP2 ND2.
    pose proof (BSHY _ _ _ _ _ _ AHK2 (or_intror IHR0) ltac:(cbn; unfold SIZEOF_HANDLE; lia)) as [OSH_H2 _]. cbn [ab_addr ab_size] in OSH_H2.
    unfold oshadow, A_SB, SIZEOF_HANDLE in OSH_H2. destruct OSH_H2 as (_ & _ & SHH2). rewrite EH in SHH2. rewrite <- SHHeq in SHH2.
    (* [comment removed for export] *)
    pose proof (munch_refl [(mh_addr (p_mh E) + 48, mh_addr (p_mh E) + 56)] m2) as MU2. pose proof (wmono_refl bsegs m2) as WM2.
    clear BACK. arz_seg KIPY AHK2'.
    assert (PSTK : pol (acc_ok (m_vm_lazy mo2) (y_aS Y s2')) (p_lo E) (pSP E))
      by (apply (aypol_stack Y _ _ _ _ LINK); [aceil; clear -CEILB pa_ceil0; lia| clear -CEILB pa_sp0; lia]).
    destruct (aypol_opol_block Y _ _ _ _ LINK (mkABlock (mh_addr mh) SIZEOF_HANDLE) ltac:(apply in_or_app; left; apply (yb_in_hand mh1 h1))
                ltac:(cbn; unfold SIZEOF_HANDLE; clear -CEILB pa_H0 EH; lia) ltac:(cbn; unfold oshw_lo, A_SB; clear -CEILB pa_H0 EH; lia)
                ltac:(cbn; unfold oshw_hi, A_SB, amem, SIZEOF_HANDLE; clear -CEILB pa_H0 EH; Z.div_mod_to_equations; lia) ltac:(cbn; unfold SIZEOF_HANDLE; clear -CEILB pa_H0 EH; lia)) as [PH PHs].
    cbn [ab_addr ab_size] in PH, PHs. unfold pol, oshw_lo, oshw_hi, A_SB, amem, SIZEOF_HANDLE in PSTK, PH, PHs. rewrite EH in PH, PHs. change ((104 + 7) / 8) with 13 in PHs.
    clear PPM. pose proof (ppol_mark E mh1) as PPM. clear LINK.
    shH SHH2 SHHeq MU2 WM2 48 8.                           (* [comment removed for export] *)
    zstepA. iflit2.                                        (* [comment removed for export] *)
    clear SHH2. (* [comment removed for export] *) zstepA.                                                (* [comment removed for export] *)
    zstepA. if_cases Kz; zify_cond Kz; [exfalso; clear -CEILB ARNG Kz; lia| clear Kz].   (* [comment removed for export] *)
    apply evtA_done. intros mo3 Hag3 HLI3 Hh3. destruct (BACK mo3 Hag3 HLI3) as [AHK3m R23].
    lazymatch goal with |- realizes_cfg _ _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ => rename mx into m3 end.
    lazymatch goal with H : mem_inv bsegs m3 |- _ => rename H into MI3 end.
    lazymatch goal with H : stk bsegs m3 (p_lo E) (p_SQ E) |- _ => rename H into ST3 end.
    lazymatch goal with H : rw_cells bsegs m3 (mh_addr (p_mh E)) _ |- _ => rename H into HC3 end.
    lazymatch goal with H : rw_cells bsegs m3 A' _ |- _ => rename H into NEW3 end.
    assert (AHK3 : y_AHK Y s2' (abl (yblocks mh1 h1) ++ [] ++ p_REST E) (pLF E) m3 mo3).
    { eapply FRAMEY; [exact AHK3m| exact MU2| exact WM2|]. constructor; [| constructor]. right; left.
      exists (mkABlock (mh_addr mh) SIZEOF_HANDLE). split; [apply in_or_app; left; apply (yb_in_hand mh1 h1)| cbn; unfold SIZEOF_HANDLE; rewrite EH; clear; lia]. }
    clear AHK3m.
    pose proof (aystatics_munch _ _ _ YS2 MU2 WM2 ltac:(constructor; [cbn [fst snd]; clear -CEILB pa_H0; lia| constructor])) as YS3.
    yshow AGQ2. pose proof (AGQ2 m3 _ MU2 WM2 ltac:(intros a [HO _]; cbn; clear -CEILB HO; lia)) as AGQ3. yhide AGQ2.
    yshow XFER. destruct (XFER m3 AGQ3) as (LXR3 & DBR3 & CXR3 & TXT3 & FR3 & SV3 & FF3 & OCX3 & GAP3 & UA3). yhide XFER.
    yshow CQ0. yshow PRES. yshow CRED. yshow PHI2.
    set (cr3 := cr2 + y_arefund Y (h_stack_size h)).
    destruct junk as [|j0 junk']; [| exfalso; cbn [length] in L2; clear -CEILB L2 FULL; lia]. rewrite app_nil_r in NEW3.
    assert (PM3 : pmem E m3 mo3 s2' [] h1 mh1 cx obw olw cr3).
    { split. { apply AYST_split. split; [exact AHK3| exact YS3]. }
      split.
      { split; [| split; [| split]].
        - split; [| unfold h1, mh1; cbn [h_set_stack3 h_bytesConsumed h_stack_size h_stack_blk h_parseError mh_set_stack mh_stack];
                   split; [exact BC1| split; [clear -CEILB BC2 SZB pa_len0; lia| split; [unfold h_used; cbn [h_stack h_set_stack3]; unfold h_used in BC3; clear -CEILB BC3; lia| split; [discriminate| intros A0; exfalso; clear -CEILB A0 ARNG; lia]]]]].
          exists pew, pad. split; [| exact PW].
          unfold hand_cells, hand_head_cells, alloc_cells, h1, mh1.
          cbn [yc_callbacks yc_malloc_w yc_realloc_w yc_free_w ayc app h_set_stack3 h_bytesConsumed h_stack_size h_stack mh_set_stack mh_ctx mh_lexer mh_decbuf mh_stack mh_addr].
          replace (h_used (mkHandle (h_blk h) (h_lexer_blk h) (h_lexer h) (h_parseError h) (h_bytesConsumed h) (h_decbuf_blk h) (h_decbuf h) (h_stack h) (h_stack_size h + 128) (Some 0%nat))) with (h_used h) by reflexivity.
          unfold AY_REALLOC_W, wz. rewrite EH. exact HC3.
        - unfold h1, mh1; cbn [h_set_stack3 h_lexer mh_set_stack mh_lexer mh_lexbuf mh_addr]. exact LXR3.
        - unfold h1, mh1; cbn [h_set_stack3 h_decbuf mh_set_stack mh_decbuf mh_addr]. exact DBR3.
        - unfold RYajlRep.bs_rep, h1, mh1. cbn [h_stack_blk h_set_stack3 mh_set_stack mh_stack h_stack h_stack_size]. split; [clear -CEILB ARNG; lia|].
          exists junk2. replace (h_used (mkHandle (h_blk h) (h_lexer_blk h) (h_lexer h) (h_parseError h) (h_bytesConsumed h) (h_decbuf_blk h) (h_decbuf h) (h_stack h) (h_stack_size h + 128) (Some 0%nat))) with (h_used h) by reflexivity.
          rewrite FULL. replace (h_stack_size h + 128 - h_stack_size h) with 128 by (clear; lia). exact NEW3. }
      split. { unfold mh_same, mh1. cbn [mh_set_stack mh_id mh_addr mh_lid mh_lexer mh_lexbuf mh_decbuf mh_sid mh_stack mh_ctx]. exact SAME. }
      split; [exact CXR3|]. split; [exact TXT3|]. split; [exact FR3|]. split; [exact SV3|]. split; [exact FF3|]. split; [exact OCX3|].
      split; [exact ST3|]. split; [exact GAP3|]. split; [exact MI3|].
      split. { eapply ay_pres_trans; [exact PRES|]. intros a Ha Hc Hx. exact (AGQ3 a Ha (CQ0 a Hc Hx)). }
      split; [exact UA3|].
      split. { pose proof (PHI2 0%nat) as X. lazymatch type of X with y_phi_hand Y ?hx ?L + _ <= _ => pose proof (PHI0 hx L) as Q end. unfold cr3, cr2. unfold cr2 in REF2. clear -CEILB REF2 X Q. split; lia. }
      split. { split; [rewrite SO2; exact SO1| eapply RRT; [eapply RRT; [eapply RRT; [exact R1| exact R01]| exact R2]| exact R23]]. }
      split; [unfold h1; cbn [h_stack_blk h_set_stack3]; discriminate| reflexivity].   (* [comment removed for export] *) }
    pose proof (push_room Y KIPY FRAMEY BLKY BSHY LAYY RRT UFRAME E F2 fc2 m3 mo3 s2' [] h0 cx0 h1 mh1 cx obw olw cr3 stp) as PR.
    unfold pstate, PUSH_ROOM, wz, h1, mh1 in PR. cbn [mh_addr mh_set_stack] in PR. fold h1 in PR.
    eapply PR; [exact PA| exact OK| exact PM3| exact FRM2| | | | | apply plk_ok_nil| exact AG].
    + unfold h1. unfold h_used. cbn [h_stack h_stack_size h_set_stack3]. unfold h_used in FULL. clear -CEILB FULL. lia.
    + unfold h1. cbn [h_stack_size h_set_stack3]. clear -CEILB SZM'. Z.div_mod_to_equations. lia.
    + apply YGG. unfold ybs_push. rewrite (proj2 (Z.eqb_eq _ _)) by (clear -CEILB FULL; lia).
      replace (UINT_MAX - YAJL_BS_INC <? h_stack_size h) with false by (symmetry; apply Z.ltb_ge; unfold UINT_MAX, YAJL_BS_INC; clear -CEILB SZB pa_len0; lia).
      eapply yleaf_bind.
      * eapply yleaf_bind; [apply (yl_realloc _ _ _ (Some 0%nat)); apply yl_ret|]. cbv beta iota. apply yl_ret.
      * cbv beta iota. unfold YAJL_BS_INC, h1. apply yl_ret.
    + apply (pcr_full YHM E _ _ PA). pose proof (PHI2 0%nat) as X. unfold cr3, cr2, h1, YAJL_BS_INC.
      enough (G : forall q, q + ypushc Y (h_stack_size h) <= cr + y_arefund Y (h_stack_size h) -> q <= cr - ypushc Y (h_stack_size h) + y_arefund Y (h_stack_size h)) by (apply G; exact X). clear; intros; lia.
Qed.
End W.
End RC__2.
