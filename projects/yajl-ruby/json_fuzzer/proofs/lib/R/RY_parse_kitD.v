(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Image ZBridge SysStep SFModel SFW1_lemmas InitMem Arr FP NodesCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Images.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import PortShim.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RMallocRep RMallocTree RMalloc_iface RYajlRep RYajl_iface RY_lib RY_rz RY_kit2 RY_parse_kit RY_parse_kitJ.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Agent Require Import MallocBlocks.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import RawAlloc Prelim YajlBase YajlBuf YajlLex YajlDecode YajlParser YajlLeaf YajlFactsBuf YajlFactsLex YajlFactsParse YajlFactsLoop.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section S.
Variable HK : RawAlloc.PState -> list block -> (word -> option byte) -> Model -> Prop.
Hypothesis HKS : HK_silent_stmt HK.
Hypothesis HKP : HK_perm_stmt HK.
Hypothesis HKF : HK_frame_stmt HK.
Hypothesis HKB : HK_blocks_stmt HK.
Hypothesis YSD : ystring_decode_stmt HK.
Notation buf_rep := (buf_rep rsegs).
Notation buf_struct := (buf_struct rsegs).
Notation buf_data := (buf_data rsegs).
Notation lexer_rep := (lexer_rep rsegs).
Notation hand_rep := (hand_rep rsegs ryc).
Notation hand_struct := (hand_struct rsegs ryc).
Notation bs_rep := (bs_rep rsegs).
Notation ctx_rep := (ctx_rep rsegs).
Notation text_at := (text_at rsegs).
Notation RYST := (RYST HK).
Notation yparse_head_inv := (yparse_head_inv HK).
Notation yparse_exit_cont := (yparse_exit_cont HK).
Notation pmem := (pmem HK).
Notation again_cont := (again_cont HK).
Notation exit_cont := (exit_cont HK).
Notation yhead_invX := (yhead_invX HK).

Ltac kill K := exfalso; revert K; unfold wz; rewrite ?unsigned_lit by lia;
  try (change 18446744073709551615 with (Z.ones 64); rewrite ?Z.land_ones by lia; rewrite ?Z.mod_small by lia); lia.


(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma all_sep_app12 : forall (l1 l2 : list block) x y, all_sep (l1 ++ l2) -> In x l1 -> In y l2 -> bsep x y.
Proof.
  induction l1 as [|z l1 IH]; intros l2 x y H Hx Hy; [destruct Hx|].
  cbn in H. destruct H as [H1 H2]. destruct Hx as [<-|Hx].
  - apply (sep_from_In _ _ _ H1). apply in_or_app. right. exact Hy.
  - exact (IH _ _ _ H2 Hx Hy).
Qed.

Lemma pzbytes_firstn : forall k l, zbytes (firstn k l) = firstn k (zbytes l).
Proof. intros k l. unfold zbytes. rewrite firstn_map. reflexivity. Qed.
Lemma pzbytes_skipn : forall k l, zbytes (skipn k l) = skipn k (zbytes l).
Proof. intros k l. unfold zbytes. rewrite skipn_map. reflexivity. Qed.
Lemma pbytes_at_sub : forall m A bs i k,
  bytes_at rsegs m A bs -> (i <= length bs)%nat -> bytes_at rsegs m (A + Z.of_nat i) (firstn k (skipn i bs)).
Proof.
  intros m A bs i k HB Hi.
  rewrite <- (firstn_skipn i bs) in HB. apply bytes_at_app in HB. destruct HB as [_ HB].
  rewrite length_firstn, Nat.min_l in HB by lia.
  rewrite <- (firstn_skipn k (skipn i bs)) in HB. apply bytes_at_app in HB. destruct HB as [HB _]. exact HB.
Qed.
Lemma pbytes_at_zslice : forall m A str i k,
  bytes_at rsegs m A (zbytes str) -> 0 <= i <= zlength str -> bytes_at rsegs m (A + i) (zbytes (zslice str i k)).
Proof.
  intros m A str i k HB Hi. unfold zslice. rewrite pzbytes_firstn, pzbytes_skipn.
  replace i with (Z.of_nat (Z.to_nat i)) at 1 by lia. apply pbytes_at_sub; [exact HB|]. rewrite zbytes_length. unfold zlength in Hi. lia.
Qed.
Lemma pForall_zslice : forall (P : Z -> Prop) str i k, Forall P str -> Forall P (zslice str i k).
Proof.
  intros P str i k HF. unfold zslice.
  rewrite <- (firstn_skipn (Z.to_nat i) str) in HF. apply Forall_app in HF. destruct HF as [_ HF].
  rewrite <- (firstn_skipn (Z.to_nat k) (skipn (Z.to_nat i) str)) in HF. apply Forall_app in HF. tauto.
Qed.

Definition mh_set_decbuf (mh : mhand) (mbd : mbuf) : mhand :=
  mkMH (mh_id mh) (mh_addr mh) (mh_lid mh) (mh_lexer mh) (mh_lexbuf mh) mbd (mh_sid mh) (mh_stack mh) (mh_ctx mh).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ownD (E : penv) (mh : mhand) (h : yhandle) (iv : Z * Z) : Prop :=
  (p_lo E <= fst iv /\ snd iv <= pSP E)
  \/ (mb_addr (mh_decbuf mh) <= fst iv /\ snd iv <= mb_addr (mh_decbuf mh) + 32)
  \/ (yb_data (h_decbuf h) <> None /\ mb_data (mh_decbuf mh) <= fst iv /\ snd iv <= mb_data (mh_decbuf mh) + yb_len (h_decbuf h)).

Lemma ownD_outside : forall E mh h W a,
  Forall (ownD E mh h) W ->
  (a < p_lo E \/ pSP E <= a) ->
  (a < mb_addr (mh_decbuf mh) \/ mb_addr (mh_decbuf mh) + 32 <= a) ->
  (yb_data (h_decbuf h) <> None -> a < mb_data (mh_decbuf mh) \/ mb_data (mh_decbuf mh) + yb_len (h_decbuf h) <= a) ->
  outside W a.
Proof.
  intros E mh h W a HF H1 H2 H3. induction HF as [| [lo hi] W HO HF IH]; [exact I|].
  cbn. split; [| exact IH]. unfold ownD in HO. cbn [fst snd] in HO.
  destruct HO as [HO|[HO|[HD HO]]]; [lia| lia| specialize (H3 HD); lia].
Qed.

Lemma pmem_updD : forall E m m' mo s LK h mh cx obw olw b' W,
  pok E -> pmem E m mo s LK h mh cx obw olw ->
  munch W m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
  Forall (ownD E mh h) W ->
  yb_data b' = yb_data (h_decbuf h) -> yb_len b' = yb_len (h_decbuf h) ->
  buf_rep m' (mh_decbuf mh) b' (pH E + 72) ->
  stk rsegs m' (p_lo E) (pSP E) ->
  pmem E m' mo s LK (h_set_decbuf h b') mh cx obw olw.
Proof.
  intros until W. intros OK PM MU WM MI' OWN ED EL BR' STK'.
  pose proof (pmem_ranges _ HKB _ _ _ _ _ _ _ _ _ _ OK PM) as (I1 & I2 & R1 & R2 & S12 & B1 & B2 & B3).
  destruct OK as (K0 & LP & U0 & SB0 & L26 & TB & SPC & CXB & CEIL & LO & TP & B64 & PYR).
  destruct PM as (RY & HR & SAME & CXR & TXT & (padw & FR) & AX & STK & ERR & MI & PRES & SB1 & LK0).
  apply RYST_split in RY. destruct RY as [HK0 YS]. destruct (HK_blocks HK HKB _ _ _ _ HK0) as [RNG SEP].
  destruct HR as (HS & LXR & DBR & BSR).
  pose proof (proj1 STK) as LO0. unfold pSP in LO0, STK, STK', LO.
  pose proof AX as (av & x3 & x4 & x5 & x16 & x6 & x11 & x12 & x23 & rnd & _ & _ & _ & CB0 & _). unfold alloc_ceiling in CB0.
  pose proof SAME as (_ & EHA & _). unfold pH in BR'. rewrite <- EHA in BR'.
  pose proof (munch_agree _ _ _ MU WM) as AG.
  destruct TXT as (TXB & TXF & T0 & T62).
  rewrite (yblocks_mid mh h LK (p_REST E) SB1) in RNG, SEP, HK0.
  set (MID := mid_blocks mh h) in *. set (TL := LK ++ p_REST E) in *.
  (* [comment removed for export] *)
  assert (IDB : In (mb_id (mh_decbuf mh), mb_addr (mh_decbuf mh), SIZEOF_BUF) MID).
  { unfold MID, mid_blocks. apply in_or_app. right. left. reflexivity. }
  assert (IDD : yb_data (h_decbuf h) <> None -> In (mb_did (mh_decbuf mh), mb_data (mh_decbuf mh), yb_len (h_decbuf h)) MID).
  { intros HD. unfold MID, mid_blocks, buf_blocks. apply in_or_app. right. destruct (yb_data (h_decbuf h)); [| congruence]. right. left. reflexivity. }
  (* [comment removed for export] *)
  assert (OUTb : forall y a, In y ((mh_id mh, mh_addr mh, SIZEOF_HANDLE) :: MID ++ (mh_sid mh, mh_stack mh, h_stack_size h) :: TL) ->
            bsep y (mb_id (mh_decbuf mh), mb_addr (mh_decbuf mh), SIZEOF_BUF) ->
            (yb_data (h_decbuf h) <> None -> bsep y (mb_did (mh_decbuf mh), mb_data (mh_decbuf mh), yb_len (h_decbuf h))) ->
            blk_addr y <= a < blk_addr y + blk_size y -> outside W a).
  { intros y a Hy D1 D2 Ha. pose proof (all_range_In _ _ RNG Hy) as Ry. unfold rblock_range, alloc_ceiling in Ry.
    unfold bsep, SIZEOF_BUF in D1, D2. cbn [blk_addr blk_size fst snd] in D1, D2.
    eapply ownD_outside; [exact OWN| clear -Ha Ry CEIL; lia| clear -Ha D1; lia| intros HD; specialize (D2 HD); clear -Ha D2; lia]. }
  cbn [all_sep] in SEP. destruct SEP as [SEPH SEPT].
  (* [comment removed for export] *)
  assert (OUTH : forall a, mh_addr mh <= a < mh_addr mh + 104 -> outside W a).
  { intros a Ha. apply (OUTb (mh_id mh, mh_addr mh, SIZEOF_HANDLE)); [left; reflexivity| | | cbn; unfold SIZEOF_HANDLE; exact Ha].
    - apply (sep_from_In _ _ _ SEPH). apply in_or_app. left. exact IDB.
    - intros HD. apply (sep_from_In _ _ _ SEPH). apply in_or_app. left. exact (IDD HD). }
  (* [comment removed for export] *)
  assert (OUTL : forall y a, In y (lexer_blocks (mh_lid mh) (mh_lexer mh) (mh_lexbuf mh) (h_lexer h)) -> blk_addr y <= a < blk_addr y + blk_size y -> outside W a).
  { intros y a Hy Ha. assert (SEPM : all_sep (MID ++ (mh_sid mh, mh_stack mh, h_stack_size h) :: TL)) by exact SEPT.
    unfold MID, mid_blocks in SEPM. rewrite <- app_assoc in SEPM.
    apply (OUTb y); [right; apply in_or_app; left; unfold MID, mid_blocks; apply in_or_app; left; exact Hy| | | exact Ha].
    - apply (all_sep_app12 _ _ _ _ SEPM Hy). apply in_or_app. left. left. reflexivity.
    - intros HD. apply (all_sep_app12 _ _ _ _ SEPM Hy). apply in_or_app. left. unfold buf_blocks. destruct (yb_data (h_decbuf h)); [| congruence]. right. left. reflexivity. }
  (* [comment removed for export] *)
  assert (OUTT : forall y a, In y ((mh_sid mh, mh_stack mh, h_stack_size h) :: TL) -> blk_addr y <= a < blk_addr y + blk_size y -> outside W a).
  { intros y a Hy Ha. apply (OUTb y); [right; apply in_or_app; right; exact Hy| | | exact Ha].
    - pose proof (all_sep_app12 _ _ _ _ SEPT IDB Hy) as X. unfold bsep in X |- *. clear -X. lia.
    - intros HD. pose proof (all_sep_app12 _ _ _ _ SEPT (IDD HD) Hy) as X. unfold bsep in X |- *. clear -X. lia. }
  (* [comment removed for export] *)
  pose proof (all_range_In _ _ RNG ltac:(right; apply in_or_app; left; exact IDB)) as RDB. unfold rblock_range, alloc_ceiling, SIZEOF_BUF in RDB. cbn [blk_addr blk_size fst snd] in RDB.
  assert (RDD : yb_data (h_decbuf h) <> None -> 0 < mb_data (mh_decbuf mh) /\ mb_data (mh_decbuf mh) + yb_len (h_decbuf h) <= (Z.max 0x7fff80000000 (Z.min 0x800000000000 rc_sp) - 8388608) /\ (mb_data (mh_decbuf mh) + yb_len (h_decbuf h) <= 0x10000 \/ 0x56000 <= mb_data (mh_decbuf mh))).
  { intros HD. pose proof (all_range_In _ _ RNG ltac:(right; apply in_or_app; left; exact (IDD HD))) as X. unfold rblock_range, alloc_ceiling in X. cbn [blk_addr blk_size fst snd] in X. clear -X. lia. }
  assert (OUTI : forall a, 0x23000 <= a < 0x56000 -> outside W a).
  { intros a Ha. eapply ownD_outside; [exact OWN| clear -Ha CEIL; lia| clear -Ha RDB; lia| intros HD; specialize (RDD HD); clear -Ha RDD; lia]. }
  assert (OUTS : forall a, bv_unsigned (p_sp E) <= a -> outside W a).
  { intros a Ha. eapply ownD_outside; [exact OWN| unfold pSP; clear -Ha; lia| clear -Ha RDB CEIL LO; lia| intros HD; specialize (RDD HD); clear -Ha RDD CEIL LO; lia]. }
  split.
  { apply RYST_split. rewrite (yblocks_mid mh (h_set_decbuf h b') LK (p_REST E)) by exact SB1.
    replace (mid_blocks mh (h_set_decbuf h b')) with MID by (unfold MID, mid_blocks, buf_blocks; cbn [h_lexer h_decbuf h_set_decbuf]; rewrite ED, EL; reflexivity).
    cbn [h_stack_size h_set_decbuf]. fold TL. split.
    - eapply HKF; [exact HK0| exact MU| exact WM|].
      eapply Forall_impl; [| exact OWN]. intros iv Hiv. unfold ownD in Hiv. unfold rclient_write_ok.
      destruct Hiv as [Hiv|[Hiv|[HD Hiv]]].
      + left. unfold alloc_ceiling. clear -Hiv CEIL. lia.
      + right; right. eexists. split; [right; apply in_or_app; left; exact IDB|]. cbn. unfold SIZEOF_BUF. clear -Hiv. lia.
      + right; right. eexists. split; [right; apply in_or_app; left; exact (IDD HD)|]. cbn. clear -Hiv. lia.
    - eapply ystatics_munch; [exact YS| exact MU| exact WM|].
      eapply Forall_impl; [| exact OWN]. intros iv Hiv. unfold ownD in Hiv. unfold RY_CALLBACKS.
      destruct Hiv as [Hiv|[Hiv|[HD Hiv]]]; [clear -Hiv CEIL; lia| clear -Hiv RDB; lia| specialize (RDD HD); clear -Hiv RDD; lia]. }
  assert (ILX : In (mh_lid mh, mh_lexer mh, SIZEOF_LEXER) (lexer_blocks (mh_lid mh) (mh_lexer mh) (mh_lexbuf mh) (h_lexer h))) by (left; reflexivity).
  assert (ILB : In (mb_id (mh_lexbuf mh), mb_addr (mh_lexbuf mh), SIZEOF_BUF) (lexer_blocks (mh_lid mh) (mh_lexer mh) (mh_lexbuf mh) (h_lexer h))) by (right; left; reflexivity).
  assert (ILD : yb_data (lx_buf (h_lexer h)) <> None -> In (mb_did (mh_lexbuf mh), mb_data (mh_lexbuf mh), yb_len (lx_buf (h_lexer h))) (lexer_blocks (mh_lid mh) (mh_lexer mh) (mh_lexbuf mh) (h_lexer h))).
  { intros HD. unfold lexer_blocks, buf_blocks. right. destruct (yb_data (lx_buf (h_lexer h))); [| congruence]. right. left. reflexivity. }
  split.
  { split; [| split; [| split]].
    - destruct HS as ((pew & pad & HC & PW) & HB). split; [| cbn [h_set_decbuf h_bytesConsumed h_stack_size h_stack_blk h_parseError h_stack]; exact HB].
      exists pew, pad. split; [| exact PW]. eapply rw_cells_agree; [exact AG| | rewrite hand_cells_size; exact OUTH].
      unfold hand_cells, hand_head_cells in HC |- *. cbn [h_set_decbuf h_bytesConsumed h_stack_size h_parseError h_stack].
      replace (h_used (h_set_decbuf h b')) with (h_used h) by reflexivity. exact HC.
    - cbn [h_lexer h_set_decbuf]. eapply lexer_rep_agree; [exact AG| exact LXR| | |].
      + intros a Ha. apply (OUTL _ a ILX). cbn. exact Ha.
      + intros a Ha. apply (OUTL _ a ILB). cbn. exact Ha.
      + intros HD a Ha. apply (OUTL _ a (ILD HD)). cbn. exact Ha.
    - cbn [h_decbuf h_set_decbuf]. exact BR'.
    - eapply bs_rep_agree; [exact AG| | | cbn [h_stack_size h_set_decbuf]; replace (h_used (h_set_decbuf h b')) with (h_used h) by reflexivity; clear -B3; lia].
      + unfold RYajlRep.bs_rep in BSR |- *. cbn [h_stack_blk h_set_decbuf h_stack h_stack_size]. replace (h_used (h_set_decbuf h b')) with (h_used h) by reflexivity. exact BSR.
      + cbn [h_stack_size h_set_decbuf]. intros a Ha. apply (OUTT (mh_sid mh, mh_stack mh, h_stack_size h)); [left; reflexivity| cbn; exact Ha]. }
  split; [exact SAME|].
  split. { eapply ctx_rep_agree; [exact AG| exact CXR|]. intros a Ha. apply OUTS. clear -Ha SPC. unfold pCX, pSP in *. lia. }
  split.
  { eapply text_at_agree; [exact AG| exact (conj TXB (conj TXF (conj T0 T62)))|]. intros a Ha.
    destruct TB as [(bt & HIN & HB)|Z0]; [| unfold pLEN in Z0; clear -Ha Z0; lia].
    apply (OUTT bt a); [right; unfold TL; apply in_or_app; right; exact HIN| unfold pLEN in HB; clear -Ha HB; lia]. }
  split. { exists padw. eapply rw_cells_agree; [exact AG| exact FR|]. intros a Ha. apply OUTS. clear -Ha. lia. }
  split.
  { eapply rauxv_ok_frame; [exact AX| exact MU| exact WM|].
    eapply Forall_impl; [| exact OWN]. intros iv Hiv. unfold ownD in Hiv. unfold RAUXV_CELL.
    destruct Hiv as [Hiv|[Hiv|[HD Hiv]]]; [clear -Hiv CEIL LO SPC CXB CB0; unfold pSP, pCX in *; lia| clear -Hiv RDB CB0; lia| specialize (RDD HD); clear -Hiv RDD CB0; lia]. }
  split; [exact STK'|].
  split.
  { destruct ERR as [errv ERR]. exists errv. eapply rw_cells_agree; [exact AG| exact ERR|].
    rewrite (ry_errno_lit _ TP). unfold RERRNO. cbn. intros a Ha. apply OUTI. clear -Ha. lia. }
  split; [exact MI'|].
  split.
  { eapply ry_pres_trans; [exact PRES|]. eapply ryajl_pres_of_munch; [exact MU| exact WM|].
    intros a Ha Hc Hx. destruct Hc as [Hc|[[Hc _]|(b & Hb & Hr)]].
    - apply OUTS. unfold pSP in Hc. clear -Hc. lia.
    - apply OUTI. exact Hc.
    - apply (OUTT b a); [right; unfold TL; apply in_or_app; right; exact Hb| exact Hr]. }
  split; [exact SB1| exact LK0].
Qed.

(* [comment removed for export] *)
Lemma perm_decode : forall (hand : block) (LX D B LK' LK R : list block),
  Permutation.Permutation (D ++ LK' ++ ((hand :: LX) ++ B ++ LK ++ R)) ((hand :: LX ++ D ++ B) ++ (LK' ++ LK) ++ R).
Proof.
  intros. cbn [app]. rewrite <- !app_assoc.
  eapply Permutation.Permutation_trans.
  { rewrite (app_assoc D LK'). apply (Permutation.Permutation_app_swap_app (D ++ LK') (hand :: LX) (B ++ LK ++ R)). }
  cbn [app]. apply Permutation.perm_skip. rewrite <- !app_assoc. apply Permutation.Permutation_app_head. apply Permutation.Permutation_app_head.
  rewrite (app_assoc LK' B), (app_assoc B LK'). apply Permutation.Permutation_app_tail. apply Permutation.Permutation_app_comm.
Qed.

(* [comment removed for export] *)
Lemma decode_call : forall E m mo s LK h mh cx obw olw (rav : word) (i n : Z)
    (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s5v s6v s8v s10v : word),
  pok E -> pmem E m mo s LK h mh cx obw olw ->
  buf_inv (h_decbuf h) -> yb_used (h_decbuf h) = 0 ->
  0 <= i -> 0 <= n -> i + n <= pLEN E -> sbody_ix (p_txt E) i (i + n) ->
  (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m' mo' s' db' mbd' LK',
     yleaf (ystring_decode (h_decbuf h) (zslice (p_txt E) i n) n) db' ->
     mb_same (mh_decbuf mh) mbd' ->
     pmem E m' mo' s' (LK' ++ LK) (h_set_decbuf h db') (mh_set_decbuf mh mbd') cx obw olw ->
     realizes_cfg acfg rsegs (mkCfg (MS (mkR rav (p_sp E) (p_gp E) (p_tp E) t0' t1' t2' (wz (pH E)) (wz (pH E + 48)) a0' a1' a2' a3' a4' a5' a6' a7'
                                     (wz (pLEN E)) (wz (p_T E)) (wz (pH E + 32)) s5v s6v (wz 11) s8v (wz RY_JT_TOKVAL) s10v (wz RY_JT_STATE) t3' t4' t5' t6')
                                (p_F E) (ret_pc rav) (p_fc E) None m' (seg_rom rsegs)) mo') (p_K E)) ->
  realizes_cfg acfg rsegs (mkCfg (MS (mkR rav (p_sp E) (p_gp E) (p_tp E) t0 t1 t2 (wz (pH E)) (wz (pH E + 48)) (wz (mb_addr (mh_decbuf mh))) (wz (p_T E + i)) (wz n) a3 a4 a5 a6 a7
                                  (wz (pLEN E)) (wz (p_T E)) (wz (pH E + 32)) s5v s6v (wz 11) s8v (wz RY_JT_TOKVAL) s10v (wz RY_JT_STATE) t3 t4 t5 t6)
                             (p_F E) (wz RY_STRING_DECODE) (p_fc E) None m (seg_rom rsegs)) mo) (p_K E).
Proof.
  intros until s10v. intros OK PM DBI DBU I0 N0 IN SBX CONT.
  pose proof OK as OK'. destruct OK' as (K0 & LP & U0 & SB0 & L26 & TB & SPC & CXB & CEIL & LO & TP & B64 & PYR).
  pose proof PM as PM'. destruct PM' as (RY & HR & SAME & CXR & TXT & (padw & FR) & AX & STK & ERR & MI & PRES & SB1 & LK0).
  apply RYST_split in RY. destruct RY as [HK0 YS].
  pose proof HR as (HS & LXR & DBR & BSR). pose proof HS as ((pew & pad & HC & PW) & BC1 & BC2 & BC3 & BC4).
  pose proof SAME as (EID & EHA & ELID & ELX & ELBI & ELBA & EDBI & EDBA & ECX). unfold pCX, pH, pSP in *.
  rewrite <- EHA, <- ECX in *.
  pose proof (proj1 STK) as LO0.
  destruct (HK_blocks HK HKB _ _ _ _ HK0) as [RNG SEP].
  destruct ERR as [errv ERR].
  pose proof TXT as (TXB & TXF & T0 & T62). unfold pLEN in *.
  pose proof (rw_cells_bound _ _ _ _ HC) as HCB. rewrite hand_cells_size in HCB.
  (* [comment removed for export] *)
  set (REST' := ((mh_id mh, mh_addr mh, SIZEOF_HANDLE) :: lexer_blocks (mh_lid mh) (mh_lexer mh) (mh_lexbuf mh) (h_lexer h)) ++ bs_blocks (mh_sid mh) (mh_stack mh) h ++ LK ++ p_REST E).
  assert (PERM : Permutation.Permutation (yblocks mh h ++ LK ++ p_REST E) (buf_blocks (mh_decbuf mh) (h_decbuf h) ++ REST')).
  { unfold yblocks, REST'.
    eapply Permutation.Permutation_trans; [| apply (Permutation.Permutation_app_swap_app ((mh_id mh, mh_addr mh, SIZEOF_HANDLE) :: lexer_blocks (mh_lid mh) (mh_lexer mh) (mh_lexbuf mh) (h_lexer h)) (buf_blocks (mh_decbuf mh) (h_decbuf h)) (bs_blocks (mh_sid mh) (mh_stack mh) h ++ LK ++ p_REST E))].
    match goal with |- Permutation.Permutation ?a ?b => replace b with a; [apply Permutation.Permutation_refl|] end.
    cbn [app]. rewrite <- !app_assoc. reflexivity. }
  pose proof (HKP _ _ _ _ _ HK0 PERM) as HK1.
  pose proof (HK_blocks HK HKB _ _ _ _ HK1) as [RNG1 SEP1].
  assert (IH1 : In (mh_id mh, mh_addr mh, SIZEOF_HANDLE) REST') by (unfold REST'; left; reflexivity).
  pose proof HC as HC2. apply hand_cells_app in HC2. destruct HC2 as [HHD YAF].
  eapply (YSD REST' (mh_decbuf mh) (h_decbuf h) (mh_addr mh + 72) (p_T E + i) (zslice (p_txt E) i n) n (p_lo E) (p_B E) errv (p_K E));
    [exact K0 | apply RYST_split; split; [exact HK1| exact YS] | exact DBR | exact DBI | exact DBU | exact YAF
    | exists (mh_id mh, mh_addr mh, SIZEOF_HANDLE); split; [exact IH1| cbn; unfold SIZEOF_HANDLE; clear; lia]
    | apply pbytes_at_zslice; [exact TXB| clear -I0 N0 IN; lia]
    | apply pForall_zslice; exact TXF
    | symmetry; apply zslice_length; [exact I0| exact N0| exact IN]
    | clear -N0 I0 IN L26; lia
    | clear -T0 I0; lia
    | clear -T62 I0 N0 IN; lia
    | apply sbody_ix_slice; [exact I0| exact SBX]
    | | unfold REST'; clear -PYR LK0; yroom_solve | | reflexivity | reflexivity | reflexivity | ].
  { destruct TB as [(bt & HIN & HB)|Z0]; [left; exists bt; split; [unfold REST'; right; apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; exact HIN| clear -HB I0 N0 IN; lia]| right; clear -Z0 I0 N0 IN; lia]. }
  { split; [exact AX|]. split; [clear -SPC CXB; lia|]. split; [exact STK|]. split; [clear -CEIL; unfold alloc_ceiling; lia|].
    split; [clear -LO; unfold RY_DECODE_STACK, RY_BUF_APPEND_STACK, RY_WRAP_STACK; lia|]. split; [exact ERR|]. split; [exact MI| exact TP]. }
  cbv beta. intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 mo2 s2 db' mbd' LK' POST.
  destruct POST as ((MI2 & STK2 & ERR2 & AX2 & PR2) & YAF2 & YL & BR2 & MBS & BY2 & LKE & RY2).
  apply ry_pres_nil in PR2.
  apply (CONT t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 mo2 s2 db' mbd' LK' YL MBS).
  (* [comment removed for export] *)
  unfold RY_parse_kit.pmem, pCX, pH, pSP. rewrite <- ECX.
  apply RYST_split in RY2. destruct RY2 as [HK2 YS2].
  destruct MBS as [MBI MBA].
  assert (ISB : In (mh_sid mh, mh_stack mh, h_stack_size h) REST').
  { unfold REST'. right. apply in_or_app; right. apply in_or_app; left. unfold bs_blocks. unfold RYajlRep.bs_rep in BSR. destruct (h_stack_blk h); [left; reflexivity| congruence]. }
  split.
  { apply RYST_split. split; [| exact YS2]. eapply HKP; [exact HK2|].
    unfold yblocks, REST'. cbn [mh_set_decbuf mh_id mh_addr mh_lid mh_lexer mh_lexbuf mh_decbuf mh_sid mh_stack h_set_decbuf h_lexer h_decbuf].
    replace (bs_blocks (mh_sid mh) (mh_stack mh) (h_set_decbuf h db')) with (bs_blocks (mh_sid mh) (mh_stack mh) h) by reflexivity.
    apply perm_decode. }
  split.
  { split; [| split; [| split]].
    - split; [| cbn [h_set_decbuf h_bytesConsumed h_stack_size h_stack_blk h_parseError h_stack mh_set_decbuf mh_stack]; exact (conj BC1 (conj BC2 (conj BC3 BC4)))].
      exists pew, pad. split; [| exact PW]. apply (proj2 (hand_cells_app rsegs ryc m2 _ (mh_set_decbuf mh mbd') pew pad)).
      cbn [mh_set_decbuf mh_addr]. split; [| exact YAF2].
      eapply ypres_block; [exact PR2| | rewrite hand_head_cells_size; exists (mh_id mh, mh_addr mh, SIZEOF_HANDLE); split; [exact IH1| cbn; unfold SIZEOF_HANDLE; clear; lia]].
      unfold hand_head_cells in HHD |- *. cbn [h_set_decbuf h_bytesConsumed h_stack_size h_parseError h_stack mh_set_decbuf mh_ctx mh_lexer mh_decbuf mh_stack mh_addr].
      rewrite MBA. replace (h_used (h_set_decbuf h db')) with (h_used h) by reflexivity. exact HHD.
    - cbn [mh_set_decbuf mh_lexer mh_lexbuf mh_addr h_set_decbuf h_lexer]. eapply lexer_rep_pres_sub; [exact LXR| exact PR2|].
      intros x Hx. unfold REST'. right. apply in_or_app. left. exact Hx.
    - cbn [mh_set_decbuf mh_decbuf mh_addr h_set_decbuf h_decbuf]. exact BR2.
    - cbn [mh_set_decbuf mh_stack]. unfold RYajlRep.bs_rep in BSR |- *. cbn [h_stack_blk h_set_decbuf h_stack h_stack_size]. destruct (h_stack_blk h); [| congruence].
      destruct BSR as (NZ & junk & SC). split; [exact NZ|]. exists junk. replace (h_used (h_set_decbuf h db')) with (h_used h) by reflexivity.
      eapply ypres_block; [exact PR2| exact SC|]. exists (mh_sid mh, mh_stack mh, h_stack_size h). split; [exact ISB|]. cbn [cells_size csize Nat.add blk_addr blk_size fst snd]. clear -BC3. lia. }
  split. { unfold mh_same. cbn [mh_set_decbuf mh_id mh_addr mh_lid mh_lexer mh_lexbuf mh_decbuf mh_sid mh_stack mh_ctx]. rewrite MBI, MBA. exact SAME. }
  split. { eapply ctx_rep_agree; [apply rheap_pres_agree; exact PR2| exact CXR|]. intros a Ha. left. clear -Ha SPC. lia. }
  split. { eapply ypres_text; [exact PR2| exact TXT|]. destruct TB as [(bt & HIN & HB)|Z0]; [left; exists bt; split; [unfold REST'; right; apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; exact HIN| exact HB]| right; exact Z0]. }
  split. { exists padw. eapply ypres_frame; [exact PR2| exact FR| clear; lia]. }
  split; [exact AX2|]. split; [exact STK2|]. split; [exact ERR2|]. split; [exact MI2|].
  split.
  { eapply ry_pres_trans; [exact PRES|]. apply ry_pres_of_rheap_pres. eapply rheap_pres_weaken; [exact PR2| clear; lia|].
    intros b Hb. unfold REST'. right. apply in_or_app; right. apply in_or_app; right. apply in_or_app; right. exact Hb. }
  split; [exact SB1| rewrite LKE, LK0; reflexivity].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma decbuf_facts : forall E m mo s LK h mh cx obw olw,
  pok E -> pmem E m mo s LK h mh cx obw olw ->
  (0 < mb_addr (mh_decbuf mh) /\ mb_addr (mh_decbuf mh) + 32 <= (Z.max 0x7fff80000000 (Z.min 0x800000000000 rc_sp) - 8388608)
     /\ (mb_addr (mh_decbuf mh) + 32 <= 0x10000 \/ 0x56000 <= mb_addr (mh_decbuf mh))
     /\ (mh_addr mh + 104 <= mb_addr (mh_decbuf mh) \/ mb_addr (mh_decbuf mh) + 32 <= mh_addr mh)
     /\ (mb_addr (mh_decbuf mh) + 32 <= mh_stack mh \/ mh_stack mh + h_stack_size h <= mb_addr (mh_decbuf mh)))
  /\ (yb_data (h_decbuf h) <> None ->
     1 <= yb_len (h_decbuf h) /\ 0 < mb_data (mh_decbuf mh) /\ mb_data (mh_decbuf mh) + yb_len (h_decbuf h) <= (Z.max 0x7fff80000000 (Z.min 0x800000000000 rc_sp) - 8388608)
     /\ (mb_data (mh_decbuf mh) + yb_len (h_decbuf h) <= 0x10000 \/ 0x56000 <= mb_data (mh_decbuf mh))
     /\ (mb_addr (mh_decbuf mh) + 32 <= mb_data (mh_decbuf mh) \/ mb_data (mh_decbuf mh) + yb_len (h_decbuf h) <= mb_addr (mh_decbuf mh))
     /\ (mh_addr mh + 104 <= mb_data (mh_decbuf mh) \/ mb_data (mh_decbuf mh) + yb_len (h_decbuf h) <= mh_addr mh)
     /\ (mb_data (mh_decbuf mh) + yb_len (h_decbuf h) <= mh_stack mh \/ mh_stack mh + h_stack_size h <= mb_data (mh_decbuf mh))).
Proof.
  intros until olw. intros OK PM.
  destruct OK as (K0 & LP & U0 & SB0 & L26 & TB & SPC & CXB & CEIL & LO & TP & B64 & PYR).
  destruct PM as (RY & HR & SAME & CXR & TXT & (padw & FR) & AX & STK & ERR & MI & PRES & SB1 & LK0).
  apply RYST_split in RY. destruct RY as [HK0 YS]. destruct (HK_blocks HK HKB _ _ _ _ HK0) as [RNG SEP].
  destruct HR as (HS & LXR & DBR & BSR).
  rewrite (yblocks_mid mh h LK (p_REST E) SB1) in RNG, SEP.
  cbn [all_sep] in SEP. destruct SEP as [SEPH SEPT].
  set (MID := mid_blocks mh h) in *.
  assert (IDB : In (mb_id (mh_decbuf mh), mb_addr (mh_decbuf mh), SIZEOF_BUF) MID).
  { unfold MID, mid_blocks. apply in_or_app. right. left. reflexivity. }
  assert (IDD : yb_data (h_decbuf h) <> None -> In (mb_did (mh_decbuf mh), mb_data (mh_decbuf mh), yb_len (h_decbuf h)) MID).
  { intros HD. unfold MID, mid_blocks, buf_blocks. apply in_or_app. right. destruct (yb_data (h_decbuf h)); [| congruence]. right. left. reflexivity. }
  assert (IST : In (mh_sid mh, mh_stack mh, h_stack_size h) ((mh_sid mh, mh_stack mh, h_stack_size h) :: LK ++ p_REST E)) by (left; reflexivity).
  pose proof (all_range_In _ _ RNG ltac:(right; apply in_or_app; left; exact IDB)) as R1.
  pose proof (sep_from_In _ _ _ SEPH ltac:(apply in_or_app; left; exact IDB)) as H1.
  pose proof (all_sep_app12 _ _ _ _ SEPT IDB IST) as S1.
  unfold rblock_range, alloc_ceiling, bsep, SIZEOF_BUF, SIZEOF_HANDLE in R1, H1, S1. cbn [blk_addr blk_size fst snd] in R1, H1, S1.
  split; [clear -R1 H1 S1; lia|].
  intros HD. specialize (IDD HD).
  pose proof (all_range_In _ _ RNG ltac:(right; apply in_or_app; left; exact IDD)) as R2.
  pose proof (sep_from_In _ _ _ SEPH ltac:(apply in_or_app; left; exact IDD)) as H2.
  pose proof (all_sep_app12 _ _ _ _ SEPT IDD IST) as S2.
  assert (D12 : bsep (mb_id (mh_decbuf mh), mb_addr (mh_decbuf mh), SIZEOF_BUF) (mb_did (mh_decbuf mh), mb_data (mh_decbuf mh), yb_len (h_decbuf h))).
  { assert (SEPM : all_sep (MID ++ (mh_sid mh, mh_stack mh, h_stack_size h) :: LK ++ p_REST E)) by exact SEPT.
    unfold MID, mid_blocks in SEPM. rewrite <- app_assoc in SEPM. apply all_sep_app_r in SEPM.
    unfold buf_blocks in SEPM. destruct (yb_data (h_decbuf h)); [| congruence]. cbn [all_sep sep_from app] in SEPM.
    destruct SEPM as [[D _] _]. exact D. }
  destruct DBR as (_ & BD & _). unfold RYajlRep.buf_data in BD. destruct (yb_data (h_decbuf h)); [| congruence]. destruct BD as [UL _].
  unfold rblock_range, alloc_ceiling, bsep, SIZEOF_BUF, SIZEOF_HANDLE in R2, H2, S2, D12. cbn [blk_addr blk_size fst snd] in R2, H2, S2, D12.
  clear -R2 H2 S2 D12 UL. lia.
Qed.

End S.
End RC__1.
