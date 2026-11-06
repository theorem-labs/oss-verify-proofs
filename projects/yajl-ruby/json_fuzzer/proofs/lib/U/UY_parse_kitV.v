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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Image ZBridge SysStep SFModel SFW1_lemmas InitMem Arr FP.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Images.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import PortShim.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.U Require Import UMallocRep UMallocTree UMalloc_iface.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RYajlRep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.U Require Import UYajlAlign UYajl_iface.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RY_lib.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.U Require Import UY_rz UY_kit2 UY_parse_kit UY_parse_kitJ UY_parse_kitD.
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
Notation buf_rep := (buf_rep usegs).
Notation buf_struct := (buf_struct usegs).
Notation buf_data := (buf_data usegs).
Notation lexer_rep := (lexer_rep usegs).
Notation hand_rep := (hand_rep usegs ryc).
Notation hand_struct := (hand_struct usegs ryc).
Notation bs_rep := (bs_rep usegs).
Notation ctx_rep := (ctx_rep usegs).
Notation text_at := (text_at usegs).
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
Definition ownL (E : penv) (mh : mhand) (h : yhandle) (iv : Z * Z) : Prop :=
  ownA E mh h iv
  \/ (mh_lexer mh <= fst iv /\ snd iv <= mh_lexer mh + 48)
  \/ (mb_addr (mh_lexbuf mh) <= fst iv /\ snd iv <= mb_addr (mh_lexbuf mh) + 32).

Lemma ownL_outside : forall E mh h W a,
  Forall (ownL E mh h) W ->
  (a < mh_addr mh \/ mh_addr mh + 72 <= a) -> (a < mh_stack mh \/ mh_stack mh + h_stack_size h <= a) ->
  (a < pCX E \/ pCX E + 8 <= a) -> (a < p_lo E \/ pSP E + 160 <= a) ->
  (a < mh_lexer mh \/ mh_lexer mh + 48 <= a) -> (a < mb_addr (mh_lexbuf mh) \/ mb_addr (mh_lexbuf mh) + 32 <= a) ->
  outside W a.
Proof.
  intros E mh h W a HF H1 H2 H3 H4 H5 H6. induction HF as [| [lo hi] W HO HF IH]; [exact I|].
  cbn. split; [| exact IH]. unfold ownL, ownA in HO. cbn [fst snd] in HO. lia.
Qed.

Lemma pmem_updL : forall E m m' mo s LK h mh cx obw olw lx' cx' obw' olw' W,
  pok E -> pmem E m mo s LK h mh cx obw olw ->
  munch W m m' -> wmono usegs m m' -> mem_inv usegs m' ->
  Forall (ownL E mh h) W ->
  yb_data (lx_buf lx') = yb_data (lx_buf (h_lexer h)) -> yb_len (lx_buf lx') = yb_len (lx_buf (h_lexer h)) ->
  hand_struct m' (h_set_lexer h lx') mh -> lexer_rep m' (mh_lexer mh) lx' (mh_lexbuf mh) (pH E + 72) ->
  bs_rep m' (mh_stack mh) h -> ctx_rep m' (pCX E) cx' ->
  (exists padw, yparse_frame m' (p_sp E) (p_ra E) (p_s0 E) (p_s1 E) (p_s2 E) (p_s3 E) (p_s4 E) (p_s5 E) (p_s6 E) (p_s7 E)
                              (p_s8 E) (p_s9 E) (p_s10 E) (p_s11 E) (reg_get (p_F E) 8%bv) padw obw' olw') ->
  stk usegs m' (p_lo E) (pSP E) ->
  pmem E m' mo s LK (h_set_lexer h lx') mh cx' obw' olw'.
Proof.
  intros until W. intros OK PM MU WM MI' OWN ED EL HS' LXR' BS' CX' FR' STK'.
  pose proof (pmem_ranges _ HKB _ _ _ _ _ _ _ _ _ _ OK PM) as (I1 & I2 & R1 & R2 & S12 & B1 & B2 & B3).
  destruct OK as (K0 & LP & U0 & SB0 & L26 & TB & SPC & CXB & CEIL & LO & TP & B64 & AL16 & AL4 & PYR).
  destruct PM as (RY & HR & SAME & CXR & TXT & (padw & FR) & AX & STK & ERR & MI & PRES & SB1 & LK0).
  apply RYST_split in RY. destruct RY as [HK0 YS]. destruct (HK_blocks HK HKB _ _ _ _ HK0) as [RNG SEP].
  destruct HR as (HS & LXR & DBR & BSR).
  pose proof (proj1 STK) as LO0. unfold pSP in LO0, STK, STK', LO.
  pose proof AX as (av & x3 & x4 & x5 & x16 & x6 & x11 & x12 & x23 & rnd & _ & _ & _ & CB0 & _). unfold alloc_ceiling in CB0.
  pose proof SAME as (_ & EHA & _). unfold pH in LXR'. rewrite <- EHA in LXR'.
  pose proof (munch_agree _ _ _ MU WM) as AG.
  destruct TXT as (TXB & TXF & T0 & T62).
  rewrite (yblocks_mid mh h LK (p_REST E) SB1) in RNG, SEP, HK0.
  set (MID := mid_blocks mh h) in *. set (TL := LK ++ p_REST E) in *.
  cbn [all_sep] in SEP. destruct SEP as [SEPH SEPT].
  assert (ILX : In (mh_lid mh, mh_lexer mh, SIZEOF_LEXER) (lexer_blocks (mh_lid mh) (mh_lexer mh) (mh_lexbuf mh) (h_lexer h))) by (left; reflexivity).
  assert (ILB : In (mb_id (mh_lexbuf mh), mb_addr (mh_lexbuf mh), SIZEOF_BUF) (lexer_blocks (mh_lid mh) (mh_lexer mh) (mh_lexbuf mh) (h_lexer h))) by (right; left; reflexivity).
  pose proof (all_range_In _ _ RNG ltac:(right; apply in_or_app; left; unfold MID, mid_blocks; apply in_or_app; left; exact ILX)) as RL.
  pose proof (all_range_In _ _ RNG ltac:(right; apply in_or_app; left; unfold MID, mid_blocks; apply in_or_app; left; exact ILB)) as RLB.
  unfold rblock_range, alloc_ceiling, SIZEOF_LEXER, SIZEOF_BUF in RL, RLB. cbn [blk_addr blk_size fst snd] in RL, RLB.
  (* [comment removed for export] *)
  assert (OUTy : forall y a, In y ((mh_id mh, mh_addr mh, SIZEOF_HANDLE) :: MID ++ (mh_sid mh, mh_stack mh, h_stack_size h) :: TL) ->
            bsep (mh_id mh, mh_addr mh, SIZEOF_HANDLE) y ->
            (blk_addr y + blk_size y <= mh_stack mh \/ mh_stack mh + h_stack_size h <= blk_addr y) ->
            bsep (mh_lid mh, mh_lexer mh, SIZEOF_LEXER) y -> bsep (mb_id (mh_lexbuf mh), mb_addr (mh_lexbuf mh), SIZEOF_BUF) y ->
            blk_addr y <= a < blk_addr y + blk_size y -> outside W a).
  { intros y a Hy D1 D2 D3 D4 Ha. pose proof (all_range_In _ _ RNG Hy) as Ry. unfold rblock_range, alloc_ceiling in Ry.
    unfold bsep, SIZEOF_HANDLE, SIZEOF_LEXER, SIZEOF_BUF in D1, D3, D4. cbn [blk_addr blk_size fst snd] in D1, D3, D4.
    eapply ownL_outside; [exact OWN| clear -Ha D1; lia| clear -Ha D2; lia| clear -Ha Ry CEIL LO SPC; unfold pSP, pCX in *; lia| clear -Ha Ry CEIL; lia| clear -Ha D3; lia| clear -Ha D4; lia]. }
  (* [comment removed for export] *)
  assert (OUTM : forall y a, In y (match yb_data (lx_buf (h_lexer h)) with Some _ => [(mb_did (mh_lexbuf mh), mb_data (mh_lexbuf mh), yb_len (lx_buf (h_lexer h)))] | None => [] end
                                ++ buf_blocks (mh_decbuf mh) (h_decbuf h)) \/ In y TL ->
            blk_addr y <= a < blk_addr y + blk_size y -> outside W a).
  { intros y a Hy Ha.
    assert (EMID : MID = [(mh_lid mh, mh_lexer mh, SIZEOF_LEXER); (mb_id (mh_lexbuf mh), mb_addr (mh_lexbuf mh), SIZEOF_BUF)]
                         ++ (match yb_data (lx_buf (h_lexer h)) with Some _ => [(mb_did (mh_lexbuf mh), mb_data (mh_lexbuf mh), yb_len (lx_buf (h_lexer h)))] | None => [] end
                             ++ buf_blocks (mh_decbuf mh) (h_decbuf h))).
    { unfold MID, mid_blocks, lexer_blocks, buf_blocks. cbn [app]. try rewrite <- app_assoc. reflexivity. }
    assert (SEPM : all_sep (([(mh_lid mh, mh_lexer mh, SIZEOF_LEXER); (mb_id (mh_lexbuf mh), mb_addr (mh_lexbuf mh), SIZEOF_BUF)]
                            ++ (match yb_data (lx_buf (h_lexer h)) with Some _ => [(mb_did (mh_lexbuf mh), mb_data (mh_lexbuf mh), yb_len (lx_buf (h_lexer h)))] | None => [] end
                                ++ buf_blocks (mh_decbuf mh) (h_decbuf h))) ++ (mh_sid mh, mh_stack mh, h_stack_size h) :: TL)).
    { rewrite <- EMID. exact SEPT. }
    rewrite <- app_assoc in SEPM.
    assert (HyIn : In y ((mh_id mh, mh_addr mh, SIZEOF_HANDLE) :: MID ++ (mh_sid mh, mh_stack mh, h_stack_size h) :: TL)).
    { right. apply in_or_app. destruct Hy as [Hy|Hy]; [left; rewrite EMID; apply in_or_app; right; exact Hy| right; right; exact Hy]. }
    apply (OUTy y a HyIn).
    - apply (sep_from_In _ _ _ SEPH). apply in_or_app. destruct Hy as [Hy|Hy]; [left; rewrite EMID; apply in_or_app; right; exact Hy| right; right; exact Hy].
    - destruct Hy as [Hy|Hy].
      + pose proof (all_sep_mid _ _ _ _ SEPT ltac:(rewrite EMID; apply in_or_app; right; exact Hy)) as X. unfold bsep in X. cbn [blk_addr blk_size fst snd] in X. clear -X. lia.
      + pose proof (all_sep_tail _ _ _ _ SEPT Hy) as X. unfold bsep in X. cbn [blk_addr blk_size fst snd] in X. clear -X. lia.
    - destruct Hy as [Hy|Hy].
      + exact (all_sep_app12 _ _ _ _ SEPM ltac:(left; reflexivity) ltac:(apply in_or_app; left; exact Hy)).
      + exact (all_sep_app12 _ _ _ _ SEPM ltac:(left; reflexivity) ltac:(apply in_or_app; right; right; exact Hy)).
    - destruct Hy as [Hy|Hy].
      + exact (all_sep_app12 _ _ _ _ SEPM ltac:(right; left; reflexivity) ltac:(apply in_or_app; left; exact Hy)).
      + exact (all_sep_app12 _ _ _ _ SEPM ltac:(right; left; reflexivity) ltac:(apply in_or_app; right; right; exact Hy)).
    - exact Ha. }
  assert (OUTI : forall a, 0x24000 <= a < 0x57000 -> outside W a).
  { intros a Ha. eapply ownL_outside; [exact OWN| clear -Ha R1; lia| clear -Ha R2; lia| clear -Ha CEIL LO SPC; unfold pCX, pSP in *; lia| clear -Ha CEIL; lia| clear -Ha RL; lia| clear -Ha RLB; lia]. }
  split.
  { apply RYST_split. rewrite (yblocks_mid mh (h_set_lexer h lx') LK (p_REST E)) by exact SB1.
    replace (mid_blocks mh (h_set_lexer h lx')) with MID by (unfold MID, mid_blocks, lexer_blocks, buf_blocks; cbn [h_lexer h_decbuf h_set_lexer]; rewrite ED, EL; reflexivity).
    cbn [h_stack_size h_set_lexer]. fold TL. split.
    - eapply HKF; [exact HK0| exact MU| exact WM|].
      eapply Forall_impl; [| exact OWN]. intros iv Hiv. unfold ownL, ownA in Hiv. unfold rclient_write_ok.
      destruct Hiv as [[Hiv|[Hiv|[Hiv|Hiv]]]|[Hiv|Hiv]].
      + right; right. eexists. split; [left; reflexivity|]. cbn. unfold SIZEOF_HANDLE. clear -Hiv. lia.
      + right; right. eexists. split; [right; apply in_or_app; right; left; reflexivity|]. cbn. clear -Hiv. lia.
      + left. unfold alloc_ceiling. clear -Hiv CEIL LO SPC. unfold pCX, pSP in *. lia.
      + left. unfold alloc_ceiling. clear -Hiv CEIL. lia.
      + right; right. eexists. split; [right; apply in_or_app; left; unfold MID, mid_blocks; apply in_or_app; left; exact ILX|]. cbn. unfold SIZEOF_LEXER. clear -Hiv. lia.
      + right; right. eexists. split; [right; apply in_or_app; left; unfold MID, mid_blocks; apply in_or_app; left; exact ILB|]. cbn. unfold SIZEOF_BUF. clear -Hiv. lia.
    - eapply ystatics_munch; [exact YS| exact MU| exact WM|].
      eapply Forall_impl; [| exact OWN]. intros iv Hiv. unfold ownL, ownA in Hiv. unfold RY_CALLBACKS.
      clear -Hiv R1 R2 RL RLB CEIL LO SPC. unfold pCX, pSP in *. lia. }
  split.
  { split; [exact HS'|]. split; [| split; [| cbn [h_stack_size h_stack h_set_lexer]]].
    - cbn [h_lexer h_set_lexer]. exact LXR'.
    - cbn [h_decbuf h_set_lexer]. eapply buf_rep_agree; [exact AG| exact DBR| |].
      + intros a Ha. apply (OUTM (mb_id (mh_decbuf mh), mb_addr (mh_decbuf mh), SIZEOF_BUF)); [left; apply in_or_app; right; left; reflexivity| cbn; exact Ha].
      + intros HD a Ha. apply (OUTM (mb_did (mh_decbuf mh), mb_data (mh_decbuf mh), yb_len (h_decbuf h))); [| cbn; exact Ha].
        left. apply in_or_app. right. unfold buf_blocks. destruct (yb_data (h_decbuf h)); [| congruence]. right. left. reflexivity.
    - unfold RYajlRep.bs_rep in BS' |- *. cbn [h_stack_blk h_set_lexer h_stack h_stack_size]. replace (h_used (h_set_lexer h lx')) with (h_used h) by reflexivity. exact BS'. }
  split; [exact SAME|]. split; [exact CX'|].
  split.
  { eapply text_at_agree; [exact AG| exact (conj TXB (conj TXF (conj T0 T62)))|]. intros a Ha.
    destruct TB as [(bt & HIN & HB)|Z0]; [| unfold pLEN in Z0; clear -Ha Z0; lia].
    apply (OUTM bt a); [right; unfold TL; apply in_or_app; right; exact HIN| unfold pLEN in HB; clear -Ha HB; lia]. }
  split; [exact FR'|].
  split.
  { eapply rauxv_ok_frame; [exact AX| exact MU| exact WM|].
    eapply Forall_impl; [| exact OWN]. intros iv Hiv. unfold ownL, ownA in Hiv. unfold RAUXV_CELL.
    clear -Hiv R1 R2 RL RLB CEIL LO SPC CXB CB0. unfold pCX, pSP in *. lia. }
  split; [exact STK'|].
  split.
  { destruct ERR as [errv ERR]. exists errv. eapply rw_cells_agree; [exact AG| exact ERR|].
    rewrite (ry_errno_lit _ TP). unfold RERRNO. cbn. intros a Ha. apply OUTI. clear -Ha. lia. }
  split; [exact MI'|].
  split.
  { eapply ry_pres_trans; [exact PRES|]. eapply ryajl_pres_of_munch; [exact MU| exact WM|].
    intros a Ha Hc Hx. destruct Hc as [Hc|[[Hc _]|(b & Hb & Hr)]].
    - eapply ownL_outside; [exact OWN| clear -Hc R1 CEIL LO SPC; unfold pSP in *; lia| clear -Hc R2 CEIL LO SPC; unfold pSP in *; lia| | clear -Hc; unfold pSP in *; lia
                           | clear -Hc RL CEIL LO SPC; unfold pSP in *; lia| clear -Hc RLB CEIL LO SPC; unfold pSP in *; lia].
      assert (~ (pCX E <= a < pCX E + 8)) by (intros X; apply Hx; left; exact X). clear -H. lia.
    - apply OUTI. exact Hc.
    - apply (OUTM b a); [right; unfold TL; apply in_or_app; right; exact Hb| exact Hr]. }
  split; [exact SB1| exact LK0].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma pmem_push : forall E m m' mo s LK h mh cx obw olw stp junk,
  pok E -> pmem E m mo s LK h mh cx obw olw -> h_used h < h_stack_size h ->
  munch [(mh_addr mh + 60, mh_addr mh + 64); (mh_stack mh + h_used h, mh_stack mh + h_used h + 1)] m m' -> wmono usegs m m' -> mem_inv usegs m' ->
  (exists pew pad, rw_cells usegs m' (mh_addr mh) (hand_cells ryc (h_set_stack h (stp :: h_stack h)) mh pew pad) /\ perr_word ryc (h_parseError h) pew) ->
  u8arr usegs m' (mh_stack mh) (upd (zbytes (stack_bytes (h_stack h)) ++ junk) (Z.to_nat (h_used h)) (Z_to_bv 8 (state_code stp))) ->
  length junk = Z.to_nat (h_stack_size h - h_used h) ->
  rw_cells usegs m' (pCX E) (ctx_cells cx) ->
  (exists padw, yparse_frame m' (p_sp E) (p_ra E) (p_s0 E) (p_s1 E) (p_s2 E) (p_s3 E) (p_s4 E) (p_s5 E) (p_s6 E) (p_s7 E)
                              (p_s8 E) (p_s9 E) (p_s10 E) (p_s11 E) (reg_get (p_F E) 8%bv) padw obw olw) ->
  stk usegs m' (p_lo E) (pSP E) ->
  pmem E m' mo s LK (h_set_stack h (stp :: h_stack h)) mh cx obw olw.
Proof.
  intros until junk. intros OK PM UL MU WM MI' (pew & pad & HC' & PW) ARR' L2 CXC' FR' STK'.
  pose proof (pmem_ranges _ HKB _ _ _ _ _ _ _ _ _ _ OK PM) as (I1 & I2 & R1 & R2 & S12 & B1 & B2 & B3).
  pose proof PM as (RY & HR & SAME & CXR & _). destruct CXR as [_ CXB2].
  pose proof HR as ((_ & _ & _ & _ & BC4) & _ & _ & BSR). unfold RYajlRep.bs_rep in BSR.
  destruct (h_stack_blk h) as [sbk|] eqn:HSB; [| destruct PM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SB1 & _); congruence].
  destruct BSR as [SBNZ _].
  assert (EU : h_used (h_set_stack h (stp :: h_stack h)) = h_used h + 1) by (unfold h_used; cbn [h_stack h_set_stack]; unfold zlength; cbn [length]; lia).
  pose proof (u8arr_bound _ _ _ _ ARR') as ARB. rewrite upd_length, length_app, zbytes_length, stack_bytes_length in ARB.
  eapply pmem_updA; [exact HKF| exact HKB| exact OK| exact PM| exact MU| exact WM| exact MI'| | reflexivity| reflexivity| reflexivity| reflexivity| | | split; [exact CXC'| exact CXB2]| exact FR'| exact STK'].
  - constructor; [| constructor; [| constructor]]; unfold ownA; cbn [fst snd]; [clear; lia| clear -B3 UL; lia].
  - split; [| cbn [h_set_stack h_bytesConsumed h_stack_size h_stack_blk h_parseError]; rewrite HSB, EU; repeat split; try (clear -B1 B2 B3 UL; lia); intros; congruence].
    exists pew, pad. split; [exact HC'| exact PW].
  - unfold RYajlRep.bs_rep. cbn [h_stack_blk h_set_stack h_stack h_stack_size]. rewrite HSB, EU. split; [exact SBNZ|].
    destruct junk as [|j0 junk']; [cbn [length] in L2; clear -L2 B3 UL; lia|].
    exists junk'.
    apply (CB2_of_u8arr usegs m' (mh_stack mh) (zbytes (stack_bytes (stp :: h_stack h))) junk').
    + revert ARR'. rewrite stack_bytes_cons, zbytes_app. cbn [zbytes map]. rewrite <- app_assoc. cbn [app].
      rewrite (upd_app_len _ _ _ _ _) by (rewrite zbytes_length, stack_bytes_length; unfold h_used, zlength; clear; lia).
      intros ARR'. exact ARR'.
    + rewrite zbytes_length, stack_bytes_length. cbn [length]. unfold h_used, zlength. clear. lia.
    + cbn [length] in L2. clear -L2 B3 UL. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma lexer_facts : forall E m mo s LK h mh cx obw olw,
  pok E -> pmem E m mo s LK h mh cx obw olw ->
  (0 < mh_lexer mh /\ mh_lexer mh + 48 <= (Z.max 0x7fff80000000 (Z.min 0x800000000000 rc_sp) - 8388608) /\ (mh_lexer mh + 48 <= 0x10000 \/ 0x57000 <= mh_lexer mh))
  /\ (0 < mb_addr (mh_lexbuf mh) /\ mb_addr (mh_lexbuf mh) + 32 <= (Z.max 0x7fff80000000 (Z.min 0x800000000000 rc_sp) - 8388608) /\ (mb_addr (mh_lexbuf mh) + 32 <= 0x10000 \/ 0x57000 <= mb_addr (mh_lexbuf mh)))
  /\ (mh_addr mh + 104 <= mh_lexer mh \/ mh_lexer mh + 48 <= mh_addr mh)
  /\ (mh_addr mh + 104 <= mb_addr (mh_lexbuf mh) \/ mb_addr (mh_lexbuf mh) + 32 <= mh_addr mh)
  /\ (mh_lexer mh + 48 <= mb_addr (mh_lexbuf mh) \/ mb_addr (mh_lexbuf mh) + 32 <= mh_lexer mh)
  /\ (mh_lexer mh + 48 <= mh_stack mh \/ mh_stack mh + h_stack_size h <= mh_lexer mh)
  /\ (mb_addr (mh_lexbuf mh) + 32 <= mh_stack mh \/ mh_stack mh + h_stack_size h <= mb_addr (mh_lexbuf mh)).
Proof.
  intros until olw. intros OK PM.
  destruct OK as (K0 & LP & U0 & SB0 & L26 & TB & SPC & CXB & CEIL & LO & TP & B64 & AL16 & AL4 & PYR).
  destruct PM as (RY & HR & SAME & CXR & TXT & (padw & FR) & AX & STK & ERR & MI & PRES & SB1 & LK0).
  apply RYST_split in RY. destruct RY as [HK0 YS]. destruct (HK_blocks HK HKB _ _ _ _ HK0) as [RNG SEP].
  rewrite (yblocks_mid mh h LK (p_REST E) SB1) in RNG, SEP.
  cbn [all_sep] in SEP. destruct SEP as [SEPH SEPT].
  set (MID := mid_blocks mh h) in *.
  assert (ILX : In (mh_lid mh, mh_lexer mh, SIZEOF_LEXER) MID) by (unfold MID, mid_blocks, lexer_blocks; left; reflexivity).
  assert (ILB : In (mb_id (mh_lexbuf mh), mb_addr (mh_lexbuf mh), SIZEOF_BUF) MID) by (unfold MID, mid_blocks, lexer_blocks, buf_blocks; right; left; reflexivity).
  assert (IST : In (mh_sid mh, mh_stack mh, h_stack_size h) ((mh_sid mh, mh_stack mh, h_stack_size h) :: LK ++ p_REST E)) by (left; reflexivity).
  pose proof (all_range_In _ _ RNG ltac:(right; apply in_or_app; left; exact ILX)) as R1.
  pose proof (all_range_In _ _ RNG ltac:(right; apply in_or_app; left; exact ILB)) as R2.
  pose proof (sep_from_In _ _ _ SEPH ltac:(apply in_or_app; left; exact ILX)) as H1.
  pose proof (sep_from_In _ _ _ SEPH ltac:(apply in_or_app; left; exact ILB)) as H2.
  pose proof (all_sep_app12 _ _ _ _ SEPT ILX IST) as S1.
  pose proof (all_sep_app12 _ _ _ _ SEPT ILB IST) as S2.
  assert (L12 : bsep (mh_lid mh, mh_lexer mh, SIZEOF_LEXER) (mb_id (mh_lexbuf mh), mb_addr (mh_lexbuf mh), SIZEOF_BUF)).
  { assert (SEPM : all_sep (MID ++ (mh_sid mh, mh_stack mh, h_stack_size h) :: LK ++ p_REST E)) by exact SEPT.
    unfold MID, mid_blocks, lexer_blocks in SEPM. cbn [all_sep sep_from app] in SEPM. destruct SEPM as [[D _] _]. exact D. }
  unfold rblock_range, alloc_ceiling, bsep, SIZEOF_BUF, SIZEOF_LEXER, SIZEOF_HANDLE in R1, R2, H1, H2, S1, S2, L12.
  cbn [blk_addr blk_size fst snd] in R1, R2, H1, H2, S1, S2, L12.
  clear -R1 R2 H1 H2 S1 S2 L12. lia.
Qed.

End S.
End RC__1.
