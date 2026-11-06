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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import InitMem SysStep SFW1_lemmas Arr.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Agent Require Import MallocBlocks.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.MS Require Import MallocRep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim YajlBase YajlBuf YajlLeaf YajlLex YajlDecode YajlParser YajlFactsLex YajlFactsBuf YajlFactsDecode.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RY_lib RY_lex_top1.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA AImages LazyModel NodesA Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import B_iface BI_shadow BYajlRep BYajl_iface BYajlAlign BY_ubkit BY_rz BY_lex_rdck BY_lex_kit BY_lex_comment BY_lex_number2 BY_lex_string2 BY_lex_main1 BY_lex_main2 BY_lex_main BY_lex_top1 BY_lex_top2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Open Scope yprog_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac aceil := first [pose proof alloc_ceiling_range as CEILB | idtac].
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma ahand_split : forall m h mh pew pad,
  rw_cells bsegs m (mh_addr mh) (hand_cells ayc h mh pew pad) <->
  (rw_cells bsegs m (mh_addr mh) [C8 (wz (yc_callbacks ayc)); C8 (wz (mh_ctx mh)); C8 (wz (mh_lexer mh)); C8 pew]
   /\ rw_cells bsegs m (mh_addr mh + 32) [C4 (wz (h_bytesConsumed h))]
   /\ rw_cells bsegs m (mh_addr mh + 36) [C4 pad; C8 (wz (mb_addr (mh_decbuf mh))); C8 (wz (mh_stack mh)); C4 (wz (h_stack_size h)); C4 (wz (h_used h)); C8 (wz (mh_addr mh + 72))]
   /\ rw_cells bsegs m (mh_addr mh + 72) (alloc_cells ayc)).
Proof. aceil.
  intros m h mh pew pad. unfold hand_cells, hand_head_cells.
  change ([C8 (wz (yc_callbacks ayc)); C8 (wz (mh_ctx mh)); C8 (wz (mh_lexer mh)); C8 pew; C4 (wz (h_bytesConsumed h)); C4 pad;
           C8 (wz (mb_addr (mh_decbuf mh))); C8 (wz (mh_stack mh)); C4 (wz (h_stack_size h)); C4 (wz (h_used h)); C8 (wz (mh_addr mh + 72))] ++ alloc_cells ayc)
    with ((([C8 (wz (yc_callbacks ayc)); C8 (wz (mh_ctx mh)); C8 (wz (mh_lexer mh)); C8 pew] ++ [C4 (wz (h_bytesConsumed h))])
           ++ [C4 pad; C8 (wz (mb_addr (mh_decbuf mh))); C8 (wz (mh_stack mh)); C4 (wz (h_stack_size h)); C4 (wz (h_used h)); C8 (wz (mh_addr mh + 72))])
          ++ alloc_cells ayc).
  rewrite !ycells_app. cbn [cells_size csize Nat.add length app].
  replace (mh_addr mh + 32 + 4) with (mh_addr mh + 36) by lia. replace (mh_addr mh + 36 + 36) with (mh_addr mh + 72) by lia.
  tauto.
Qed.

Lemma tok_post_cases : forall K m0 tok e o st ms, tok_post K m0 tok e o st ms ->
  (tok = TK_eof /\ exists s7v, alex_at K m0 J_EOF s7v e o st ms) \/ (tok <> TK_eof /\ alex_at K m0 J_TOK (wz (tok_code tok)) e o st ms).
Proof. aceil. intros K m0 tok e o st ms H. destruct tok; first [left; split; [reflexivity| exact H] | right; split; [discriminate| exact H]]. Qed.

(* [comment removed for export] *)
Lemma abytes_at_sub : forall m A bs i k,
  bytes_at bsegs m A bs -> (i <= length bs)%nat -> bytes_at bsegs m (A + Z.of_nat i) (firstn k (skipn i bs)).
Proof. aceil.
  intros m A bs i k HB Hi.
  rewrite <- (firstn_skipn i bs) in HB. apply bytes_at_app in HB. destruct HB as [_ HB].
  rewrite length_firstn, Nat.min_l in HB by lia.
  rewrite <- (firstn_skipn k (skipn i bs)) in HB. apply bytes_at_app in HB. destruct HB as [HB _]. exact HB.
Qed.
Lemma abytes_at_zslice : forall m A str i k,
  bytes_at bsegs m A (zbytes str) -> 0 <= i <= zlength str -> bytes_at bsegs m (A + i) (zbytes (zslice str i k)).
Proof. aceil.
  intros m A str i k HB Hi. unfold zslice. rewrite lzbytes_firstn, lzbytes_skipn.
  replace i with (Z.of_nat (Z.to_nat i)) at 1 by lia. apply abytes_at_sub; [exact HB|]. rewrite zbytes_length. unfold zlength in Hi. lia.
Qed.
(* [comment removed for export] *)
Lemma abuf_rep_transport : forall W m m' mb b AF,
  buf_rep bsegs m mb b AF -> munch W m m' -> wmono bsegs m m' ->
  disjoint_from W (mb_addr mb) 32 ->
  (yb_data b <> None -> disjoint_from W (mb_data mb) (yb_len b)) ->
  buf_rep bsegs m' mb b AF.
Proof. aceil.
  intros W m m' mb b AF ((BC & BR) & BD & FB) MU WM D1 D2. split; [split; [| exact BR]|].
  - eapply (rw_cells_transport bsegs); [exact BC| exact MU| exact WM|]. rewrite buf_cells_size. exact D1.
  - split; [| exact FB]. unfold buf_data in *. destruct (yb_data b); [| exact I].
    destruct BD as (HU & junk & HC). split; [exact HU|]. exists junk.
    pose proof (proj1 (proj1 HC)) as WF. cbn [cells_wf cell_wf] in WF. destruct WF as (L1 & _ & L2 & _).
    eapply (rw_cells_transport bsegs); [exact HC| exact MU| exact WM|].
    cbn [cells_size csize]. replace (Z.of_nat (Z.to_nat (yb_used b) + (1 + (Z.to_nat (yb_len b - yb_used b - 1) + 0)))) with (yb_len b) by lia.
    apply D2. discriminate.
Qed.

Lemma tok_eqb_eof_false : forall tok, tok <> TK_eof -> tok_eqb tok TK_eof = false.
Proof. aceil. intros [] H; try reflexivity. congruence. Qed.
Lemma tok_eqb_error : forall tok, tok_eqb tok TK_error = true -> tok = TK_error.
Proof. aceil. intros [] H; try discriminate H. reflexivity. Qed.

Section W.
Variable Y : ay_params.
Hypothesis KIPY : AHK_y_kip_stmt Y.
Hypothesis FRAMEY : AHK_y_frame_stmt Y.
Hypothesis BLKY : AHK_y_blocks_stmt Y.
Hypothesis MIY : AHK_y_mem_inv_stmt Y.
Hypothesis BSHY : AHK_y_block_shadow_stmt Y.
Hypothesis BSMALL : AHK_y_small_high_stmt Y.   (* [comment removed for export] *)
Hypothesis LAYY : AHK_y_layout_stmt Y.
Hypothesis PERMY : AHK_y_perm_stmt Y.
Hypothesis GLOBY : AHK_y_globals_shadow_stmt Y.
Hypothesis RRT : ayR_trans_stmt Y.
Hypothesis RREFL : forall s mo, y_ayR Y s mo s mo.
Hypothesis BCLR : aybuf_clear_stmt.
Hypothesis BERR : aybuf_err_stmt.
Hypothesis BAPP : aybuf_append_stmt Y.
Variable URA : list Z.
Hypothesis UTRIV : forall m SP ra s0, bv_unsigned s0 < alloc_ceiling -> In (bv_unsigned ra) URA -> y_uanchor Y m SP ra s0.
Hypothesis URA_site : In 0x85ba0 URA.   (* [comment removed for export] *)
Hypothesis ICPB : forall s LB LF m mo b A n, y_AHK Y s LB LF m mo -> In b LB ->
    ab_addr b <= A -> 1 <= n -> A + n <= ab_addr b + ab_size b ->
    exists ws, shadow_window bsegs m A_SB A n ws /\ range_clean A_SB A n ws
               /\ shw_hi A_SB A n <= 0x10007fff8000 /\ amem (ab_addr b) (ab_size b).   (* [comment removed for export] *)
Hypothesis ICPR : forall s LB LF m mo b A n, y_AHK Y s LB LF m mo -> In b LB -> ab_addr b <= A -> 1 <= n -> A + n <= ab_addr b + ab_size b ->
    pages_budgeted (y_aS Y s) (shw_lo A_SB A) (shw_hi A_SB A n).

Theorem aylex_lex_proof : aylex_lex_stmt Y.
Proof. aceil.
  unfold aylex_lex_stmt. intros LF REST h mh T txt off OBP OLP OT OTn obw olw lo RR KT. intros until s.
  intros BA K0 AY HS LR LI HOFF OFFB LEN TX TLE TXR TSH OSH OSL OSB OB OL OSOB OSOL FOB FP EA0 EA1 EA2 EA3 EA4 EA5 CRED RR0 NBIG UA CONT.
  subst a0 a1 a2 a3 a4 a5.
  destruct FP as (ST & CEIL & LO & SPH & SP16 & MI & TP & FRM).
  apply AYST_split in AY. destruct AY as [AHK0 YS]. pose proof YS as (YSa & YSb & YSc & STA).
  pose proof LI as (IU & IO & IL & ICH & IA & IV & IB).
  (* [comment removed for export] *)
  unfold buf_blocks in AHK0. rewrite IB in AHK0. cbn [abl map blk_addr blk_size fst snd app] in AHK0.
  unfold SIZEOF_HANDLE, SIZEOF_LEXER, SIZEOF_BUF, AY_LEX_LEX_STACK, AY_BUF_APPEND_STACK, AMALLOC_STACK in *.
  destruct (BLKY _ _ _ _ _ AHK0) as (RNG & SEP & ND).
  pose proof (RNG (mkABlock (mh_addr mh) 104) (or_introl eq_refl)) as RH.
  pose proof (RNG (mkABlock (mh_lexer mh) 48) (or_intror (or_introl eq_refl))) as RL.
  pose proof (RNG (mkABlock (mb_addr (mh_lexbuf mh)) 32) (or_intror (or_intror (or_introl eq_refl)))) as RLB.
  unfold ablock_range, ACONSTS in RH, RL, RLB. cbn [c_img_hi ab_addr ab_size] in RH, RL, RLB.
  pose proof (SEP (mkABlock (mh_addr mh) 104) (mkABlock (mh_lexer mh) 48) (or_introl eq_refl) (or_intror (or_introl eq_refl))) as SHL.
  pose proof (SEP (mkABlock (mh_addr mh) 104) (mkABlock (mb_addr (mh_lexbuf mh)) 32) (or_introl eq_refl) (or_intror (or_intror (or_introl eq_refl)))) as SHB.
  pose proof (SEP (mkABlock (mh_lexer mh) 48) (mkABlock (mb_addr (mh_lexbuf mh)) 32) (or_intror (or_introl eq_refl)) (or_intror (or_intror (or_introl eq_refl)))) as SLB.
  cbn [ab_addr ab_size] in SHL, SHB, SLB.
  pose proof (proj2 (proj1 (List.NoDup_cons_iff _ _) ND)) as ND1. pose proof (proj2 (proj1 (List.NoDup_cons_iff _ _) ND1)) as ND2.
  assert (NHL : mh_addr mh <> mh_lexer mh).
  { intros E. apply (proj1 (proj1 (List.NoDup_cons_iff _ _) ND)). cbn [map ab_addr]. rewrite E. left. reflexivity. }
  assert (NHB : mh_addr mh <> mb_addr (mh_lexbuf mh)).
  { intros E. apply (proj1 (proj1 (List.NoDup_cons_iff _ _) ND)). cbn [map ab_addr]. rewrite E. right. left. reflexivity. }
  assert (NLB : mh_lexer mh <> mb_addr (mh_lexbuf mh)).
  { intros E. apply (proj1 (proj1 (List.NoDup_cons_iff _ _) ND1)). cbn [map ab_addr]. rewrite E. left. reflexivity. }
  specialize (SHL NHL). specialize (SHB NHB). specialize (SLB NLB).
  yhide SHL. yhide SHB. yhide SLB.
  pose proof (BSMALL _ _ _ _ _ (mkABlock (mh_addr mh) 104) AHK0 (or_introl eq_refl) ltac:(cbn; unfold SIZEOF_BUF, SIZEOF_LEXER, SIZEOF_HANDLE; lia)) as HH. cbn [ab_addr] in HH.
  pose proof (BSMALL _ _ _ _ _ (mkABlock (mh_lexer mh) 48) AHK0 (or_intror (or_introl eq_refl)) ltac:(cbn; unfold SIZEOF_BUF, SIZEOF_LEXER, SIZEOF_HANDLE; lia)) as HL. cbn [ab_addr] in HL.
  pose proof (BSMALL _ _ _ _ _ (mkABlock (mb_addr (mh_lexbuf mh)) 32) AHK0 (or_intror (or_intror (or_introl eq_refl))) ltac:(cbn; unfold SIZEOF_BUF, SIZEOF_LEXER, SIZEOF_HANDLE; lia)) as HLB. cbn [ab_addr] in HLB.
  unfold oshw_hi, A_SB, amem in HH, HL, HLB. cbn -[Z.le Z.add] in HH, HL, HLB.
  aceil.
  (* [comment removed for export] *)
  destruct HS as ((pew & pad & HC & PW) & HB1 & HB2 & HB3 & HB4).
  destruct LR as ((LC & L1 & L2 & L3 & L4 & L5 & L6) & ((BC & BI & BL1 & BL2) & BD & BF)). clear L1 L2 L3 L4 L5 L6 BL1 BL2.
  rewrite IB in BC, BI, BD, BF.
  assert (D0 : mb_data (mh_lexbuf mh) = 0) by (apply BI; reflexivity). rewrite D0 in BC.
  rewrite (lxcells_of_lexer _ _ _ LI) in LC.
  apply ahand_split in HC. destruct HC as (HC0 & OFF0 & HC2 & YAF). rewrite HOFF in OFF0.
  pose proof TX as (_ & TF & TP0 & TL).
  (* [comment removed for export] *)
  destruct FOB as (ff & FFIN & FF1 & FF2 & FF3).
  destruct (proj1 (LAYY _ _ _ _ _ AHK0) ff FFIN) as (LF1 & LF2 & LF3 & LF4 & LF5). rewrite FF3 in LF1, LF2, LF3. unfold ff_bytes in LF1, LF2, LF3. change (Z.shiftl 64 1) with 128 in LF1. change (Z.shiftl 64 1) with 128 in LF2. change (Z.shiftl 64 1) with 128 in LF3.
  unfold oshw_hi, A_SB, amem in LF1, LF2; aceil. cbn -[Z.le Z.add Z.lt] in LF1.
  pose proof (fun b Hb => proj1 (proj1 (proj2 (LAYY _ _ _ _ _ AHK0)) ff b FFIN Hb)) as LFB. rewrite FF3 in LFB. unfold ff_bytes in LFB. change (Z.shiftl 64 1) with 128 in LFB.
  pose proof (LFB _ (or_introl eq_refl)) as FBH. pose proof (LFB _ (or_intror (or_introl eq_refl))) as FBL.
  pose proof (LFB _ (or_intror (or_intror (or_introl eq_refl)))) as FBLB. cbn [ab_addr ab_size] in FBH, FBL, FBLB.
  yhide FBH. yhide FBL. yhide FBLB. yhide LFB.
  (* [comment removed for export] *)
  assert (TSEP : 0 < zlength txt -> exists bt, In bt REST /\ ab_addr bt <= T /\ T + zlength txt <= ab_addr bt + ab_size bt
            /\ (6303744 <= ab_addr bt /\ (ab_addr bt + ab_size bt <= 2147446784 \/ 17594333495296 <= ab_addr bt)) /\ ab_addr bt + ab_size bt <= alloc_ceiling
            /\ (mh_addr mh + 104 <= ab_addr bt \/ ab_addr bt + ab_size bt <= mh_addr mh)
            /\ (mh_lexer mh + 48 <= ab_addr bt \/ ab_addr bt + ab_size bt <= mh_lexer mh)
            /\ (mb_addr (mh_lexbuf mh) + 32 <= ab_addr bt \/ ab_addr bt + ab_size bt <= mb_addr (mh_lexbuf mh))
            /\ (ab_addr bt + ab_size bt <= snd ff \/ snd ff + 128 <= ab_addr bt)).
  { intros Hl. destruct TXR as [(bt & HBT & B1 & B2)| Z0]; [| lia]. exists bt.
    pose proof (RNG bt ltac:(right; right; right; exact HBT)) as RT. unfold ablock_range, ACONSTS in RT. cbn [c_img_hi] in RT.
    aceil.
    pose proof (proj2 (BSHY _ _ _ _ _ bt AHK0 ltac:(right; right; right; exact HBT) ltac:(lia))) as BTH. unfold oshw_hi, A_SB, amem in BTH. cbn -[Z.le Z.add] in BTH.
    assert (NE1 : mh_addr mh <> ab_addr bt).
    { intros E. apply (proj1 (proj1 (List.NoDup_cons_iff _ _) ND)). cbn [map ab_addr]. rewrite E. right; right. apply (in_map ab_addr). exact HBT. }
    assert (NE2 : mh_lexer mh <> ab_addr bt).
    { intros E. apply (proj1 (proj1 (List.NoDup_cons_iff _ _) ND1)). cbn [map ab_addr]. rewrite E. right. apply (in_map ab_addr). exact HBT. }
    assert (NE3 : mb_addr (mh_lexbuf mh) <> ab_addr bt).
    { intros E. apply (proj1 (proj1 (List.NoDup_cons_iff _ _) ND2)). cbn [map ab_addr]. rewrite E. apply (in_map ab_addr). exact HBT. }
    pose proof (SEP (mkABlock (mh_addr mh) 104) bt (or_introl eq_refl) ltac:(right; right; right; exact HBT) NE1) as S1.
    pose proof (SEP (mkABlock (mh_lexer mh) 48) bt (or_intror (or_introl eq_refl)) ltac:(right; right; right; exact HBT) NE2) as S2.
    pose proof (SEP (mkABlock (mb_addr (mh_lexbuf mh)) 32) bt (or_intror (or_intror (or_introl eq_refl))) ltac:(right; right; right; exact HBT) NE3) as S3.
    cbn [ab_addr ab_size] in S1, S2, S3.
    pose proof LFB as LFB'. yshow LFB'. pose proof (LFB' bt ltac:(right; right; right; exact HBT)) as FBT.
    clear -CEILB HBT B1 B2 RT BTH S1 S2 S3 FBT. repeat split; first [exact HBT| lia]. }
  assert (OTF : 0 < zlength txt -> OT mod 8 = 0 /\ OT <= T /\ T + zlength txt <= OT + OTn /\ (6303744 <= OT /\ (OT + OTn <= 2147446784 \/ 17594333495296 <= OT)) /\ OT + OTn <= alloc_ceiling
            /\ exists bt, In bt REST /\ ab_addr bt <= OT /\ OT + OTn <= ab_addr bt + ab_size bt).
  { intros Hl. destruct TSH as [Z0 | (OTS & O1 & O2 & O3 & O4 & OTB)]; [lia|].
    destruct OTS as (O8 & _ & _). unfold oshw_hi, A_SB, amem in O3, O4; aceil. cbn -[Z.le Z.add] in O3.
    clear -CEILB O8 O1 O2 O3 O4 OTB. repeat split; try lia. exact OTB. }
  assert (LENV : lexenvA (bv_unsigned sp) lo T (zlength txt) (mh_addr mh) (mh_lexer mh) (mb_addr (mh_lexbuf mh)) OT OTn).
  { clear CONT. split.
    - clear -CEILB CEIL. lia.
    - clear -CEILB LO. lia.
    - clear -CEILB SPH. lia.
    - clear -CEILB HH RH. lia.
    - clear -CEILB HL RL. lia.
    - clear -CEILB HLB RLB. lia.
    - clear -CEILB SHL. yshow SHL. lia.
    - clear -CEILB SHB. yshow SHB. lia.
    - clear -CEILB SLB. yshow SLB. lia.
    - clear -CEILB OFFB LEN. lia.
    - clear -CEILB TP0 TL. lia.
    - intros Hl. destruct (TSEP Hl) as (bt & X). clear -CEILB X. lia.
    - intros Hl. destruct (OTF Hl) as (X1 & X2 & X3 & X4 & X5 & _). exact (conj X1 (conj X2 (conj X3 (conj X4 X5)))). }
  assert (LENVT : lexenvT lo T (zlength txt) (mh_addr mh) (mh_lexer mh) (mb_addr (mh_lexbuf mh)) OBP OLP).
  { clear CONT. split.
    - clear -CEILB FF1 FF2 LF1 LF2 LF3 CEIL. subst OBP. split; [lia|]. split; [lia|]. split; [| lia]. Z.div_mod_to_equations. lia.
    - clear -CEILB FF1 FF2 FBH FBL FBLB TSEP. yshow FBH. yshow FBL. yshow FBLB. subst OBP. split; [lia|]. split; [lia|]. split; [lia|].
      intros Hl. destruct (TSEP Hl) as (bt & X). lia. }
  assert (LOSP : lo <= bv_unsigned sp) by (clear -CEILB LO; lia).
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  (* [comment removed for export] *)
  assert (RESTIN : forall b, In b REST -> In b (mkABlock (mh_addr mh) 104 :: mkABlock (mh_lexer mh) 48 :: mkABlock (mb_addr (mh_lexbuf mh)) 32 :: REST))
    by (intros b Hb; right; right; right; exact Hb).
  assert (RESTH : forall b, In b REST -> In b (mkABlock (mh_addr mh) 104 :: mkABlock (mh_lexer mh) 48 :: mkABlock (mb_addr (mh_lexbuf mh)) 32 :: REST) /\ ab_addr b <> ab_addr (mkABlock (mh_addr mh) 104)).
  { intros b Hb. split; [right; right; right; exact Hb|]. cbn [ab_addr]. intros E. apply (proj1 (proj1 (List.NoDup_cons_iff _ _) ND)). cbn [map ab_addr]. rewrite <- E. right; right. apply (in_map ab_addr). exact Hb. }
  assert (RESTL : forall b, In b REST -> In b (mkABlock (mh_addr mh) 104 :: mkABlock (mh_lexer mh) 48 :: mkABlock (mb_addr (mh_lexbuf mh)) 32 :: REST) /\ ab_addr b <> ab_addr (mkABlock (mh_lexer mh) 48)).
  { intros b Hb. split; [right; right; right; exact Hb|]. cbn [ab_addr]. intros E. apply (proj1 (proj1 (List.NoDup_cons_iff _ _) ND1)). cbn [map ab_addr]. rewrite <- E. right. apply (in_map ab_addr). exact Hb. }
  assert (RESTLB : forall b, In b REST -> In b (mkABlock (mh_addr mh) 104 :: mkABlock (mh_lexer mh) 48 :: mkABlock (mb_addr (mh_lexbuf mh)) 32 :: REST) /\ ab_addr b <> ab_addr (mkABlock (mb_addr (mh_lexbuf mh)) 32)).
  { intros b Hb. split; [right; right; right; exact Hb|]. cbn [ab_addr]. intros E. apply (proj1 (proj1 (List.NoDup_cons_iff _ _) ND2)). cbn [map ab_addr]. rewrite <- E. apply (in_map ab_addr). exact Hb. }
  assert (WOUT : forall m1 m2 W, munch W m1 m2 -> wmono bsegs m1 m2 ->
            (forall x, outside [(lo, bv_unsigned sp)] x -> outside [(mh_addr mh + 32, mh_addr mh + 36)] x -> outside [(mh_lexer mh, mh_lexer mh + 48)] x ->
                       outside [(mb_addr (mh_lexbuf mh) + 8, mb_addr (mh_lexbuf mh) + 12)] x -> ~ (OLP <= x < OLP + 4) -> ~ (OBP <= x < OBP + 8) -> outside W x) ->
            ay_pres REST LF (bv_unsigned sp) [(OLP, OLP + 4); (OBP, OBP + 8)] m1 m2).
  { intros m1 m2 W MU WM HW. eapply ay_pres_of_munch; [exact MU| exact WM|]. intros a Ha Hc Hx. apply HW.
    - eapply (ay_client_outside_stack Y BLKY LAYY _ _ _ _ _ REST (bv_unsigned sp)); [exact AHK0| exact RESTIN| clear -CEILB CEIL; aceil; lia| lia| exact Hc].
    - eapply (ay_client_outside_block Y BLKY BSHY LAYY _ _ _ _ _ REST (bv_unsigned sp) (mkABlock (mh_addr mh) 104)); [exact AHK0| left; reflexivity| exact RESTH| cbn; lia| cbn; lia| lia| clear -CEILB CEIL LOSP; aceil; lia| exact Hc].
    - eapply (ay_client_outside_block Y BLKY BSHY LAYY _ _ _ _ _ REST (bv_unsigned sp) (mkABlock (mh_lexer mh) 48)); [exact AHK0| right; left; reflexivity| exact RESTL| cbn; lia| cbn; lia| lia| clear -CEILB CEIL LOSP; aceil; lia| exact Hc].
    - eapply (ay_client_outside_block Y BLKY BSHY LAYY _ _ _ _ _ REST (bv_unsigned sp) (mkABlock (mb_addr (mh_lexbuf mh)) 32)); [exact AHK0| right; right; left; reflexivity| exact RESTLB| cbn; lia| cbn; lia| lia| clear -CEILB CEIL LOSP; aceil; lia| exact Hc].
    - intros X. apply Hx. cbn. left. exact X.
    - intros X. apply Hx. cbn. right. left. exact X. }
  (* [comment removed for export] *)
  assert (WOK : Forall (ay_write_ok (mkABlock (mh_addr mh) 104 :: mkABlock (mh_lexer mh) 48 :: mkABlock (mb_addr (mh_lexbuf mh)) 32 :: REST) LF)
                  [(lo, bv_unsigned sp); (mh_addr mh + 32, mh_addr mh + 36); (mh_lexer mh, mh_lexer mh + 48); (mb_addr (mh_lexbuf mh) + 8, mb_addr (mh_lexbuf mh) + 12); (OLP, OLP + 4); (OBP, OBP + 8)]).
  { unfold ay_write_ok.
    constructor; [cbn [fst snd]; left; clear -CEILB CEIL; aceil; lia|].
    constructor; [cbn [fst snd]; right; left; exists (mkABlock (mh_addr mh) 104); split; [left; reflexivity| cbn; lia]|].
    constructor; [cbn [fst snd]; right; left; exists (mkABlock (mh_lexer mh) 48); split; [right; left; reflexivity| cbn; lia]|].
    constructor; [cbn [fst snd]; right; left; exists (mkABlock (mb_addr (mh_lexbuf mh)) 32); split; [right; right; left; reflexivity| cbn; lia]|].
    constructor; [cbn [fst snd]; right; right; left; exists ff; split; [exact FFIN| rewrite FF3; unfold ff_bytes; change (Z.shiftl 64 1) with 128; lia]|].
    constructor; [cbn [fst snd]; right; right; left; exists ff; split; [exact FFIN| rewrite FF3; unfold ff_bytes; change (Z.shiftl 64 1) with 128; lia]|].
    constructor. }
  assert (WST : Forall (fun iv : Z * Z => snd iv <= 0xa5000 \/ 0xae838 <= fst iv)
                  [(lo, bv_unsigned sp); (mh_addr mh + 32, mh_addr mh + 36); (mh_lexer mh, mh_lexer mh + 48); (mb_addr (mh_lexbuf mh) + 8, mb_addr (mh_lexbuf mh) + 12); (OLP, OLP + 4); (OBP, OBP + 8)]).
  { clear -CEILB CEIL HH HL HLB LF1 FF1 FF2. repeat (constructor; [cbn [fst snd]; lia|]). constructor. }
  (* [comment removed for export] *)
  pose proof OSH as (H8 & _ & UH). pose proof OSOB as (OB8 & _ & UOB). pose proof OSOL as (OL8 & _ & UOL). unfold A_SB in UH, UOB, UOL.
  destruct (GLOBY _ _ _ _ _ AHK0) as (_ & _ & _ & GC & GR & GA & GU).
  (* [comment removed for export] *)
  assert (MKKP : forall (Lz : list (word * word)) (Sz : word -> Prop) (LBx : list ablock) (Fz : bvmap 5 word) (fcz : bv 32),
            (forall x, ay_acc Y LBx LF x -> acc_ok Lz Sz x) ->
            In (mkABlock (mh_addr mh) 104) LBx -> In (mkABlock (mh_lexer mh) 48) LBx -> In (mkABlock (mb_addr (mh_lexbuf mh)) 32) LBx ->
            (forall b, In b REST -> In b LBx) ->
            kpolA (mkALK (acc_ok Lz Sz) sp gp tp Fz fcz lo T txt (mh_addr mh) (mh_lexer mh) (mb_addr (mh_lexbuf mh)) OBP OLP OT OTn
                         ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)).
  { clear CONT WOUT UA. intros Lz Sz LBx Fz fcz LINK INH INL INLB INR.
    pose proof (aypol_stack Y _ LF _ _ LINK lo (bv_unsigned sp) ltac:(clear -CEILB CEIL; aceil; lia) (Z.lt_le_incl _ _ SPH)) as PSTK.
    pose proof (aypol_img Y _ LF _ _ LINK) as PIMG.
    pose proof (aypol_imgshadow Y _ LF _ _ LINK) as PIMGSH.
    destruct (aypol_opol_block Y _ LF _ _ LINK (mkABlock (mh_addr mh) 104) INH ltac:(cbn; clear -CEILB RH; lia) ltac:(cbn; unfold oshw_lo, A_SB; clear -CEILB RH; lia)
                ltac:(cbn; unfold oshw_hi, A_SB, amem; clear -CEILB RH; lia) ltac:(cbn; clear -CEILB RH; lia)) as [PH PHS]. cbn [ab_addr ab_size] in PH, PHS.
    destruct (aypol_opol_block Y _ LF _ _ LINK (mkABlock (mh_lexer mh) 48) INL ltac:(cbn; clear -CEILB RL; lia) ltac:(cbn; unfold oshw_lo, A_SB; clear -CEILB RL; lia)
                ltac:(cbn; unfold oshw_hi, A_SB, amem; clear -CEILB RL; lia) ltac:(cbn; clear -CEILB RL; lia)) as [PL PLS]. cbn [ab_addr ab_size] in PL, PLS.
    destruct (aypol_opol_block Y _ LF _ _ LINK (mkABlock (mb_addr (mh_lexbuf mh)) 32) INLB ltac:(cbn; clear -CEILB RLB; lia) ltac:(cbn; unfold oshw_lo, A_SB; clear -CEILB RLB; lia)
                ltac:(cbn; unfold oshw_hi, A_SB, amem; clear -CEILB RLB; lia) ltac:(cbn; clear -CEILB RLB; lia)) as [PLB PLBS]. cbn [ab_addr ab_size] in PLB, PLBS.
    pose proof (aypol_fframe Y _ LF _ _ LINK ff OBP (OLP + 4) FFIN ltac:(clear -CEILB FF1 FF2; lia) ltac:(rewrite FF3; unfold ff_bytes; change (Z.shiftl 64 1) with 128; clear -CEILB FF1 FF2; lia) ltac:(clear -CEILB FF1 LF1; lia)
                  ltac:(rewrite FF3; unfold ff_bytes; change (Z.shiftl 64 1) with 128; clear -CEILB LF2; lia)) as PFF.
    pose proof (aypol_ffshadow Y _ LF _ _ LINK ff (2147450880 + OBP / 8) (2147450880 + OLP / 8 + 1) FFIN
                  ltac:(unfold oshw_lo, A_SB; clear -CEILB FF1 FF2 LF1; Z.div_mod_to_equations; lia)
                  ltac:(rewrite FF3; unfold oshw_lo, A_SB; change (Z.shiftl 8 1) with 16; clear -CEILB FF1 FF2 LF1 LF3; Z.div_mod_to_equations; lia)
                  ltac:(clear -CEILB FF1 FF2 LF1; Z.div_mod_to_equations; lia)
                  ltac:(rewrite FF3; unfold oshw_lo, A_SB; change (Z.shiftl 8 1) with 16; clear -CEILB LF1 LF2; Z.div_mod_to_equations; lia)) as PFFS.
    unfold opol, pol, oshw_lo, oshw_hi, A_SB, amem in PH, PHS, PL, PLS, PLB, PLBS. unfold pol in PSTK, PIMG, PIMGSH, PFF, PFFS.
    unfold AY_IMG_LO, AY_IMG_HI, oshw_lo, oshw_hi, A_SB, amem in PIMG, PIMGSH.
    split; cbn [k_P k_lo k_sp k_H k_L k_LB k_T k_txt k_OT k_OTn k_OBP k_OLP].
    - intros a k Ha Hk. apply PSTK; lia.
    - intros a k Ha Hk. unfold AY_IMG_LO, AY_IMG_HI in Ha, Hk. apply PIMG; lia.
    - intros a k Ha Hk. eapply (PIMGSH a (a + Z.of_nat k)); lia.
    - intros a k Ha Hk. apply PH; lia.
    - intros a k Ha Hk. apply PHS; lia.
    - intros a k Ha Hk. apply PL; lia.
    - intros a k Ha Hk. apply PLS; lia.
    - intros a k Ha Hk. apply PLB; lia.
    - intros a k Ha Hk. apply PLBS; lia.
    - intros Hl. destruct (TSEP Hl) as (bt & HBT & X).
      apply (aypol_block Y _ LF _ _ LINK bt); [apply INR; exact HBT| lia| lia| lia| lia].
    - intros Hl. destruct (OTF Hl) as (O8' & O1 & O2 & O3 & O4 & (bt & HBT & Q1 & Q2)).
      pose proof (RNG bt (RESTIN _ HBT)) as RT. unfold ablock_range, ACONSTS in RT. cbn [c_img_hi] in RT. aceil.
      apply (aypol_bshadow Y _ LF _ _ LINK bt); [apply INR; exact HBT| unfold oshw_lo, A_SB; clear -CEILB Q1 O8'; Z.div_mod_to_equations; lia| | clear -CEILB O3; lia|];
        unfold oshw_lo, oshw_hi, A_SB, amem; clear -CEILB Q1 Q2 O8' RT O3 O4; Z.div_mod_to_equations; lia.
    - intros a k Ha Hk. apply PFF; lia.
    - intros a k Ha Hk. apply PFFS; lia.
    - intros a k Ha Hk. apply PFF; lia.
    - intros a k Ha Hk. apply PFFS; lia. }
  (* [comment removed for export] *)
  arz_seg KIPY AHK0.
  pose proof (MKKP _ _ _ F fc LINK (or_introl eq_refl) (or_intror (or_introl eq_refl)) (or_intror (or_intror (or_introl eq_refl))) RESTIN) as KP0.
  (* [comment removed for export] *)
  assert (ALN : Z.land (mh_addr mh + 32) 3 = 0 /\ Z.land (mh_addr mh + 32) 7 = 0 /\ Z.land OBP 7 = 0 /\ Z.land OLP 3 = 0 /\ Z.land OLP 7 = 0
                /\ Z.land (mh_lexer mh) 7 = 0 /\ Z.land (mh_lexer mh + 28) 7 = 4 /\ Z.land (mh_lexer mh + 32) 7 = 0).
  { pose proof (le_H _ _ _ _ _ _ _ _ _ LENV) as XH. pose proof (le_L _ _ _ _ _ _ _ _ _ LENV) as XL. pose proof (le_OB _ _ _ _ _ _ _ _ LENVT) as XO.
    clear -XH XL XO. rewrite !land7_mod8, !land3_mod4 by lia.
    repeat match goal with |- _ /\ _ => split end; Z.div_mod_to_equations; lia. }
  destruct ALN as (AH3 & AH7 & AOB7 & AOL3 & AOL7 & AL7 & AL28 & AL32).
  eapply evtA_cut.
  { eapply (lex_prologue (acc_ok (m_vm_lazy mo) (y_aS Y s)) sp gp tp F fc lo T txt (mh_addr mh) (mh_lexer mh) (mb_addr (mh_lexbuf mh)) OBP OLP OT OTn
              _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ obw olw m _ off (blk_shadow 104) (blk_shadow 8) (blk_shadow 4));
      [exact ST| exact MI| exact OFF0| exact OB| exact OL| exact LC| exact BC| exact STA| exact UH| reflexivity| exact UOB| reflexivity| exact UOL| reflexivity
      | exact LENV| exact LENVT| exact OFFB| apply lex_error_code_range
      | exact AH3| exact AH7| exact AOB7| exact AOL3| exact AOL7| exact AL7| exact AL28| exact AL32
      | exact (kp_stk _ KP0)| exact (kp_img _ KP0)| exact (kp_H _ KP0)| exact (kp_Hs _ KP0)
      | exact (kp_OB _ KP0)| exact (kp_OBs _ KP0)| exact (kp_OL _ KP0)| exact (kp_OLs _ KP0)]. }
  cbv beta. intros ms1 (a2p & a3p & a4p & a5p & a6p & m1 & -> & MU1 & WM1 & MI1 & ST1 & FR1 & OFF1 & OB1 & OL1 & LC1 & BC1).
  clear KP0.
  set (K := mkALK (acc_ok (m_vm_lazy mo) (y_aS Y s)) sp gp tp F fc lo T txt (mh_addr mh) (mh_lexer mh) (mb_addr (mh_lexbuf mh)) OBP OLP OT OTn
                  ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
  assert (ENV : kenvA K) by exact LENV. assert (ENVT : kenvT K) by exact LENVT.
  Ltac kk X := cbv delta [X]; cbv delta [kSQ kAF]; cbn [k_P k_sp k_gp k_tp k_F k_fc k_lo k_T k_txt k_H k_L k_LB k_OBP k_OLP k_OT k_OTn k_ra k_s0 k_s1 k_s2 k_s3 k_s4 k_s5 k_s6 k_s7 k_s8 k_s9 k_s10 k_s11].
  Ltac kkh X H := cbv delta [X] in H; cbv delta [kSQ kAF] in H; cbn [k_P k_sp k_gp k_tp k_F k_fc k_lo k_T k_txt k_H k_L k_LB k_OBP k_OLP k_OT k_OTn k_ra k_s0 k_s1 k_s2 k_s3 k_s4 k_s5 k_s6 k_s7 k_s8 k_s9 k_s10 k_s11] in H.
  pose proof (MKKP _ _ _ F fc LINK (or_introl eq_refl) (or_intror (or_introl eq_refl)) (or_intror (or_intror (or_introl eq_refl))) RESTIN) as KP.
  change (kpolA K) in KP.
  (* [comment removed for export] *)
  assert (WLOW : forall A n, 2147450880 <= A -> A + n <= 17594333495296 -> disjoint_from [(lo, bv_unsigned sp); (OLP, OLP + 4); (OBP, OBP + 8)] A n).
  { intros A n HA Hn. cbn. clear -CEILB HA Hn CEIL LF1 FF1 FF2. lia. }   (* [comment removed for export] *)
  assert (SH1 : alexsh K m1).
  { destruct GC as (_ & _ & GCu). destruct GR as (_ & _ & GRu). destruct GA as (_ & _ & GAu). destruct GU as (_ & _ & GUu). unfold A_SB in GCu, GRu, GAu, GUu.
    split; kk K.
    - eapply (u8arr_transport bsegs); [exact UH| exact MU1| exact WM1| rewrite (blk_shadow_length 104) by lia; apply WLOW; clear -CEILB RH; lia].
    - destruct OSL as (_ & _ & U). unfold A_SB in U. eapply (u8arr_transport bsegs); [exact U| exact MU1| exact WM1| rewrite (blk_shadow_length 48) by lia; apply WLOW; clear -CEILB RL; lia].
    - destruct OSB as (_ & _ & U). unfold A_SB in U. eapply (u8arr_transport bsegs); [exact U| exact MU1| exact WM1| rewrite (blk_shadow_length 32) by lia; apply WLOW; clear -CEILB RLB; lia].
    - intros Hl. destruct TSH as [Z0 | ((_ & On0 & U) & O1 & O2 & O3 & O4 & _)]; [exfalso; clear -CEILB Hl Z0; lia|]. unfold A_SB in U.
      unfold oshw_hi, A_SB, amem in O3, O4; aceil. cbn -[Z.le Z.add] in O3.
      eapply (u8arr_transport bsegs); [exact U| exact MU1| exact WM1| rewrite (blk_shadow_length OTn) by lia; apply WLOW; clear -CEILB O3 O4 On0; lia].
    - eapply (u8arr_transport bsegs); [exact GCu| exact MU1| exact WM1| rewrite (blk_shadow_length 256) by lia; apply WLOW; unfold AY_CHARTAB; lia].
    - eapply (u8arr_transport bsegs); [exact GRu| exact MU1| exact WM1| rewrite (blk_shadow_length 4) by lia; apply WLOW; unfold A_RUE; lia].
    - eapply (u8arr_transport bsegs); [exact GAu| exact MU1| exact WM1| rewrite (blk_shadow_length 5) by lia; apply WLOW; unfold A_ALSE; lia].
    - eapply (u8arr_transport bsegs); [exact GUu| exact MU1| exact WM1| rewrite (blk_shadow_length 4) by lia; apply WLOW; unfold A_ULL; lia].
    - eapply (u8arr_transport bsegs); [exact UOB| exact MU1| exact WM1| rewrite (blk_shadow_length 8) by lia; apply WLOW; clear -CEILB LF1 LF2 FF1; Z.div_mod_to_equations; lia].
    - eapply (u8arr_transport bsegs); [exact UOL| exact MU1| exact WM1| rewrite (blk_shadow_length 4) by lia; apply WLOW; clear -CEILB LF1 LF2 FF1 FF2; Z.div_mod_to_equations; lia].
    - pose proof (aystatics_munch _ _ _ YS MU1 WM1) as X. destruct X as (_ & _ & _ & X); [| exact X].
      clear -CEILB CEIL LF1 FF1 FF2. repeat (constructor; [cbn [fst snd]; lia|]). constructor.
    - eapply text_at_transport; [exact TX| exact MU1|]. intros Hl. destruct (TSEP Hl) as (bt & _ & B1 & B2 & BTH & BTC & _ & _ & _ & BTF). cbn. clear -CEILB B1 B2 BTH BTC BTF CEIL FF1 FF2 Hl. lia. }
  eapply evtA_cut.
  { (* [comment removed for export] *)
    pose proof (lex_core K m1 ENV KP SH1 (lex_number_proof K m1 ENV KP SH1) (lex_string_proof K m1 ENV KP SH1) (lex_comment_proof K m1 ENV KP SH1) BCLR _
                  (lex_loop_walk K m1 ENV KP SH1 (lex_number_proof K m1 ENV KP SH1) (lex_string_proof K m1 ENV KP SH1) (lex_comment_proof K m1 ENV KP SH1) BCLR
                     (Z.to_nat (zlength txt - off)))) as CORE.
    change (core_walk_at K m1 (lex_fuel (zlength txt) off)) in CORE. unfold core_walk_at, J_HD2 in CORE.
    eapply (CORE (h_lexer h)) with (start := off); [exact LI| | kk K; clear -CEILB OFFB; lia| kk K; clear -CEILB OFFB; lia| kk K; unfold lex_fuel; clear -CEILB OFFB; lia].
    unfold alexmem, kW, kframe, lexW. kk K.
    split; [apply munch_refl|]. split; [apply wmono_refl|].
    repeat match goal with |- _ /\ _ => split end; first [assumption| eassumption]. }
  cbv beta. intros ms' POST. destruct POST as (lx1 & tok & off1 & start1 & YL & LI1 & TPost).
  pose proof (ypost_yleaf _ _ _ (ylex_loop_post (lex_fuel (zlength txt) off) (h_lexer h) txt (zlength txt) off LI ltac:(clear -CEILB OFFB; lia) ltac:(unfold lex_fuel; clear -CEILB OFFB; lia)) YL) as LP.
  unfold YajlFactsLex.loop_post in LP. cbv beta iota zeta in LP. destruct LP as (_ & SB1 & SB2 & TK).
  pose proof LI1 as (IU1 & IO1 & IL1 & ICH1 & IA1 & IV1 & IB1).
  pose proof (lex_error_code_range (lx_error lx1)) as ER1.
  apply tok_post_cases in TPost. destruct TPost as [[-> [s7v AT]] | [NE AT]].
  + (* [comment removed for export] *)
    destruct AT as (rav' & s1' & s2' & s6' & s9' & t0' & t1x & t2' & a0' & a1x & a2x & a3x & a4x & a5' & a6' & a7' & t3' & t4' & t5' & t6' & k56' & k64' & k112' & m2 & -> & LM2 & K112).
    specialize (K112 eq_refl). subst k112'.
    pose proof ENVT as ET. destruct ET as [_ OBSEP]. kkh K OBSEP.
    eapply evtA_cut.
    { eapply (lex_eof_head K m1 ENV KP SH1 BCLR); [exact LM2| clear -CEILB SB1 SB2 OFFB; lia| kk K; clear -CEILB SB2; lia| exact ER1]. }
    cbv beta. intros ms3 (t0e & t1e & t2e & a4e & a5e & a6e & a7e & t3e & t4e & t5e & t6e & s2e & s6e & s9e & m4 & -> & MU4 & WM4 & MI4 & ST4 & FR4 & OFF4 & LX4 & BC4).
    unfold kW, lexW in MU4. kkh K MU4. kkh K ST4. kkh K FR4. kkh K OFF4. kkh K LX4. kkh K BC4. kk K.
    assert (OB4 : rw_cells bsegs m4 OBP [C8 (wz 0)]) by (eapply rw_cells_transport; [exact OB1| exact MU4| exact WM4| cbn; clear -CEILB OBSEP LF2 FF1 FF2 CEIL; lia]).
    assert (OL4 : rw_cells bsegs m4 OLP [C4 (wz 0)]) by (eapply rw_cells_transport; [exact OL1| exact MU4| exact WM4| cbn; clear -CEILB OBSEP LF2 FF1 FF2 CEIL; lia]).
    clear OBSEP LM2.
    (* [comment removed for export] *)
    apply evtA_done. intros mo4 Hag4 HLI4 Hh4. destruct (BACK mo4 Hag4 HLI4) as [AHK0' R4].
    assert (MUT : munch [(lo, bv_unsigned sp); (mh_addr mh + 32, mh_addr mh + 36); (mh_lexer mh, mh_lexer mh + 48);
                         (mb_addr (mh_lexbuf mh) + 8, mb_addr (mh_lexbuf mh) + 12); (OLP, OLP + 4); (OBP, OBP + 8)] m m4).
    { eapply munch_trans.
      - eapply munch_weaken; [| exact MU1]. unfold sub_fp. cbn [outside]. intros x (X1 & X2 & X3 & X4 & X5 & X6 & _). repeat split; assumption.
      - eapply munch_weaken; [| exact MU4]. unfold sub_fp. cbn [outside]. intros x (X1 & X2 & X3 & X4 & X5 & X6 & _). repeat split; assumption. }
    pose proof (wmono_trans _ _ _ _ WM1 WM4) as WMT.
    pose proof (FRAMEY _ _ _ _ _ _ _ AHK0' MUT WMT WOK) as AHK4.
    pose proof (aystatics_munch _ _ _ YS MUT WMT WST) as YS4.
    assert (TX4 : text_at bsegs m4 T txt).
    { eapply text_at_transport; [exact TX| exact MUT|]. intros Hl. destruct (TSEP Hl) as (bt & _ & X). cbn. clear -CEILB X CEIL FF1 FF2 Hl LOSP. lia. }
    assert (SRCL : zlength (zslice txt start1 (off1 - start1)) = off1 - start1) by (apply zslice_length; clear -CEILB SB1 SB2 OFFB; lia).
    assert (USQ : bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 256)) = bv_unsigned sp - 256) by (apply unsigned_lit; clear -CEILB LO LOSP SPR CEIL; lia).
    assert (PERM4 : Permutation (mkABlock (mh_addr mh) 104 :: mkABlock (mh_lexer mh) 48 :: mkABlock (mb_addr (mh_lexbuf mh)) 32 :: REST)
                                (mkABlock (mb_addr (mh_lexbuf mh)) 32 :: mkABlock (mh_addr mh) 104 :: mkABlock (mh_lexer mh) 48 :: REST)).
    { apply Permutation_sym. apply (Permutation_cons_app [mkABlock (mh_addr mh) 104; mkABlock (mh_lexer mh) 48] REST). apply Permutation_refl. }
    eapply (BAPP LF (mkABlock (mh_addr mh) 104 :: mkABlock (mh_lexer mh) 48 :: REST) (mh_lexbuf mh) ybuf_zero (mh_addr mh + 72)
                 (T + start1) (zslice txt start1 (off1 - start1)) lo RR KT).
    { (* [comment removed for export] *)
      unfold BA_aybuf_append. clear -CEILB RLB RH TP0 SB1 SB2 OFFB. repeat match goal with |- _ /\ _ => split end; first [lia| Z.div_mod_to_equations; lia]. }
    { exact K0. }
    { unfold buf_blocks. cbn [yb_data ybuf_zero abl map blk_addr blk_size fst snd app]. apply AYST_split. split; [| exact YS4].
      eapply PERMY; [exact AHK4| exact PERM4| apply Permutation_refl]. }
    { split; [split; [rewrite D0; exact BC4| split; [exact BI| cbn; lia]]|]. split; [exact BD| exact BF]. }
    { apply buf_inv_zero. }
    { eapply rw_cells_transport; [exact YAF| exact MUT| exact WMT| unfold alloc_cells; cbn; clear -CEILB RH SHL SHB FBH CEIL LOSP FF1 FF2; yshow SHL; yshow SHB; yshow FBH; lia]. }
    { exists (mkABlock (mh_addr mh) 104). split; [left; reflexivity|]. cbn [ab_addr ab_size]. split; [lia|]. split; [lia|]. split; [clear -CEILB RH; Z.div_mod_to_equations; lia|].
      split; [| exact HH].
      destruct OSH as (X8 & Xn & _). split; [exact X8|]. split; [exact Xn|].
      eapply (u8arr_transport bsegs); [exact UH| exact MUT| exact WMT| rewrite (blk_shadow_length 104) by lia; unfold A_SB; cbn; clear -CEILB RH RL RLB HH HL HLB LF1 LF2 FF1 FF2 CEIL; lia]. }
    { destruct OSB as (X8 & Xn & U). split; [exact X8|]. split; [exact Xn|].
      eapply (u8arr_transport bsegs); [exact U| exact MUT| exact WMT| rewrite (blk_shadow_length 32) by lia; unfold A_SB; unfold A_SB; cbn; clear -CEILB RH RL RLB HH HL HLB LF1 LF2 FF1 FF2 CEIL; lia]. }
    { intros X. exfalso. apply X. reflexivity. }
    { apply abytes_at_zslice; [exact (proj1 TX4)| clear -CEILB SB1 SB2 OFFB; lia]. }
    { apply lForall_zslice. exact TF. }
    { intros _. clear -CEILB TP0 SB1 SB2 OFFB. lia. }
    { rewrite SRCL. clear -CEILB SB1 SB2 OFFB TLE. lia. }
    { rewrite SRCL. cbn [yb_used ybuf_zero]. clear -CEILB SB1 SB2 OFFB LEN. lia. }
    { unfold ysrc_range. rewrite SRCL. destruct (Z.lt_ge_cases 0 (off1 - start1)) as [Hn|Hn]; [| right; right; right; clear -CEILB Hn SB1 SB2; lia].
      destruct (TSEP ltac:(clear -CEILB Hn SB1 SB2 OFFB; lia)) as (bt & IN & B1 & B2 & _). left. exists bt. split; [right; right; exact IN| clear -CEILB B1 B2 SB1 SB2 OFFB; lia]. }
    { (* [comment removed for export] *)
      unfold ysrc_win. rewrite SRCL. intros Hn s' LBx m' mo' AHK' PRES'.
      destruct (TSEP ltac:(clear -CEILB Hn SB1 SB2 OFFB; lia)) as (bt & IN & B1 & B2 & _).
      assert (INx : In bt (LBx ++ mkABlock (mh_addr mh) 104 :: mkABlock (mh_lexer mh) 48 :: REST)) by (apply in_or_app; right; right; right; exact IN).
      destruct (ICPB _ _ _ _ _ bt (T + start1) (off1 - start1) AHK' INx ltac:(clear -CEILB B1 SB1 SB2 OFFB; lia) ltac:(clear -CEILB Hn; lia) ltac:(clear -CEILB B2 SB1 SB2 OFFB; lia)) as (ws & SW & RC & SH1' & SH2').
      exists ws. split; [exact SW|]. split; [exact RC|].
      eapply aypol_pages.
      - eapply ICPR; [exact AHK'| exact INx| clear -CEILB B1 SB1 SB2 OFFB; lia| clear -CEILB Hn; lia| clear -CEILB B2 SB1 SB2 OFFB; lia].
      - pose proof (shw_geom A_SB (T + start1) (off1 - start1) ltac:(unfold A_SB; lia) ltac:(clear -CEILB TP0 SB1 SB2 OFFB; lia) ltac:(clear -CEILB Hn; lia)) as G. cbv zeta in G. unfold A_SB in *. clear -CEILB G. lia.
      - clear -CEILB SH1'. unfold A_SB in *. lia. }
    { unfold ayframe_pre, wz. rewrite ?USQ. split; [exact ST4|]. split; [exact CEIL|]. split; [clear -CEILB LO; unfold AY_BUF_APPEND_STACK, AMALLOC_STACK; lia|]. split; [clear -CEILB SPH LO; lia|].
      split; [clear -CEILB SP16 LO LOSP; Z.div_mod_to_equations; lia|]. split; [exact MI4|]. split; [exact TP| exact FRM]. }
    { reflexivity. }
    { reflexivity. }
    { unfold wz. rewrite SRCL. reflexivity. }
    { rewrite IB in CRED. exact CRED. }
    { exact RR0. }
    { revert NBIG. unfold nbig, AY_NBIG_REST. cbn [List.filter ab_size]. change (64512 <? 104) with false. change (64512 <? 48) with false. cbv iota. intros X. lia. }
    { rewrite USQ. apply UTRIV; [unfold wz; rewrite unsigned_lit by (clear -CEILB RH; lia); clear -CEILB RH; aceil; lia| unfold wz; rewrite unsigned_lit by lia; exact URA_site]. }
    cbv beta. intros t0c t1c t2c a0c a1c a2c a3c a4c a5c a6c a7c t3c t4c t5c t6c F5 fc5 m5 mo5 sa5 b' mb' LK POST5.
    destruct POST5 as (SO5 & R5 & CRED5 & (MI5 & ST5 & FRM5 & _ & PRES5) & YAF5 & YLA & BR5 & MBS & OS5 & OSD5 & LKZ5 & AY5 & LKB5 & LKO5).
    rewrite USQ in ST5, PRES5.
    apply AYST_split in AY5. destruct AY5 as [AHK5 YS5]. pose proof YS5 as (_ & _ & _ & STA5).
    unfold mb_same in MBS.
    pose proof BR5 as BR5c.
    destruct BR5 as ((BC5 & BI5 & BL5 & BL5') & BD5 & BF5). rewrite MBS in BC5. unfold buf_cells in BC5.
    (* [comment removed for export] *)
    pose proof (aypres_frame _ _ _ _ _ _ _ PRES5 FR4 ltac:(lia)) as FR5.
    assert (LX5 : rw_cells bsegs m5 (mh_lexer mh) [C4 (wz 0); C4 (wz 0); C4 (wz (lex_error_code (lx_error lx1))); C4 (wz 0); C8 (wz (mb_addr (mh_lexbuf mh))); C4 (wz 0); C4 (wz 1); C4 (wz 1); C4 (wz 1); C8 (wz (mh_addr mh + 72))]).
    { eapply aypres_block; [exact PRES5| exact LX4| exists (mkABlock (mh_lexer mh) 48); split; [right; left; reflexivity| cbn; lia]]. }
    assert (HC05 : rw_cells bsegs m5 (mh_addr mh) [C8 (wz (yc_callbacks ayc)); C8 (wz (mh_ctx mh)); C8 (wz (mh_lexer mh)); C8 pew]).
    { eapply aypres_block; [exact PRES5| | exists (mkABlock (mh_addr mh) 104); split; [left; reflexivity| cbn; lia]].
      eapply rw_cells_transport; [exact HC0| exact MUT| exact WMT| cbn; clear -CEILB RH SHL SHB FBH CEIL LOSP FF1 FF2; yshow SHL; yshow SHB; yshow FBH; lia]. }
    assert (OFF5 : rw_cells bsegs m5 (mh_addr mh + 32) [C4 (wz off1)]).
    { eapply aypres_block; [exact PRES5| exact OFF4| exists (mkABlock (mh_addr mh) 104); split; [left; reflexivity| cbn; lia]]. }
    assert (HC25 : rw_cells bsegs m5 (mh_addr mh + 36) [C4 pad; C8 (wz (mb_addr (mh_decbuf mh))); C8 (wz (mh_stack mh)); C4 (wz (h_stack_size h)); C4 (wz (h_used h)); C8 (wz (mh_addr mh + 72))]).
    { eapply aypres_block; [exact PRES5| | exists (mkABlock (mh_addr mh) 104); split; [left; reflexivity| cbn; lia]].
      eapply rw_cells_transport; [exact HC2| exact MUT| exact WMT| cbn; clear -CEILB RH SHL SHB FBH CEIL LOSP FF1 FF2; yshow SHL; yshow SHB; yshow FBH; lia]. }
    assert (OB5 : rw_cells bsegs m5 OBP [C8 (wz 0)]).
    { eapply aypres_fframe; [exact PRES5| exact OB4| exact FFIN| left; rewrite FF3; unfold ff_bytes; change (Z.shiftl 64 1) with 128; cbn; clear -CEILB FF1 FF2; lia]. }
    assert (OL5 : rw_cells bsegs m5 OLP [C4 (wz 0)]).
    { eapply aypres_fframe; [exact PRES5| exact OL4| exact FFIN| left; rewrite FF3; unfold ff_bytes; change (Z.shiftl 64 1) with 128; cbn; clear -CEILB FF1 FF2; lia]. }
    assert (TX5 : text_at bsegs m5 T txt).
    { eapply aypres_text; [exact PRES5| exact TX4|].
      destruct (Z.lt_ge_cases 0 (zlength txt)) as [Hl|Hl]; [destruct (TSEP Hl) as (bt & IN & B1 & B2 & _); left; exists bt; split; [right; right; exact IN| clear -CEILB B1 B2; lia]| right; clear -CEILB Hl OFFB; lia]. }
    (* [comment removed for export] *)
    assert (INL5 : In (mkABlock (mh_lexer mh) 48) (abl (buf_blocks mb' b') ++ LK ++ mkABlock (mh_addr mh) 104 :: mkABlock (mh_lexer mh) 48 :: REST)).
    { apply in_or_app. right. apply in_or_app. right. right. left. reflexivity. }
    assert (INH5 : In (mkABlock (mh_addr mh) 104) (abl (buf_blocks mb' b') ++ LK ++ mkABlock (mh_addr mh) 104 :: mkABlock (mh_lexer mh) 48 :: REST)).
    { apply in_or_app. right. apply in_or_app. right. left. reflexivity. }
    assert (INLB5 : In (mkABlock (mb_addr (mh_lexbuf mh)) 32) (abl (buf_blocks mb' b') ++ LK ++ mkABlock (mh_addr mh) 104 :: mkABlock (mh_lexer mh) 48 :: REST)).
    { apply in_or_app. left. unfold buf_blocks. rewrite <- MBS. cbn [abl map blk_addr blk_size fst snd]. left. reflexivity. }
    assert (INR5 : forall b, In b REST -> In b (abl (buf_blocks mb' b') ++ LK ++ mkABlock (mh_addr mh) 104 :: mkABlock (mh_lexer mh) 48 :: REST)).
    { intros b Hb. apply in_or_app. right. apply in_or_app. right. right. right. exact Hb. }
    destruct (BSHY _ _ _ _ _ (mkABlock (mh_lexer mh) 48) AHK5 INL5 ltac:(cbn [ab_size]; lia)) as [(_ & _ & UL5) _]. cbn [ab_addr ab_size] in UL5. unfold A_SB in UL5.
    destruct OS5 as (_ & _ & ULB5). rewrite MBS in ULB5. unfold A_SB in ULB5.
    assert (BSR : 0 <= buf_state_code (yb_state b') <= 2) by (destruct (yb_state b'); cbn; lia).
    (* [comment removed for export] *)
    destruct (BLKY _ _ _ _ _ AHK5) as (RNG5 & SEP5 & ND5).
    assert (DSEP : yb_data b' <> None -> mb_data mb' + yb_len b' <= mh_lexer mh \/ mh_lexer mh + 48 <= mb_data mb').
    { intros HD. unfold buf_blocks in SEP5, ND5, RNG5. destruct (yb_data b'); [| congruence].
      cbn [abl map blk_addr blk_size fst snd app] in SEP5, ND5.
      assert (NE : ab_addr (mkABlock (mb_data mb') (yb_len b')) <> ab_addr (mkABlock (mh_lexer mh) 48)).
      { cbn [ab_addr]. intros E. pose proof (proj2 (proj1 (List.NoDup_cons_iff _ _) ND5)) as NDx.
        apply (proj1 (proj1 (List.NoDup_cons_iff _ _) NDx)). cbn [map ab_addr]. rewrite E. rewrite map_app. apply in_or_app. right. cbn [map ab_addr]. right. left. reflexivity. }
      pose proof (SEP5 (mkABlock (mb_data mb') (yb_len b')) (mkABlock (mh_lexer mh) 48) (or_intror (or_introl eq_refl)) ltac:(right; right; apply in_or_app; right; right; left; reflexivity) NE) as S.
      cbn [ab_addr ab_size] in S. clear -CEILB S. lia. }
    (* [comment removed for export] *)
    arz_seg KIPY AHK5.
    set (K' := mkALK (acc_ok (m_vm_lazy mo5) (y_aS Y sa5)) sp gp tp F5 fc5 lo T txt (mh_addr mh) (mh_lexer mh) (mb_addr (mh_lexbuf mh)) OBP OLP OT OTn
                     ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
    assert (ENV' : kenvA K') by exact LENV.
    pose proof (MKKP _ _ _ F5 fc5 LINK0 INH5 INL5 INLB5 INR5) as KP'. change (kpolA K') in KP'.
    eapply evtA_mono.
    { eapply (lex_eof_tail K' ENV' KP' BERR) with (e1 := lex_error_code (lx_error lx1)) (st := buf_state_code (yb_state b'))
        (LB := mb_addr (mh_lexbuf mh)) (bl := yb_len b') (bu := yb_used b') (bd := mb_data mb') (ba := mh_addr mh + 72) (off1 := off1) (start1 := start1) (k56 := k56') (k64 := k64')
        (shL := blk_shadow 48) (shLB := blk_shadow 32);
        kk K'; [exact FR5| exact LX5| exact BC5| exact BSR| exact HLB| clear -CEILB RLB; lia| clear -CEILB RLB; lia| clear -CEILB SLB; yshow SLB; lia
               | exact UL5| reflexivity| exact ULB5| reflexivity| exact STA5| exact ST5| exact MI5| exact ER1| exact (kp_LB _ KP')| ]. 
      pose proof (kp_LBs _ KP') as X. kkh K' X. exact X. }
    cbv beta. intros ms6 (t0f & t1f & t2f & a1f & a2f & a3f & a4f & a5f & a6f & a7f & t3f & t4f & t5f & t6f & m6 & -> & MU6 & WM6 & MI6 & ST6 & LX6 & BC6 & ULB6 & STA6).
    kkh K' MU6. kkh K' ST6. kkh K' LX6. kk K'.
    intros mo6 Hag6 HLI6 Hh6. destruct (BACK0 mo6 Hag6 HLI6) as [AHK5' R6].
    assert (WOK6 : Forall (ay_write_ok (abl (buf_blocks mb' b') ++ LK ++ mkABlock (mh_addr mh) 104 :: mkABlock (mh_lexer mh) 48 :: REST) LF) [(lo, bv_unsigned sp); (mh_lexer mh, mh_lexer mh + 48)]).
    { unfold ay_write_ok. constructor; [cbn [fst snd]; left; clear -CEILB CEIL; aceil; lia|].
      constructor; [| constructor]. cbn [fst snd]. right; left. exists (mkABlock (mh_lexer mh) 48). split; [exact INL5| cbn; lia]. }
    pose proof (FRAMEY _ _ _ _ _ _ _ AHK5' MU6 WM6 WOK6) as AHK6.
    (* [comment removed for export] *)
    set (lx2 := lx_set_buf lx1 b' 0 1).
    set (lxr := if buf_state_code (yb_state b') =? 0 then lx2 else lx_set_error lx2 LE_alloc_failed).
    set (tokr := if buf_state_code (yb_state b') =? 0 then TK_eof else TK_error).
    assert (RES : eof_ret (buf_state_code (yb_state b')) = tok_code tokr /\ eof_err (buf_state_code (yb_state b')) (lex_error_code (lx_error lx1)) = lex_error_code (lx_error lxr)
                  /\ lx_buf lxr = b' /\ lx_bufOff lxr = 0 /\ lx_bufInUse lxr = 1 /\ lx_lineOff lxr = 0 /\ lx_charOff lxr = 0
                  /\ lx_allowComments lxr = 1 /\ lx_validateUTF8 lxr = 1
                  /\ yleaf (ylex_finish lx1 txt TK_eof off1 start1) (lxr, tokr, off1, OB_null, 0)).
    { unfold eof_ret, eof_err, lxr, tokr, lx2. unfold ylex_finish. rewrite IU1, IB1.
      cbn [tok_eqb tok_code Z.eqb Pos.eqb orb negb andb ybuf_clear yb_state ybuf_zero ybind yb_len yb_data].
      destruct (yb_state b') eqn:BS;
        cbn [buf_state_code Z.eqb Pos.eqb tok_code lx_buf lx_bufOff lx_bufInUse lx_lineOff lx_charOff lx_allowComments lx_validateUTF8 lx_set_buf lx_set_error lx_error lex_error_code];
        repeat split; try reflexivity; try assumption.
      all: eapply yleaf_bind; [exact YLA|]; cbv beta iota; unfold ybuf_err; rewrite BS; cbn [buf_state_ok negb]; apply yl_ret. }
    destruct RES as (R1 & R2 & R3 & R4' & R5' & R6' & R7 & R8 & R9 & RLEAF). rewrite R1. rewrite R2 in LX6.
    eapply (CONT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F5 fc5 m6 mo6 sa5 lxr tokr off1 OB_null 0 mb' LK).
    unfold aylex_lex_rpost.
    split; [exact SO5|]. split; [eapply RRT; [exact R4| eapply RRT; [exact R5| exact R6]]|]. split; [rewrite R3; exact CRED5|].
    split.
    { split; [exact MI6|]. split; [exact ST6|]. split; [exact FRM5|]. split; [exact I|].
      eapply ay_pres_trans; [| eapply ay_pres_trans; [eapply (ay_pres_weaken Y); [exact PRES5| | | | ]|]].
      - apply (WOUT _ _ _ MUT WMT). intros x X1 X2 X3 X4 X5 X6. cbn [outside] in *. clear -CEILB X1 X2 X3 X4 X5 X6. tauto.
      - clear -CEILB LO LOSP; lia.
      - intros b Hb. right; right. exact Hb.
      - intros f Hf. exact Hf.
      - intros a Xa. cbn in Xa. destruct Xa.
      - eapply ay_pres_of_munch; [exact MU6| exact WM6|]. intros a Ha Hc Hx. cbn [outside]. split; [| split; [| exact I]].
        + eapply (ay_client_outside_stack Y BLKY LAYY _ _ _ _ _ REST (bv_unsigned sp)); [exact AHK0| exact RESTIN| clear -CEILB CEIL; aceil; lia| lia| exact Hc].
        + eapply (ay_client_outside_block Y BLKY BSHY LAYY _ _ _ _ _ REST (bv_unsigned sp) (mkABlock (mh_lexer mh) 48)); [exact AHK0| right; left; reflexivity| exact RESTL| cbn; lia| cbn; lia| lia| clear -CEILB CEIL LOSP; aceil; lia| exact Hc]. }
    split.
    { unfold ylex_lex. eapply yleaf_bind; [exact YL|]. cbv beta iota. exact RLEAF. }
    split; [reflexivity|].
    split.
    { split. 2:{ change (h_used (h_set_lex_off h lxr off1)) with (h_used h). cbn. clear -CEILB HB1 HB2 HB3 HB4 SB1 SB2 LEN OFFB. split; [lia| split; [lia| split; [lia| exact HB4]]]. }
      exists pew, pad. split; [| exact PW]. apply ahand_split. cbn [h_bytesConsumed h_set_lex_off h_stack_size h_parseError mh_decbuf].
      change (h_used (h_set_lex_off h lxr off1)) with (h_used h).
      split; [| split; [| split]]; (eapply rw_cells_transport; [| exact MU6| exact WM6| unfold alloc_cells; cbn; clear -CEILB RH RL SHL CEIL LOSP; yshow SHL; lia]);
        [exact HC05| exact OFF5| exact HC25| unfold alloc_cells in YAF5 |- *; cbn [yc_malloc_w yc_realloc_w yc_free_w ayc] in YAF5 |- *; exact YAF5]. }
    split.
    { split.
      - split; [| rewrite ?R4', ?R5', ?R6', ?R7, ?R8, ?R9; clear; lia].
        unfold lexer_cells. rewrite ?R3, ?R4', ?R5', ?R6', ?R7, ?R8, ?R9, ?MBS. exact LX6.
      - rewrite R3. eapply abuf_rep_transport; [exact BR5c| exact MU6| exact WM6| rewrite MBS; cbn; clear -CEILB RL RLB SLB CEIL LOSP; yshow SLB; lia|].
        intros HD. specialize (DSEP HD).
        pose proof (RNG5 (mkABlock (mb_data mb') (yb_len b')) ltac:(apply in_or_app; left; unfold buf_blocks; destruct (yb_data b'); [cbn; right; left; reflexivity| congruence])) as RD5.
        unfold ablock_range, ACONSTS in RD5. cbn [c_img_hi ab_addr ab_size] in RD5. aceil.
        cbn. clear -CEILB DSEP CEIL LOSP RL RD5. lia. }
    split; [exact MBS|].
    split.
    { rewrite R3. intros HD. destruct (OSD5 HD) as [OD1 OD2]. split; [| exact OD2].
      destruct OD1 as (Q8 & Qn & QU). split; [exact Q8|]. split; [exact Qn|].
      eapply (u8arr_transport bsegs); [exact QU| exact MU6| exact WM6|]. rewrite (blk_shadow_length (yb_len b')) by lia.
      unfold oshw_hi, A_SB, amem in OD2.
      pose proof (RNG5 (mkABlock (mb_data mb') (yb_len b')) ltac:(apply in_or_app; left; unfold buf_blocks; destruct (yb_data b'); [cbn; right; left; reflexivity| congruence])) as RD5.
      unfold ablock_range, ACONSTS in RD5. cbn [c_img_hi ab_addr ab_size] in RD5. aceil.
      unfold A_SB. cbn [disjoint_from fst snd]. clear -CEILB RD5 RL HL CEIL. Z.div_mod_to_equations. lia. }
    split; [cbn [outref_addr]; eapply rw_cells_transport; [exact OB5| exact MU6| exact WM6| cbn; clear -CEILB FBL FF1 FF2 LF2 CEIL; yshow FBL; lia]|].
    split; [eapply rw_cells_transport; [exact OL5| exact MU6| exact WM6| cbn; clear -CEILB FBL FF1 FF2 LF2 CEIL; yshow FBL; lia]|].
    split; [eapply text_at_transport; [exact TX5| exact MU6|]; intros Hl; destruct (TSEP Hl) as (bt & _ & X); cbn; clear -CEILB X CEIL LOSP Hl; lia|].
    split; [exact LKZ5|].
    split; [| intros X; split; [subst tokr; destruct (buf_state_code (yb_state b') =? 0); [left| right]; reflexivity| exact (proj2 (LKB5 X))]].
    rewrite R3. apply AYST_split. split.
    - eapply PERMY; [exact AHK6| | apply Permutation_refl].
      unfold SIZEOF_HANDLE, SIZEOF_LEXER. apply Permutation_sym.
      replace (mkABlock (mh_addr mh) 104 :: mkABlock (mh_lexer mh) 48 :: abl (buf_blocks mb' b') ++ LK ++ REST)
        with ([mkABlock (mh_addr mh) 104; mkABlock (mh_lexer mh) 48] ++ (abl (buf_blocks mb' b') ++ LK) ++ REST)
        by (cbn [app]; first [now rewrite <- !app_assoc | now rewrite !app_assoc | reflexivity]).
      replace (abl (buf_blocks mb' b') ++ LK ++ mkABlock (mh_addr mh) 104 :: mkABlock (mh_lexer mh) 48 :: REST)
        with ((abl (buf_blocks mb' b') ++ LK) ++ [mkABlock (mh_addr mh) 104; mkABlock (mh_lexer mh) 48] ++ REST)
        by (cbn [app]; first [now rewrite <- !app_assoc | now rewrite !app_assoc | reflexivity]).
      apply Permutation_app_swap_app.
    - eapply (aystatics_munch _ _ _ YS5 MU6 WM6). clear -CEILB CEIL RL. repeat (constructor; [cbn [fst snd]; lia|]). constructor.
  + (* [comment removed for export] *)
    destruct AT as (rav' & s1' & s2' & s6' & s9' & t0' & t1x & t2' & a0' & a1x & a2x & a3x & a4x & a5' & a6' & a7' & t3' & t4' & t5' & t6' & k56' & k64' & k112' & m2 & -> & LM2 & _).
    pose proof LM2 as (MU2 & WM2 & _). unfold kW, lexW in MU2. kkh K MU2.
    pose proof ENVT as ET. destruct ET as [_ OBSEP]. kkh K OBSEP.
    assert (OB2 : rw_cells bsegs m2 OBP [C8 (wz 0)]) by (eapply rw_cells_transport; [exact OB1| exact MU2| exact WM2| cbn; clear -CEILB OBSEP LF2 FF1 FF2 CEIL; lia]).
    assert (OL2 : rw_cells bsegs m2 OLP [C4 (wz 0)]) by (eapply rw_cells_transport; [exact OL1| exact MU2| exact WM2| cbn; clear -CEILB OBSEP LF2 FF1 FF2 CEIL; lia]).
    clear OBSEP.
    eapply evtA_mono.
    { eapply (lex_fin_walk K m1 ENV ENVT KP SH1 tok); [exact NE| exact LM2| kk K; exact OB2| kk K; exact OL2| clear -CEILB SB1 SB2 OFFB; lia| kk K; clear -CEILB SB2; lia| | exact ER1].
      intros IS. clear -CEILB TK IS SB1 SB2. destruct tok; try discriminate IS; lia. }
    cbv beta. intros ms'' (t0y & t1y & t2y & a1y & a2y & a3y & a4y & a5y & a6y & a7y & t3y & t4y & t5y & t6y & m3 & -> & MU3 & WM3 & MI3 & ST3 & OFF3 & LX3 & BC3 & OB3 & OL3).
    unfold topW, kW, lexW in MU3. kkh K MU3. kkh K ST3. kkh K OFF3. kkh K LX3. kkh K BC3. kkh K OB3. kkh K OL3. cbn [app] in MU3. kk K.
    (* [comment removed for export] *)
    intros mo3 Hag3 HLI3 Hh3. destruct (BACK mo3 Hag3 HLI3) as [AHK0' R3].
    assert (MUT : munch [(lo, bv_unsigned sp); (mh_addr mh + 32, mh_addr mh + 36); (mh_lexer mh, mh_lexer mh + 48);
                         (mb_addr (mh_lexbuf mh) + 8, mb_addr (mh_lexbuf mh) + 12); (OLP, OLP + 4); (OBP, OBP + 8)] m m3).
    { eapply munch_trans; [| exact MU3]. eapply munch_weaken; [| exact MU1]. unfold sub_fp. cbn [outside].
      intros x (X1 & X2 & X3 & X4 & X5 & X6 & _). repeat split; assumption. }
    pose proof (wmono_trans _ _ _ _ WM1 WM3) as WMT.
    pose proof (FRAMEY _ _ _ _ _ _ _ AHK0' MUT WMT WOK) as AHK3.
    pose proof (aystatics_munch _ _ _ YS MUT WMT WST) as YS3.
    eapply (CONT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m3 mo3 s lx1 tok off1 (fst (fin_ob tok start1 off1)) (snd (fin_ob tok start1 off1)) (mh_lexbuf mh) []).
    unfold aylex_lex_rpost.
    split; [reflexivity|]. split; [exact R3|]. split; [rewrite IB1; rewrite IB in CRED; exact CRED|].
    split.
    { split; [exact MI3|]. split; [exact ST3|]. split; [exact FRM|]. split; [exact I|].
      apply (WOUT _ _ _ MUT WMT). intros x X1 X2 X3 X4 X5 X6. cbn [outside] in *. clear -CEILB X1 X2 X3 X4 X5 X6. tauto. }
    split.
    { unfold ylex_lex. eapply yleaf_bind; [exact YL|]. cbv beta iota.
      unfold ylex_finish. rewrite (tok_eqb_eof_false tok NE), IU1. cbn [orb negb Z.eqb].
      unfold fin_ob. destruct (tok_eqb tok TK_error) eqn:TE; cbn [negb fst snd].
      - apply yl_ret.
      - destruct (is_string_tok tok) eqn:IS.
        + unfold yassert. replace (2 <=? off1 - start1) with true by (symmetry; apply Z.leb_le; clear -CEILB TK IS SB1 SB2; destruct tok; try discriminate IS; lia).
          cbn [ybind]. apply yl_ret.
        + apply yl_ret. }
    split; [reflexivity|].
    split.
    { split. 2:{ change (h_used (h_set_lex_off h lx1 off1)) with (h_used h). cbn. clear -CEILB HB1 HB2 HB3 HB4 SB1 SB2 LEN OFFB. split; [lia| split; [lia| split; [lia| exact HB4]]]. }
      exists pew, pad. split; [| exact PW]. apply ahand_split. cbn [h_bytesConsumed h_set_lex_off h_stack_size h_parseError mh_decbuf].
      change (h_used (h_set_lex_off h lx1 off1)) with (h_used h).
      split; [| split; [exact OFF3| split]]; (eapply rw_cells_transport; [| exact MUT| exact WMT| unfold alloc_cells; cbn; clear -CEILB RH RL RLB SHL SHB FBH CEIL LOSP FF1 FF2; yshow SHL; yshow SHB; yshow FBH; lia]);
        [exact HC0| exact HC2| exact YAF]. }
    split.
    { split.
      - split; [| clear -CEILB IL1 ICH1 IO1 IU1 IA1 IV1; rewrite IL1, ICH1, IO1, IU1, IA1, IV1; lia]. rewrite (lxcells_of_lexer _ _ _ LI1). exact LX3.
      - rewrite IB1. split; [split; [rewrite D0; exact BC3| split; [exact BI| cbn; lia]]|]. split; [exact BD| exact BF]. }
    split; [split; reflexivity|].
    split; [intros X; exfalso; apply X; rewrite IB1; reflexivity|].
    split; [rewrite D0; exact OB3|]. split; [exact OL3|].
    split; [eapply text_at_transport; [exact TX| exact MUT|]; intros Hl; destruct (TSEP Hl) as (bt & _ & X); cbn; clear -CEILB X CEIL FF1 FF2 Hl LOSP; lia|].
    split; [reflexivity|].
    split; [| intros X; exfalso; apply X; reflexivity].
    unfold buf_blocks. rewrite IB1. cbn [abl map blk_addr blk_size fst snd app].
    apply AYST_split. split; [exact AHK3| exact YS3].
Qed.
End W.
End RC__1.
