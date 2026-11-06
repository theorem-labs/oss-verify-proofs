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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import B_iface BYajlRep BYajl_iface BY_rz BY_hand BY_acct_needs BY_parse_kit BY_parse_head BY_parse_lex.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac aceil := first [pose proof alloc_ceiling_range as CEILB | idtac].
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition mh_set_lexbuf (mh : mhand) (mbl : mbuf) : mhand :=
  mkMH (mh_id mh) (mh_addr mh) (mh_lid mh) (mh_lexer mh) mbl (mh_decbuf mh) (mh_sid mh) (mh_stack mh) (mh_ctx mh).

(* [comment removed for export] *)
Section W.
Variable Y : ay_params.
Hypothesis KIPY : AHK_y_kip_stmt Y.
Hypothesis FRAMEY : AHK_y_frame_stmt Y.
Hypothesis BLKY : AHK_y_blocks_stmt Y.
Hypothesis BSHY : AHK_y_block_shadow_stmt Y.
Hypothesis LAYY : AHK_y_layout_stmt Y.
Hypothesis PERMY : AHK_y_perm_stmt Y.
Hypothesis RRT : ayR_trans_stmt Y.
Hypothesis YLX : aylex_lex_stmt Y.
Variable URA : list Z.
Hypothesis USTEP : forall m SP ra s0 ra' s0', In (bv_unsigned ra) URA -> SP + 16 <= bv_unsigned s0 < 2^47 ->
    rw_cells bsegs m (bv_unsigned s0 - 16) [C8 s0'; C8 ra'] -> y_uanchor Y m (bv_unsigned s0) ra' s0' -> y_uanchor Y m SP ra s0.
Hypothesis URA_lex : forall pc, lex_site pc -> In (pc + 48) URA.
(* [comment removed for export] *)
Hypothesis FFRESH_dummy : True.
Hypothesis UFRAME : forall m m' SP ra s0, (forall a, SP <= a < 2^47 -> m' (wa a) = m (wa a)) -> y_uanchor Y m SP ra s0 -> y_uanchor Y m' SP ra s0.
(* [comment removed for export] *)
Hypothesis NONNEG : yacct_nonneg_stmt Y.
Variable phr : Z -> Z -> Z -> Z -> Z.
Hypothesis YSPLIT : yphi_hand_split_stmt Y phr.
Lemma yh_lex1 : forall h L, y_phi_buf Y (lx_buf (h_lexer h)) <= y_phi_hand Y h L.
Proof. aceil.
  intros h L. destruct YSPLIT as (EQ & NN & _). destruct NONNEG as (_ & NB & _ & _).
  rewrite (EQ h L). pose proof (NB (h_decbuf h)). pose proof (NN (h_bytesConsumed h) (h_used h) (h_stack_size h) L). lia.
Qed.

(* [comment removed for export] *)
Lemma lex_call : forall (E : apE Y) pc m mo s LK h mh cx obw olw cr (F : bvmap 5 word) (fc : bv 32)
    (t0 t1 t2 a6 a7 s2v s4v s5v t3 t4 t5 t6 : word),
  penvA E -> pok E h cx -> pmem E m mo s LK h mh cx obw olw cr -> y_phi_hand Y h (pLEN E) <= cr -> frm0 fc -> hinv (pLEN E) h cx -> lex_site pc ->
  (nbig LK = 0) ->
  (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) m' mo' s' lx' tok off' ob n mbl' LK',
     yleaf (ylex_lex (h_lexer h) (p_txt E) (pLEN E) (h_bytesConsumed h)) (lx', tok, off', ob, n) ->
     lex_post (p_txt E) (pLEN E) (h_bytesConsumed h) (lx', tok, off', ob, n) -> frm0 fc' ->
     (LK' <> [] -> (tok = TK_eof \/ tok = TK_error) /\ length LK' = 1%nat) ->
     pmem E m' mo' s' (LK' ++ LK) (h_set_lex_off h lx' off') (mh_set_lexbuf mh mbl') cx (wz (outref_addr (p_T E) (mb_data mbl') ob)) (wz n)
          (cr - y_phi_buf Y (lx_buf (h_lexer h)) + y_phi_buf Y (lx_buf lx')) ->
     ppot phr E h (h_set_lex_off h lx' off') (cr - y_phi_buf Y (lx_buf (h_lexer h)) + y_phi_buf Y (lx_buf lx')) ->
     realizes_cfg acfg bsegs (mkCfg (pstate E (pc + 48) F' fc' m' (wz (pc + 48)) t0' t1' t2' (wz (tok_code tok)) a1' a2' a3' a4' a5' a6' a7' s2v s4v s5v t3' t4' t5' t6') mo') (p_K E)) ->
  realizes_cfg acfg bsegs (mkCfg (pstate E AY_LEX_LEX F fc m (wz (pc + 48)) t0 t1 t2 (wz (mh_lexer mh)) (wz (p_T E)) (wz (pLEN E)) (wz (pH E + 32))
                                  (wz (p_ff E + 32)) (wz (p_ff E + 64)) a6 a7 s2v s4v s5v t3 t4 t5 t6) mo) (p_K E).
Proof. aceil.
  intros until t6. intros PA OK PM HCR FRM HINV SITE NB0 CONT.
  pose proof PM as (AY & HR & SAME & CXR & TXT & (k0 & k224 & FR) & SV & FF & OCX & STK & GAP & MI & PRES & UA & (CRED & CR0) & (SO1 & R1) & SB1 & LKZ).
  pose proof OK as (K0 & LP & U0 & (SB0 & SZM) & TB & OTB & (f & FIN & FCX & FCL) & LC0 & NBIG & RR0 & TP & FFP & FFR0).
  pose proof HINV as (LXI & OFFB & DBI & DBOK & STI & DEPTH & SZB).
  apply AYST_split in AY. destruct AY as [AHK YS].
  pose proof HR as (HS & LXR & DBR & BSR). pose proof HS as (_ & BC1 & BC2 & BC3 & BC4).
  assert (SZ : 0 < h_stack_size h) by (clear -CEILB STI; destruct STI as (_ & _ & _ & (k & Hk & E0) & _); unfold YAJL_BS_INC in E0; lia).
  pose proof (mk_pblk BLKY LAYY BSHY E s LK h mh h cx m mo PA OK AHK SAME SB1 SZ) as PB.
  destruct (BLKY _ _ _ _ _ AHK) as (RNG & _ & _).
  openPA PA. openPB PB. pose proof SAME as (EH & EL & ELB & EDB & ECX).
  unfold pstate.
  (* [comment removed for export] *)
  set (REST' := (abl (buf_blocks (mh_decbuf mh) (h_decbuf h)) ++ abl (bs_blocks (mh_sid mh) (mh_stack mh) h)) ++ LK ++ p_REST E).
  assert (ELB0 : abl (yblocks mh h) ++ LK ++ p_REST E
                 = mkABlock (mh_addr mh) SIZEOF_HANDLE :: mkABlock (mh_lexer mh) SIZEOF_LEXER :: abl (buf_blocks (mh_lexbuf mh) (lx_buf (h_lexer h))) ++ REST').
  { unfold yblocks, lexer_blocks, REST', abl. cbn [map app MallocBlocks.blk_addr MallocBlocks.blk_size fst snd]. rewrite !map_app.
    cbn [map app MallocBlocks.blk_addr MallocBlocks.blk_size fst snd]. rewrite <- !app_assoc. reflexivity. }
  assert (INR' : forall b, In b (p_REST E) -> In b REST') by (intros b Hb; unfold REST'; apply in_or_app; right; apply in_or_app; right; exact Hb).
  assert (INRO : forall b, In b (p_REST E) -> In b (abl (yblocks mh h) ++ LK ++ p_REST E)) by (intros b Hb; apply in_or_app; right; apply in_or_app; right; exact Hb).
  assert (INRW : forall b, In b (p_REST E) -> In b (mkABlock (mh_addr mh) SIZEOF_HANDLE :: mkABlock (mh_lexer mh) SIZEOF_LEXER :: abl (buf_blocks (mh_lexbuf mh) (lx_buf (h_lexer h))) ++ REST'))
    by (intros b Hb; right; right; apply in_or_app; right; apply INR'; exact Hb).
  (* [comment removed for export] *)
  assert (IN : forall b, In b (abl (yblocks mh h)) -> In b (abl (yblocks mh h) ++ LK ++ p_REST E)) by (intros b Hb; apply in_or_app; left; exact Hb).
  pose proof (proj1 (BSHY _ _ _ _ _ _ AHK (IN _ (yb_in_hand mh h)) ltac:(cbn; unfold SIZEOF_HANDLE; lia))) as OSH_H. cbn [ab_addr ab_size] in OSH_H.
  pose proof (proj1 (BSHY _ _ _ _ _ _ AHK (IN _ (yb_in_lexer mh h)) ltac:(cbn; unfold SIZEOF_LEXER; lia))) as OSH_L. cbn [ab_addr ab_size] in OSH_L.
  pose proof (proj1 (BSHY _ _ _ _ _ _ AHK (IN _ (yb_in_lexbuf mh h)) ltac:(cbn; unfold SIZEOF_BUF; lia))) as OSH_LB. cbn [ab_addr ab_size] in OSH_LB.
  rewrite ELB0 in AHK.
  pose proof (sub_chunk m _ [C8 (p_fs0 E); C8 (p_s11 E); C8 (p_s10 E); C8 (p_s9 E); C8 (p_s8 E); C8 (p_s7 E); C8 (p_s6 E); C8 (p_s5 E); C8 (p_s4 E); C8 (p_s3 E); C8 (p_s2 E); C8 (p_s1 E)]
               [C8 (p_s0 E); C8 (p_ra E)] [] ltac:(rewrite app_nil_r; exact SV)) as SV16.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in SV16. replace (bv_unsigned (p_sp E) - 112 + 96) with (bv_unsigned (p_sp E) - 16) in SV16 by lia.
  pose proof FF as (FFA & FOB & FJ2 & FOL & FJ3 & FSH).
  pose proof (bv_unsigned_in_range 64 (p_sp E)) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (TSHX : exists OT' OTn', zlength (p_txt E) = 0 \/ (oshadow m OT' OTn' /\ OT' <= p_T E /\ p_T E + zlength (p_txt E) <= OT' + OTn' /\ amem OT' OTn'
                       /\ OT' + OTn' <= alloc_ceiling /\ (exists bt, In bt REST' /\ ab_addr bt <= OT' /\ OT' + OTn' <= ab_addr bt + ab_size bt))).
  { destruct (Z.eq_dec (zlength (p_txt E)) 0) as [Z0|NZ]; [exists 0, 0; left; exact Z0|].
    destruct TB as [(bt & Hbt & B1 & B2)| Z0]; [| exfalso; clear -CEILB Z0 NZ; lia].
    pose proof (RNG bt (INRO _ Hbt)) as RT. unfold ablock_range, ACONSTS in RT. cbn [c_img_hi] in RT.
    destruct (BSHY _ _ _ _ _ bt AHK (INRW _ Hbt) ltac:(clear -CEILB B1 B2 NZ pa_len0; lia)) as [OSB OHI].
    exists (ab_addr bt), (ab_size bt). right.
    split; [exact OSB|]. split; [exact B1|]. split; [exact B2|]. split; [exact OHI|]. split; [clear -CEILB RT; lia|].
    exists bt. split; [apply INR'; exact Hbt| clear -CEILB B1; lia]. }
  destruct TSHX as (OT' & OTn' & TSH').
  eapply (YLX (pLF E) REST' h mh (p_T E) (p_txt E) (h_bytesConsumed h) (p_ff E + 32) (p_ff E + 64) OT' OTn' obw olw (p_lo E)
              (p_RR E + (cr - y_phi_buf Y (lx_buf (h_lexer h)))) (p_K E));
    [ hnf; clear -CEILB pa_ff0; split; Z.div_mod_to_equations; lia   (* [comment removed for export] *)
    | exact K0
    | apply AYST_split; split; [exact AHK| exact YS]
    | exact HS | exact LXR | exact LXI | reflexivity | exact OFFB | clear -CEILB pa_len0; lia | exact TXT | clear -CEILB pa_T0; lia
    | destruct TB as [(bt & Hbt & B1 & B2)| Z0]; [left; exists bt; split; [apply INR'; exact Hbt| split; [exact B1| exact B2]]| right; exact Z0]
    | exact TSH'
    | exact OSH_H | exact OSH_L | exact OSH_LB
    | exact FOB | exact FOL
    | exact (pff_oshadow_OB E m obw olw PA FF) | exact (pff_oshadow_OL E m obw olw PA FF)
    | exists (1, p_ff E); split; [left; reflexivity|]; cbn [fst snd]; split; [reflexivity|]; split; [lia| reflexivity]
    | unfold ayframe_pre, AY_LEX_LEX_STACK, AY_BUF_APPEND_STACK, AMALLOC_STACK; aceil;
      rewrite unsigned_lit by (clear -CEILB pa_SQ0 pa_ceil0 pa_lo0 SPR; lia);
      split; [exact STK|]; split; [clear -CEILB pa_ceil0; lia|]; split; [clear -CEILB pa_SQ0 pa_lo0; lia|]; split; [clear -CEILB pa_SQ0 pa_sp0; lia|];
      split; [clear -CEILB pa_SQ0; Z.div_mod_to_equations; lia|]; split; [exact MI|]; split; [exact TP| exact FRM]
    | reflexivity | reflexivity | reflexivity | rewrite EH; reflexivity | reflexivity | reflexivity
    | clear -CEILB CRED; lia
    | pose proof (yh_lex1 h (zlength (p_txt E))); clear -CEILB H RR0 HCR; lia
    | (* [comment removed for export] *)
      unfold REST'; unfold nbig in NBIG, NB0 |- *; rewrite !List.filter_app, !length_app, !Nat2Z.inj_add;
      assert (A1 : Z.of_nat (length (List.filter (fun b => 64512 <? ab_size b) (abl (buf_blocks (mh_decbuf mh) (h_decbuf h))))) <= 1)
        by (unfold buf_blocks, abl, SIZEOF_BUF; destruct (yb_data (h_decbuf h));
            cbn [map List.filter length ab_size MallocBlocks.blk_addr MallocBlocks.blk_size fst snd Z.ltb Z.compare Pos.compare Pos.compare_cont];
            [destruct (64512 <? yb_len (h_decbuf h)); cbn [length]; lia| lia]);
      assert (A2 : Z.of_nat (length (List.filter (fun b => 64512 <? ab_size b) (abl (bs_blocks (mh_sid mh) (mh_stack mh) h)))) <= 1)
        by (unfold bs_blocks, abl; destruct (h_stack_blk h);
            cbn [map List.filter length ab_size MallocBlocks.blk_addr MallocBlocks.blk_size fst snd];
            [destruct (64512 <? h_stack_size h); cbn [length]; lia| lia]);
      clear -CEILB A1 A2 NBIG NB0; lia
    | rewrite unsigned_lit by (clear -CEILB pa_SQ0 pa_ceil0 pa_lo0 SPR; lia);
      eapply USTEP; [unfold wz; rewrite unsigned_lit by (clear -CEILB SITE; unfold lex_site in SITE; lia); apply URA_lex; exact SITE
                    | clear -CEILB pa_SQ0 pa_sp0; lia | exact SV16 | exact UA]
    | ].
  cbv beta. intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F2 fc2 m2 mo2 s2 lx' tok off' ob n mbl' LK' POST.
  destruct POST as (SO2 & R2 & CRED2 & (MI2 & ST2 & FRM2 & _ & PRES2) & YL & A0' & HS2 & LXR2 & MBS & OSHD & OB2 & OL2 & TXT2 & LKZ2 & AY2 & LKT).
  pose proof (ypost_yleaf _ _ _ (ylex_lex_post (h_lexer h) (p_txt E) (zlength (p_txt E)) (h_bytesConsumed h) eq_refl ltac:(clear -CEILB pa_len0; lia) LXI OFFB) YL) as LPOST.
  subst a0'. unfold wz. rewrite (ret_pc_even (pc + 48)) by (clear -CEILB SITE; unfold lex_site in SITE; lia).
  rewrite unsigned_lit in PRES2, ST2 by (clear -CEILB pa_SQ0 pa_ceil0 pa_lo0 SPR; lia).
  unfold pstate, wz in CONT. eapply CONT; [exact YL| exact LPOST| exact FRM2| exact LKT| |].
  2:{ (* [comment removed for export] *) unfold ppot. cbn [h_set_lex_off h_lexer h_decbuf]. destruct YSPLIT as (EQ & _). rewrite (EQ h (zlength (p_txt E))) in HCR. clear -CEILB HCR. lia. }
  (* [comment removed for export] *)
  pose proof (ay_pres_agree _ _ _ _ _ _ PRES2) as AG.
  apply AYST_split in AY2. destruct AY2 as [AHK2 YS2].
  pose proof MBS as MBA. unfold mb_same in MBA. cbn [mh_lexbuf] in MBA.
  destruct (LAYY _ _ _ _ _ AHK) as (LAYF & LAYFB & LAYFF).
  (* [comment removed for export] *)
  assert (RCL : forall b a, In b REST' -> ab_addr b <= a < ab_addr b + ab_size b ->
            ay_client_addr REST' (pLF E) (p_SQ E) a /\ ~ yin_ivs [(p_ff E + 64, p_ff E + 64 + 4); (p_ff E + 32, p_ff E + 32 + 8)] a).
  { intros b a Hb Ha. split; [right; left; exists b; split; [exact Hb| exact Ha]|].
    pose proof (proj1 (LAYFB (1, p_ff E) b (or_introl eq_refl) ltac:(right; right; apply in_or_app; right; exact Hb))) as D. cbn [fst snd] in D.
    unfold ff_bytes in D. change (Z.shiftl 64 1) with 128 in D. cbn [yin_ivs fst snd]. clear -CEILB D Ha. lia. }
  assert (IDB : In (mkABlock (mb_addr (mh_decbuf mh)) SIZEOF_BUF) REST') by (unfold REST', abl, buf_blocks; apply in_or_app; left; apply in_or_app; left; left; reflexivity).
  assert (IDD : forall d, yb_data (h_decbuf h) = Some d -> In (mkABlock (mb_data (mh_decbuf mh)) (yb_len (h_decbuf h))) REST').
  { intros d Hd. unfold REST', abl, buf_blocks. rewrite Hd. apply in_or_app; left. apply in_or_app; left. right; left; reflexivity. }
  assert (ISB : In (mkABlock (mh_stack mh) (h_stack_size h)) REST').
  { unfold REST', abl, bs_blocks. destruct (h_stack_blk h); [| exfalso; apply SB1; reflexivity]. apply in_or_app; left. apply in_or_app; right. left; reflexivity. }
  (* [comment removed for export] *)
  assert (HICL : forall a, p_SQ E <= a -> (a < p_ff E + 32 \/ p_ff E + 128 <= a) ->
            ay_client_addr REST' (pLF E) (p_SQ E) a /\ ~ yin_ivs [(p_ff E + 64, p_ff E + 64 + 4); (p_ff E + 32, p_ff E + 32 + 8)] a).
  { intros a Ha Hf. split; [left; exact Ha|]. cbn [yin_ivs fst snd]. clear -CEILB Hf. lia. }
  (* [comment removed for export] *)
  assert (CXCL : forall a, (mh_ctx (p_mh E) <= a < mh_ctx (p_mh E) + 8 \/ A_SB + mh_ctx (p_mh E) / 8 <= a < A_SB + mh_ctx (p_mh E) / 8 + 1) ->
            ay_client_addr REST' (pLF E) (p_SQ E) a /\ ~ yin_ivs [(p_ff E + 64, p_ff E + 64 + 4); (p_ff E + 32, p_ff E + 32 + 8)] a).
  { intros a Ha. split.
    - right; right; left. exists f. split; [right; exact FIN|]. rewrite FCL. unfold ff_bytes. change (Z.shiftl 64 1) with 128. change (Z.shiftl 8 1) with 16.
      clear -CEILB Ha FCX pa_CX0. unfold A_SB in *. Z.div_mod_to_equations. lia.
    - cbn [yin_ivs fst snd]. yshow pa_ffP0. clear -CEILB Ha FCX pa_ffCX0 pa_CX0 pa_ff0 pa_ffP0. unfold A_SB in *. lia. }
  split.
  { apply AYST_split. split; [| exact YS2]. eapply PERMY; [exact AHK2| | apply Permutation_refl].
    unfold yblocks, lexer_blocks, abl, REST'. cbn [mh_set_lexbuf mh_id mh_addr mh_lid mh_lexer mh_lexbuf mh_decbuf mh_sid mh_stack h_set_lex_off h_lexer h_decbuf map app MallocBlocks.blk_addr MallocBlocks.blk_size fst snd].
    rewrite !map_app. apply perm_skip. apply perm_skip.
    replace (bs_blocks (mh_sid mh) (mh_stack mh) (h_set_lex_off h lx' off')) with (bs_blocks (mh_sid mh) (mh_stack mh) h) by reflexivity.
    set (Dd := map _ (buf_blocks (mh_decbuf mh) (h_decbuf h))). set (Ss := map _ (bs_blocks (mh_sid mh) (mh_stack mh) h)).
    rewrite <- !app_assoc. apply Permutation_app_head.
    transitivity ((Dd ++ Ss) ++ LK' ++ LK ++ p_REST E); [| rewrite <- app_assoc; apply Permutation_refl].
    replace (LK' ++ Dd ++ Ss ++ LK ++ p_REST E) with (LK' ++ (Dd ++ Ss) ++ (LK ++ p_REST E)) by (rewrite <- !app_assoc; reflexivity).
    apply Permutation_app_swap_app. }
  split.
  { split; [exact HS2|]. split; [exact LXR2|]. cbn [mh_set_lexbuf mh_decbuf mh_addr mh_stack h_set_lex_off h_decbuf]. split.
    - eapply buf_rep_agree; [exact AG| exact DBR| |].
      + intros a Ha. eapply RCL; [exact IDB| cbn [ab_addr ab_size]; unfold SIZEOF_BUF in *; clear -CEILB Ha; lia].
      + intros HD a Ha. destruct (yb_data (h_decbuf h)) as [d|] eqn:Hd; [| exfalso; apply HD; reflexivity].
        eapply RCL; [exact (IDD d eq_refl)| cbn [ab_addr ab_size]; clear -CEILB Ha; lia].
    - eapply bs_rep_agree; [exact AG| | | unfold h_used; cbn [h_stack h_stack_size h_set_lex_off]; unfold h_used in BC3; clear -CEILB BC3; lia].
      + unfold RYajlRep.bs_rep in BSR |- *. cbn [h_stack_blk h_set_lex_off]. destruct (h_stack_blk h); [| exfalso; apply SB1; reflexivity].
        cbn [h_stack h_stack_size h_set_lex_off]. replace (h_used (h_set_lex_off h lx' off')) with (h_used h) by reflexivity. exact BSR.
      + cbn [h_stack_size h_set_lex_off]. intros a Ha. eapply RCL; [exact ISB| cbn [ab_addr ab_size]; clear -CEILB Ha; lia]. }
  split.
  { unfold mh_same. cbn [mh_set_lexbuf mh_id mh_addr mh_lid mh_lexer mh_lexbuf mh_decbuf mh_sid mh_stack mh_ctx]. rewrite MBA. exact SAME. }
  split. { eapply ctx_rep_agree; [exact AG| exact CXR|]. intros a Ha. apply CXCL. left. exact Ha. }
  split; [exact TXT2|].
  split.
  { exists k0, k224. eapply rw_cells_agree; [exact AG| exact FR|]. intros a Ha. apply HICL; [clear -CEILB Ha; lia|].
    unfold pframe in Ha. cbn [cells_size csize Nat.add] in Ha. clear -CEILB Ha pa_SQ0 pa_ff0 pa_ceil0 pa_lo0. lia. }
  split.
  { eapply rw_cells_agree; [exact AG| exact SV|]. intros a Ha. apply HICL; [clear -CEILB Ha pa_SQ0; lia|].
    unfold psaved in Ha. cbn [cells_size csize Nat.add] in Ha. clear -CEILB Ha pa_SQ0 pa_ff0 pa_ceil0 pa_lo0. lia. }
  split.
  { (* [comment removed for export] *)
    assert (FFCL : forall a, ((p_ff E <= a < p_ff E + 32) \/ (p_ff E + 40 <= a < p_ff E + 64) \/ (p_ff E + 68 <= a < p_ff E + 128)
                              \/ (p_ff E / 8 + 2147450880 <= a < p_ff E / 8 + 2147450880 + 16)) ->
              ay_client_addr REST' (pLF E) (p_SQ E) a /\ ~ yin_ivs [(p_ff E + 64, p_ff E + 64 + 4); (p_ff E + 32, p_ff E + 32 + 8)] a).
    { intros a Ha. split.
      - right; right; left. exists (1, p_ff E). split; [left; reflexivity|]. cbn [fst snd]. unfold ff_bytes, oshw_lo, A_SB. change (Z.shiftl 64 1) with 128. change (Z.shiftl 8 1) with 16.
        clear -CEILB Ha pa_ff0. Z.div_mod_to_equations. lia.
      - cbn [yin_ivs fst snd]. yshow pa_ffP0. clear -CEILB Ha pa_ff0 pa_ffP0. lia. }
    destruct pa_j0 as (J1 & J2 & J3).
    split; [eapply rw_cells_agree; [exact AG| exact FFA| intros a Ha; apply FFCL; unfold pffA in Ha; cbn [cells_size csize Nat.add] in Ha; clear -CEILB Ha; lia]|].
    split; [exact OB2|].
    split; [eapply rw_cells_agree; [exact AG| exact FJ2| intros a Ha; apply FFCL; cbn [cells_size csize Nat.add] in Ha; clear -CEILB Ha; lia]|].
    split; [exact OL2|].
    split; [eapply rw_cells_agree; [exact AG| exact FJ3| intros a Ha; apply FFCL; unfold pffZ in Ha; cbn [cells_size csize Nat.add] in Ha; clear -CEILB Ha; lia]|].
    eapply rw_cells_agree; [exact AG| exact FSH| intros a Ha; apply FFCL; unfold pffsh in Ha; cbn [cells_size csize Nat.add] in Ha; clear -CEILB Ha; lia]. }
  split. { eapply oshadow_agree; [exact AG| exact OCX|]. intros a Ha. apply CXCL. right. revert Ha. unfold oshw_lo, oshw_hi, A_SB, amem. clear. intros Ha. Z.div_mod_to_equations. lia. }
  split; [exact ST2|].
  split. { eapply stk_agree; [exact AG| exact GAP|]. intros a Ha. apply HICL; clear -CEILB Ha pa_SQ0 pa_ff0 pa_ceil0 pa_lo0; lia. }
  split; [exact MI2|].
  split.
  { eapply ay_pres_trans; [exact PRES|]. intros a Ha Hc Hx. apply PRES2; [exact Ha| |].
    - destruct Hc as [Hc|[Hc|[Hc|Hc]]].
      + left. clear -CEILB Hc pa_SQ0. lia.
      + right; left. destruct Hc as (b & Hb & Hr). exists b. split; [apply INR'; exact Hb| exact Hr].
      + right; right; left. destruct Hc as (f' & Hf' & Hr). exists f'. split; [right; exact Hf'| exact Hr].
      + right; right; right. exact Hc.
    - (* [comment removed for export] *)
      cbn [yin_ivs fst snd]. destruct Hc as [Hc|[Hc|[Hc|Hc]]].
      + clear -CEILB Hc pa_ff0 pa_ceil0 pa_lo0. lia.
      + destruct Hc as (b & Hb & Hr). pose proof (proj1 (LAYFB (1, p_ff E) b (or_introl eq_refl) (INRW _ Hb))) as D. cbn [fst snd] in D.
        unfold ff_bytes in D. change (Z.shiftl 64 1) with 128 in D. clear -CEILB D Hr. lia.
      + destruct Hc as (f' & Hf' & Hr). pose proof (FFR0 f' Hf') as D.
        pose proof (LAYF f' (or_intror Hf')) as (F1' & F2' & _ & F4' & _). aceil.
        destruct Hr as [Hr|Hr]; [clear -CEILB D Hr; lia|].
        yshow pa_ffP0. revert Hr F1' F2' F4' pa_ff0 pa_ffP0 CEILB. clear. unfold oshw_lo, oshw_hi, A_SB, amem. intros Hr F1' F2' F4' PFF PFFP CEILB.
        assert (E0 : fst f' = 0 \/ fst f' = 1) by lia.
        destruct E0 as [E0|E0]; rewrite E0 in Hr, F1', F2';
          [change (Z.shiftl 8 0) with 8 in Hr; change (ff_bytes 0) with 64 in F1', F2'| change (Z.shiftl 8 1) with 16 in Hr; change (ff_bytes 1) with 128 in F1', F2']; lia.
      + unfold ay_static in Hc. clear -CEILB Hc pa_ff0. lia. }
  split.
  { eapply UFRAME; [| exact UA]. intros a Ha. apply (proj1 (PRES2 a ltac:(clear -CEILB Ha SPR; lia) ltac:(left; clear -CEILB Ha pa_SQ0; lia) ltac:(cbn [yin_ivs fst snd]; clear -CEILB Ha pa_ff0 pa_ceil0 pa_lo0; lia))). }
  split. { pose proof (yh_lex1 h (zlength (p_txt E))) as Y1. destruct NONNEG as (_ & NB & _ & _). pose proof (NB (lx_buf lx')) as Y0. clear -CEILB Y1 Y0 CRED2 HCR. split; lia. }
  split. { split; [rewrite SO2; exact SO1| eapply RRT; [exact R1| exact R2]]. }
  split; [exact SB1| lk_nil].   (* [comment removed for export] *)
Qed.
(* [comment removed for export] *)
Lemma pass_lex : forall (E : apE Y) (F : bvmap 5 word) (fc : bv 32) m mo s LK h mh cx
    (rav t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2v s5v t3 t4 t5 t6 : word) st rest,
  penvA E -> phead_inv E fc m mo s LK h mh cx -> h_stack h = st :: rest -> lex_state st = true ->
  (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) m' mo' s' lx' tok off' ob n mbl' LK' cr',
     yleaf (ylex_lex (h_lexer h) (p_txt E) (pLEN E) (h_bytesConsumed h)) (lx', tok, off', ob, n) ->
     lex_post (p_txt E) (pLEN E) (h_bytesConsumed h) (lx', tok, off', ob, n) -> hinv (pLEN E) h cx -> frm0 fc' ->
     (LK' <> [] -> (tok = TK_eof \/ tok = TK_error) /\ length LK' = 1%nat) ->
     pmem E m' mo' s' (LK' ++ LK) (h_set_lex_off h lx' off') (mh_set_lexbuf mh mbl') cx (wz (outref_addr (p_T E) (mb_data mbl') ob)) (wz n) cr' ->
     ppot phr E h (h_set_lex_off h lx' off') cr' ->
     realizes_cfg acfg bsegs (mkCfg (pstate E (state_targetA st + 48) F' fc' m' (wz (state_targetA st + 48)) t0' t1' t2' (wz (tok_code tok)) a1' a2' a3' a4' a5' a6' a7'
                                    (wz 0) (wz (p_ff E)) s5v t3' t4' t5' t6') mo') (p_K E)) ->
  realizes_cfg acfg bsegs (mkCfg (phead E F fc m (h_used h) rav t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2v s5v t3 t4 t5 t6) mo) (p_K E).
Proof. aceil.
  intros until rest. intros PA HI HST LS CONT.
  destruct HI as ((obw & olw & cr & PM & PCR) & OK & FRM & PLK).
  pose proof (proj2 PCR _ _ HST LS) as HCR.
  assert (NB0 : nbig LK = 0) by (rewrite (plk_ok_lex LK h st rest PLK HST LS); reflexivity). clear PLK.
  pose proof PM as (AY & HR & SAME & CXR & TXT & (k0 & k224 & FR) & SV & FF & OCX & STK & GAP & MI & PRES & UA & (CRED & CR0) & (SO1 & R1) & SB1 & LKZ).
  pose proof OK as (K0 & LP & U0 & (SB0 & SZM) & TB & OTB & (f & FIN & FCX & FCL) & LC0 & NBIG & RR0 & TP & FFP & FFR0).
  assert (HINV : hinv (zlength (p_txt E)) h cx).
  { destruct LP as [HI'|(_ & s0 & rest0 & HS0 & HE0)]; [exact HI'|]. exfalso. rewrite HST in HS0. injection HS0 as <- <-. destruct st; discriminate. }
  pose proof HINV as (LXI & OFFB & DBI & DBOK & STI & DEPTH & SZB).
  apply AYST_split in AY. destruct AY as [AHK YS].
  pose proof HR as (HS & LXR & DBR & BSR). pose proof HS as ((pew & pad & HC & PW) & BC1 & BC2 & BC3 & BC4).
  assert (SZ : 0 < h_stack_size h) by (clear -CEILB STI; destruct STI as (_ & _ & _ & (k & Hk & E0) & _); unfold YAJL_BS_INC in E0; lia).
  assert (SZ8 : h_stack_size h mod 8 = 0) by (clear -CEILB STI; destruct STI as (_ & _ & _ & (k & Hk & E0) & _); unfold YAJL_BS_INC in E0; rewrite E0; Z.div_mod_to_equations; lia).
  pose proof (mk_pblk BLKY LAYY BSHY E s LK h mh h cx m mo PA OK AHK SAME SB1 SZ) as PB.
  openPA PA. openPB PB. pose proof SAME as (EH & EL & ELB & EDB & ECX).
  assert (USED : h_used h = zlength rest + 1) by (unfold h_used; rewrite HST; unfold zlength; cbn [length]; lia).
  assert (IN : forall b, In b (abl (yblocks mh h)) -> In b (abl (yblocks mh h) ++ LK ++ p_REST E)) by (intros b Hb; apply in_or_app; left; exact Hb).
  pose proof (proj1 (BSHY _ _ _ _ _ _ AHK (IN _ (yb_in_hand mh h)) ltac:(cbn; unfold SIZEOF_HANDLE; lia))) as OSH_H. cbn [ab_addr ab_size] in OSH_H.
  pose proof (proj1 (BSHY _ _ _ _ _ _ AHK (IN _ (yb_in_stack mh h SB1)) ltac:(cbn; lia))) as OSH_S. cbn [ab_addr ab_size] in OSH_S.
  unfold oshadow, A_SB in OSH_H, OSH_S. destruct OSH_H as (_ & _ & SHH). destruct OSH_S as (_ & _ & SHS).
  assert (SCX : exists junk, rw_cells bsegs m (mh_stack mh) [CB (Z.to_nat (h_used h)) (zbytes (stack_bytes (h_stack h))); CB (Z.to_nat (h_stack_size h - h_used h)) junk]).
  { clear -CEILB BSR SB1. unfold RYajlRep.bs_rep in BSR. destruct (h_stack_blk h); [| exfalso; apply SB1; reflexivity]. destruct BSR as (_ & junk & SC). exists junk. exact SC. }
  destruct SCX as [junk SC]. rewrite USED, HST in SC.
  unfold hand_cells, hand_head_cells, alloc_cells in HC. cbn [yc_callbacks yc_malloc_w yc_realloc_w yc_free_w ayc app] in HC. unfold wz in HC. rewrite EH in HC.
  unfold phead, pstate.
  arz_seg KIPY AHK.
  pose proof (mk_ppol BLKY LAYY BSHY E s LK h mh h cx m mo _ _ PA OK AHK SAME SB1 SZ LINK) as PP. openPP PP.
  (* [comment removed for export] *)
  eapply evtA_cut.
  { rewrite USED. eapply (head_dispatch _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (mh_addr (p_mh E)) (p_SQ E) (p_ff E) (mh_stack mh) st rest (h_stack_size h) junk);
      [ exact MI | exact HC | rewrite ?EH; exact FR | exact SC | clear -CEILB STI HST; destruct STI as (_ & HU' & _); unfold h_used in HU'; rewrite HST in HU'; unfold zlength in *; cbn [length] in HU'; lia
      | exact SZ8 | clear -CEILB BC2; lia
      | clear -CEILB pa_H0; lia | clear -CEILB pa_H0; lia | clear -CEILB pa_H0; lia
      | exact (pb_SBA PB) | clear -CEILB pb_SB0; lia | clear -CEILB pb_SB0; lia
      | rewrite EH in SHH; exact SHH | reflexivity | exact SHS | reflexivity
      | exact pp_img0 | exact pp_Hs0 | exact pp_H0 | exact pp_SB0 | exact pp_SBs0
      | intros a k Ha Hk; apply pp_stk0; clear -CEILB Ha Hk pa_SQ0 pa_lo0; lia ]. }
  cbv beta. intros ms1 ->.
  (* [comment removed for export] *)
  eapply evtA_cut.
  { eapply (lex_site_seg _ (state_targetA st)); [ apply lex_site_state; exact LS | exact FR | exact HC | exact I
      | clear -CEILB pa_H0; lia | clear -CEILB pa_H0; lia | clear -CEILB pa_H0; lia | clear -CEILB pa_SQ0 pa_lo0 pa_ceil0; lia | clear -CEILB pa_SQ0 pa_sp0; lia
      | rewrite EH in SHH; exact SHH | reflexivity
      | intros a k Ha Hk; apply pp_stk0; clear -CEILB Ha Hk pa_SQ0 pa_lo0; lia | exact pp_Hs0 | exact pp_H0 ]. }
  cbv beta. intros ms2 ->.
  apply evtA_done. intros mo1 Hag1 HLI1 Hh1. destruct (BACK mo1 Hag1 HLI1) as [AHK1 R01].
  eapply (lex_call E (state_targetA st) m mo1 s LK h mh cx obw olw cr);
    [ exact PA | exact OK | | exact HCR | exact FRM | exact HINV | apply lex_site_state; exact LS | exact NB0 | ].
  - (* [comment removed for export] *)
    unfold pmem. split; [apply AYST_split; split; [exact AHK1| exact YS]|].
    split; [exact HR|]. split; [exact SAME|]. split; [exact CXR|]. split; [exact TXT|]. split; [exists k0, k224; exact FR|]. split; [exact SV|].
    split; [exact FF|]. split; [exact OCX|]. split; [exact STK|]. split; [exact GAP|]. split; [exact MI|]. split; [exact PRES|]. split; [exact UA|]. split; [split; [exact CRED| exact CR0]|].
    split; [split; [exact SO1| eapply RRT; [exact R1| exact R01]]|]. split; [exact SB1| lk_nil].
  - intros. eapply CONT; eassumption.
Qed.

End W.
End RC__1.
