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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim YajlBase YajlLeaf YajlBuf YajlLex YajlDecode YajlParser YajlFactsBuf YajlFactsLex YajlFactsParse YajlFactsLoop.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RY_lib.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA AImages LazyModel NodesA Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import A_iface AYajlRep AYajl_iface AY_rz AY_hand AY_acct_needs AY_parse_kit AY_parse_kitD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac aceil := first [pose proof alloc_ceiling_range as CEILB | idtac].
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma dzbytes_firstn : forall k l, zbytes (firstn k l) = firstn k (zbytes l).
Proof. aceil. intros k l. unfold zbytes. rewrite firstn_map. reflexivity. Qed.
Lemma dzbytes_skipn : forall k l, zbytes (skipn k l) = skipn k (zbytes l).
Proof. aceil. intros k l. unfold zbytes. rewrite skipn_map. reflexivity. Qed.
Lemma dbytes_at_sub : forall m A bs i k,
  bytes_at asegs m A bs -> (i <= length bs)%nat -> bytes_at asegs m (A + Z.of_nat i) (firstn k (skipn i bs)).
Proof. aceil.
  intros m A bs i k HB Hi.
  rewrite <- (firstn_skipn i bs) in HB. apply bytes_at_app in HB. destruct HB as [_ HB].
  rewrite length_firstn, Nat.min_l in HB by lia.
  rewrite <- (firstn_skipn k (skipn i bs)) in HB. apply bytes_at_app in HB. destruct HB as [HB _]. exact HB.
Qed.
Lemma dbytes_at_zslice : forall m A str i k,
  bytes_at asegs m A (zbytes str) -> 0 <= i <= zlength str -> bytes_at asegs m (A + i) (zbytes (zslice str i k)).
Proof. aceil.
  intros m A str i k HB Hi. unfold zslice. rewrite dzbytes_firstn, dzbytes_skipn.
  replace i with (Z.of_nat (Z.to_nat i)) at 1 by lia. apply dbytes_at_sub; [exact HB|]. rewrite zbytes_length. unfold zlength in Hi. lia.
Qed.
Lemma dForall_zslice : forall (P : Z -> Prop) str i k, Forall P str -> Forall P (zslice str i k).
Proof. aceil.
  intros P str i k HF. unfold zslice.
  rewrite <- (firstn_skipn (Z.to_nat i) str) in HF. apply Forall_app in HF. destruct HF as [_ HF].
  rewrite <- (firstn_skipn (Z.to_nat k) (skipn (Z.to_nat i) str)) in HF. apply Forall_app in HF. tauto.
Qed.

(* [comment removed for export] *)
Lemma dnbig_app : forall l1 l2, nbig (l1 ++ l2) = nbig l1 + nbig l2.
Proof. aceil. intros. unfold nbig. rewrite List.filter_app, length_app. lia. Qed.
Lemma dnbig_cons_small : forall b l, ab_size b <= 64512 -> nbig (b :: l) = nbig l.
Proof. aceil. intros b l Hb. unfold nbig. cbn [List.filter]. destruct (64512 <? ab_size b) eqn:E0; [apply Z.ltb_lt in E0; lia| reflexivity]. Qed.

Definition dec_site (pc : Z) : Prop := pc = 0x87bac \/ pc = 0x88210.

Section W.
Variable Y : ay_params.
Hypothesis KIPY : AHK_y_kip_stmt Y.
Hypothesis BLKY : AHK_y_blocks_stmt Y.
Hypothesis BSHY : AHK_y_block_shadow_stmt Y.
Hypothesis LAYY : AHK_y_layout_stmt Y.
Hypothesis PERMY : AHK_y_perm_stmt Y.
Hypothesis RRT : ayR_trans_stmt Y.
Hypothesis YSD : aystring_decode_stmt Y.
Variable URA : list Z.
Hypothesis USTEP : forall m SP ra s0 ra' s0', In (bv_unsigned ra) URA -> SP + 16 <= bv_unsigned s0 < 2^47 ->
    rw_cells asegs m (bv_unsigned s0 - 16) [C8 s0'; C8 ra'] -> y_uanchor Y m (bv_unsigned s0) ra' s0' -> y_uanchor Y m SP ra s0.
Hypothesis URA_dec : forall pc, dec_site pc -> In pc URA.
Hypothesis UFRAME : forall m m' SP ra s0, (forall a, SP <= a < 2^47 -> m' (wa a) = m (wa a)) -> y_uanchor Y m SP ra s0 -> y_uanchor Y m' SP ra s0.
Hypothesis NONNEG : yacct_nonneg_stmt Y.
Variable phr : Z -> Z -> Z -> Z -> Z.
Hypothesis YSPLIT : yphi_hand_split_stmt Y phr.

Lemma dec_call : forall (E : apE Y) pc m mo s LK h0 cx0 h mh cx obw olw cr (F : bvmap 5 word) (fc : bv 32) (i n : Z)
    (t0 t1 t2 a3 a4 a5 a6 a7 s2v s4v s5v t3 t4 t5 t6 : word),
  penvA E -> pok E h0 cx0 -> pmem E m mo s LK h mh cx obw olw cr -> y_phi_hand Y h (pLEN E) <= cr -> frm0 fc -> dec_site pc ->
  LK = [] -> buf_inv (h_decbuf h) -> yb_state (h_decbuf h) = BS_ok -> yb_used (h_decbuf h) = 0 -> 0 < h_stack_size h ->
  0 <= i -> 0 <= n -> i + n < pLEN E -> sbody_ix (p_txt E) i (i + n) ->
  (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) m' mo' s' db' mbd' LK',
     yleaf (ystring_decode (h_decbuf h) (zslice (p_txt E) i n) n) db' -> mb_same (mh_decbuf mh) mbd' -> frm0 fc' ->
     (LK' <> [] -> yb_state db' <> BS_ok /\ length LK' = 1%nat) ->
     pmem E m' mo' s' (LK' ++ LK) (h_set_decbuf h db') (mh_set_decbuf mh mbd') cx obw olw (cr - y_phi_buf Y (h_decbuf h) + y_phi_buf Y db') ->
     y_phi_hand Y (h_set_decbuf h db') (pLEN E) <= cr - y_phi_buf Y (h_decbuf h) + y_phi_buf Y db' ->
     realizes_cfg acfg asegs (mkCfg (pstate E pc F' fc' m' (wz pc) t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2v s4v s5v t3' t4' t5' t6') mo') (p_K E)) ->
  realizes_cfg acfg asegs (mkCfg (pstate E AY_STRING_DECODE F fc m (wz pc) t0 t1 t2 (wz (mb_addr (mh_decbuf mh))) (wz (p_T E + i)) (wz n) a3 a4 a5 a6 a7 s2v s4v s5v t3 t4 t5 t6) mo) (p_K E).
Proof. aceil.
  intros until t6. intros PA OK PM HCR FRM SITE LK0 DBI DBOK DBU SZ I0 N0 INL SBX CONT.
  pose proof PM as (AY & HR & SAME & CXR & TXT & (k0 & k224 & FR) & SV & FF & OCX & STK & GAP & MI & PRES & UA & (CRED & CR0) & (SO1 & R1) & SB1 & LKZ).
  pose proof OK as (K0 & LP & U0 & (SB0 & SZM) & TB & OTB & (f & FIN & FCX & FCL) & LC0 & NBIG & RR0 & TP & FFP & FFR0).
  apply AYST_split in AY. destruct AY as [AHK YS].
  pose proof HR as (HS & LXR & DBR & BSR). pose proof HS as ((pew & pad & HC & PW) & BC1 & BC2 & BC3 & BC4).
  pose proof (mk_pblk BLKY LAYY BSHY E s LK h mh h0 cx0 m mo PA OK AHK SAME SB1 SZ) as PB.
  pose proof (mk_pdec BLKY E s LK h mh h0 cx0 m mo PA OK AHK SAME SB1) as PD.
  destruct (BLKY _ _ _ _ _ AHK) as (RNG & _ & _).
  openPA PA. openPB PB. destruct PD as [pd_LDB0 pd_LBDB0 pd_LDDB0 pd_LDD0 pd_LBDD0 pd_LDDD0 pd_DBT0 pd_DDT0 pd_DBR0 pd_DDR0 pd_DBDD0].
  pose proof SAME as (EH & EL & ELB & EDB & ECX).
  unfold pstate.
  (* [comment removed for export] *)
  set (REST' := (mkABlock (mh_addr mh) SIZEOF_HANDLE :: mkABlock (mh_lexer mh) SIZEOF_LEXER :: abl (buf_blocks (mh_lexbuf mh) (lx_buf (h_lexer h))))
                 ++ abl (bs_blocks (mh_sid mh) (mh_stack mh) h) ++ LK ++ p_REST E).
  assert (PERM0 : Permutation (abl (yblocks mh h) ++ LK ++ p_REST E) (abl (buf_blocks (mh_decbuf mh) (h_decbuf h)) ++ REST')).
  { unfold yblocks, lexer_blocks, REST', abl. cbn [map app MallocBlocks.blk_addr MallocBlocks.blk_size fst snd]. rewrite !map_app.
    cbn [map app MallocBlocks.blk_addr MallocBlocks.blk_size fst snd]. rewrite <- !app_assoc. cbn [app].
    set (Ll := map _ (buf_blocks (mh_lexbuf mh) (lx_buf (h_lexer h)))). set (Dd := map _ (buf_blocks (mh_decbuf mh) (h_decbuf h))).
    set (Ss := map _ (bs_blocks (mh_sid mh) (mh_stack mh) h)).
    change (Permutation (([mkABlock (mh_addr mh) 104; mkABlock (mh_lexer mh) 48] ++ Ll) ++ Dd ++ (Ss ++ LK ++ p_REST E))
                        (Dd ++ ([mkABlock (mh_addr mh) 104; mkABlock (mh_lexer mh) 48] ++ Ll) ++ (Ss ++ LK ++ p_REST E))).
    apply Permutation_app_swap_app. }
  assert (AHK' : y_AHK Y s (abl (buf_blocks (mh_decbuf mh) (h_decbuf h)) ++ REST') (pLF E) m mo) by (eapply PERMY; [exact AHK| exact PERM0| apply Permutation_refl]).
  assert (INR' : forall b, In b (p_REST E) -> In b REST') by (intros b Hb; unfold REST'; apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; exact Hb).
  assert (INRO : forall b, In b (p_REST E) -> In b (abl (yblocks mh h) ++ LK ++ p_REST E)) by (intros b Hb; apply in_or_app; right; apply in_or_app; right; exact Hb).
  assert (IN : forall b, In b (abl (yblocks mh h)) -> In b (abl (yblocks mh h) ++ LK ++ p_REST E)) by (intros b Hb; apply in_or_app; left; exact Hb).
  assert (IHR' : In (mkABlock (mh_addr mh) SIZEOF_HANDLE) REST') by (unfold REST'; left; reflexivity).
  (* [comment removed for export] *)
  pose proof (proj1 (BSHY _ _ _ _ _ _ AHK (IN _ (yb_in_hand mh h)) ltac:(cbn; unfold SIZEOF_HANDLE; lia))) as OSH_H. cbn [ab_addr ab_size] in OSH_H.
  pose proof (proj1 (BSHY _ _ _ _ _ _ AHK (IN _ (yb_in_decbuf mh h)) ltac:(cbn; unfold SIZEOF_BUF; lia))) as OSH_DB. cbn [ab_addr ab_size] in OSH_DB.
  assert (ODBHI : oshw_hi 0 (2^47) <= mb_addr (mh_decbuf mh)) by (revert pb_DB0; clear; unfold oshw_hi, A_SB; cbn; intros; lia).
  pose proof DBR as ((DBC & DBZ & DBL & DBUR) & DBD & DBF).
  assert (OSH_DD : yb_data (h_decbuf h) <> None -> oshadow m (mb_data (mh_decbuf mh)) (yb_len (h_decbuf h)) /\ amem (mb_data (mh_decbuf mh)) (yb_len (h_decbuf h))).
  { intros HD. destruct (yb_data (h_decbuf h)) as [d|] eqn:Hd; [| exfalso; apply HD; reflexivity].
    unfold RYajlRep.buf_data in DBD. rewrite Hd in DBD. destruct DBD as (UL & _).
    pose proof (BSHY _ _ _ _ _ _ AHK (IN _ (yb_in_decdata mh h ltac:(rewrite Hd; discriminate))) ltac:(cbn; clear -CEILB UL; lia)) as X. cbn [ab_addr ab_size] in X. exact X. }
  pose proof (sub_chunk m _ [C8 (p_fs0 E); C8 (p_s11 E); C8 (p_s10 E); C8 (p_s9 E); C8 (p_s8 E); C8 (p_s7 E); C8 (p_s6 E); C8 (p_s5 E); C8 (p_s4 E); C8 (p_s3 E); C8 (p_s2 E); C8 (p_s1 E)]
               [C8 (p_s0 E); C8 (p_ra E)] [] ltac:(rewrite app_nil_r; exact SV)) as SV16.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in SV16. replace (bv_unsigned (p_sp E) - 112 + 96) with (bv_unsigned (p_sp E) - 16) in SV16 by lia.
  pose proof (bv_unsigned_in_range 64 (p_sp E)) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  (* [comment removed for export] *)
  pose proof (sub_chunk m (mh_addr mh) (hand_head_cells ayc h mh pew pad) (alloc_cells ayc) [] ltac:(rewrite app_nil_r; exact HC)) as HAF.
  rewrite hand_head_cells_size in HAF.
  (* [comment removed for export] *)
  assert (NZL : 0 < zlength (p_txt E)) by (clear -CEILB INL I0 N0; lia).
  destruct TB as [(bt & Hbt & B1 & B2)| Z0]; [| exfalso; clear -CEILB Z0 NZL; lia].
  pose proof (RNG bt (INRO _ Hbt)) as RT. unfold ablock_range, ACONSTS in RT. cbn [c_img_hi] in RT. aceil.
  destruct (BSHY _ _ _ _ _ bt AHK' ltac:(apply in_or_app; right; apply INR'; exact Hbt) ltac:(clear -CEILB B1 B2 NZL; lia)) as [OSB OHI].
  pose proof TXT as (TXB & TXF & TX0 & TX62).
  assert (SRCL : zlength (zslice (p_txt E) i n) = n) by (apply zslice_length; clear -CEILB I0 N0 INL; lia).
  eapply (YSD (pLF E) REST' (mh_decbuf mh) (h_decbuf h) (mh_addr mh + 72) (p_T E + i) (zslice (p_txt E) i n) n (ab_addr bt) (ab_size bt) (p_lo E)
              (p_RR E + (cr - y_phi_buf Y (h_decbuf h))) (p_K E));
    [ exact K0
    | apply AYST_split; split; [exact AHK'| exact YS]
    | exact DBR | exact DBI | exact DBU
    | exact HAF
    | (* [comment removed for export] *) exists (mkABlock (mh_addr mh) SIZEOF_HANDLE); split; [exact IHR'|]; cbn [ab_addr ab_size]; unfold SIZEOF_HANDLE;
      split; [clear; lia|]; split; [clear; cbn; lia|]; split; [clear -CEILB pa_H0 EH; Z.div_mod_to_equations; lia|]; split; [exact OSH_H| revert pa_H0 EH; clear; unfold oshw_hi, A_SB; cbn; intros; lia]
    | unfold SIZEOF_BUF; exact OSH_DB | exact OSH_DD
    | apply dbytes_at_zslice; [exact TXB| clear -CEILB I0 N0 INL; lia]
    | apply dForall_zslice; exact TXF
    | symmetry; exact SRCL
    | clear -CEILB N0 I0 INL pa_len0; lia
    | clear -CEILB TX0 I0; lia
    | clear -CEILB INL pa_T0 I0; lia
    | exact (sbody_ix_slice _ _ _ I0 SBX)
    | left; exists bt; split; [apply INR'; exact Hbt| clear -CEILB B1 B2 I0 INL; lia]
    | right; split; [exact OSB|]; split; [clear -CEILB B1 I0; lia|]; split; [clear -CEILB B2 INL; lia|]; split; [exact OHI|]; split; [clear -CEILB RT; aceil; lia|];
      exists bt; split; [apply INR'; exact Hbt| clear; lia]
    | exact LC0
    | unfold ayframe_pre, AY_DECODE_STACK, AY_BUF_APPEND_STACK, AMALLOC_STACK; aceil;
      rewrite unsigned_lit by (clear -CEILB pa_SQ0 pa_ceil0 pa_lo0 SPR; lia);
      split; [exact STK|]; split; [clear -CEILB pa_ceil0; lia|]; split; [clear -CEILB pa_SQ0 pa_lo0; lia|]; split; [clear -CEILB pa_SQ0 pa_sp0; lia|];
      split; [clear -CEILB pa_SQ0; Z.div_mod_to_equations; lia|]; split; [exact MI|]; split; [exact TP| exact FRM]
    | reflexivity | reflexivity | reflexivity
    | (* [comment removed for export] *) destruct YSPLIT as (EQ & NN & _); rewrite (EQ h (pLEN E)) in HCR; destruct NONNEG as (_ & NB & _ & _);
      pose proof (NB (lx_buf (h_lexer h))) as Q1; pose proof (NN (h_bytesConsumed h) (h_used h) (h_stack_size h) (pLEN E)) as Q2; clear -CEILB CRED HCR Q1 Q2; lia
    | destruct YSPLIT as (EQ & NN & _); rewrite (EQ h (pLEN E)) in HCR; destruct NONNEG as (_ & NB & _ & _);
      pose proof (NB (lx_buf (h_lexer h))) as Q1; pose proof (NN (h_bytesConsumed h) (h_used h) (h_stack_size h) (pLEN E)) as Q2; clear -CEILB RR0 HCR Q1 Q2; lia
    | (* [comment removed for export] *)
      subst LK; unfold REST'; cbn [app];
      rewrite (dnbig_cons_small (mkABlock (mh_addr mh) SIZEOF_HANDLE)) by (cbn [ab_size]; unfold SIZEOF_HANDLE; clear; lia);
      rewrite (dnbig_cons_small (mkABlock (mh_lexer mh) SIZEOF_LEXER)) by (cbn [ab_size]; unfold SIZEOF_LEXER; clear; lia);
      rewrite !dnbig_app;
      assert (A1 : nbig (abl (buf_blocks (mh_lexbuf mh) (lx_buf (h_lexer h)))) <= 1)
        by (unfold nbig, buf_blocks, abl, SIZEOF_BUF; destruct (yb_data (lx_buf (h_lexer h)));
            cbn [map List.filter length ab_size MallocBlocks.blk_addr MallocBlocks.blk_size fst snd Z.ltb Z.compare Pos.compare Pos.compare_cont];
            [destruct (64512 <? yb_len (lx_buf (h_lexer h))); cbn [length]; lia| lia]);
      assert (A2 : nbig (abl (bs_blocks (mh_sid mh) (mh_stack mh) h)) <= 1)
        by (unfold nbig, bs_blocks, abl; destruct (h_stack_blk h);
            cbn [map List.filter length ab_size MallocBlocks.blk_addr MallocBlocks.blk_size fst snd];
            [destruct (64512 <? h_stack_size h); cbn [length]; lia| lia]);
      unfold AY_NBIG_REST in NBIG |- *; clear -CEILB A1 A2 NBIG; lia
    | rewrite unsigned_lit by (clear -CEILB pa_SQ0 pa_ceil0 pa_lo0 SPR; lia);
      eapply USTEP; [unfold wz; rewrite unsigned_lit by (clear -CEILB SITE; unfold dec_site in SITE; lia); apply URA_dec; exact SITE
                    | clear -CEILB pa_SQ0 pa_sp0; lia | exact SV16 | exact UA]
    | ].
  cbv beta. intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F2 fc2 m2 mo2 s2 db' mbd' LK' POST.
  destruct POST as (SO2 & R2 & CRED2 & (MI2 & ST2 & FRM2 & _ & PRES2) & HAF2 & YL & DBR2 & MBS & OSHDB2 & OSHDD2 & TXB2 & LKZ2 & AY2 & LKT).
  unfold wz. rewrite (ret_pc_even pc) by (clear -CEILB SITE; unfold dec_site in SITE; lia).
  rewrite unsigned_lit in PRES2, ST2 by (clear -CEILB pa_SQ0 pa_ceil0 pa_lo0 SPR; lia).
  pose proof MBS as MBA. unfold mb_same in MBA.
  assert (PHI0 : y_phi_buf Y (h_decbuf h) <= y_phi_hand Y h (pLEN E)).
  { destruct YSPLIT as (EQ & NN & _). rewrite (EQ h (pLEN E)). destruct NONNEG as (_ & NB & _ & _).
    pose proof (NB (lx_buf (h_lexer h))) as Q1. pose proof (NN (h_bytesConsumed h) (h_used h) (h_stack_size h) (pLEN E)) as Q2. clear -CEILB Q1 Q2. lia. }
  unfold pstate, wz in CONT. eapply CONT; [exact YL| exact MBS| exact FRM2| exact LKT| |].
  2:{ destruct YSPLIT as (EQ & _). rewrite (EQ (h_set_decbuf h db') (pLEN E)). rewrite (EQ h (pLEN E)) in HCR.
      cbn [h_set_decbuf h_lexer h_decbuf h_bytesConsumed h_stack_size]. unfold h_used in HCR |- *. cbn [h_stack h_set_decbuf]. clear -CEILB HCR. lia. }
  (* [comment removed for export] *)
  pose proof (ay_pres_agree _ _ _ _ _ _ PRES2) as AG.
  apply AYST_split in AY2. destruct AY2 as [AHK2 YS2].
  destruct (LAYY _ _ _ _ _ AHK) as (LAYF & LAYFB & LAYFF).
  (* [comment removed for export] *)
  assert (RCL : forall b a, In b REST' -> ab_addr b <= a < ab_addr b + ab_size b ->
            ay_client_addr REST' (pLF E) (p_SQ E) a /\ ~ yin_ivs [] a).
  { intros b a Hb Ha. split; [right; left; exists b; split; [exact Hb| exact Ha]| cbn; clear; tauto]. }
  assert (IHL : In (mkABlock (mh_lexer mh) SIZEOF_LEXER) REST') by (unfold REST'; right; left; reflexivity).
  assert (ILB : In (mkABlock (mb_addr (mh_lexbuf mh)) SIZEOF_BUF) REST') by (unfold REST', abl, buf_blocks; cbn [map app MallocBlocks.blk_addr MallocBlocks.blk_size fst snd]; right; right; left; reflexivity).
  assert (ILD : forall d, yb_data (lx_buf (h_lexer h)) = Some d -> In (mkABlock (mb_data (mh_lexbuf mh)) (yb_len (lx_buf (h_lexer h)))) REST').
  { intros d Hd. unfold REST', abl, buf_blocks. rewrite Hd. cbn [map app MallocBlocks.blk_addr MallocBlocks.blk_size fst snd]. right; right; right; left; reflexivity. }
  assert (ISB : In (mkABlock (mh_stack mh) (h_stack_size h)) REST').
  { unfold REST', abl, bs_blocks. destruct (h_stack_blk h); [| exfalso; apply SB1; reflexivity]. apply in_or_app; right. apply in_or_app; left. left; reflexivity. }
  (* [comment removed for export] *)
  assert (HICL : forall a, p_SQ E <= a -> ay_client_addr REST' (pLF E) (p_SQ E) a /\ ~ yin_ivs [] a).
  { intros a Ha. split; [left; exact Ha| cbn; clear; tauto]. }
  (* [comment removed for export] *)
  assert (CXCL : forall a, (mh_ctx (p_mh E) <= a < mh_ctx (p_mh E) + 8 \/ A_SB + mh_ctx (p_mh E) / 8 <= a < A_SB + mh_ctx (p_mh E) / 8 + 1) ->
            ay_client_addr REST' (pLF E) (p_SQ E) a /\ ~ yin_ivs [] a).
  { intros a Ha. split; [| cbn; clear; tauto].
    right; right; left. exists f. split; [right; exact FIN|]. rewrite FCL. unfold ff_bytes. change (Z.shiftl 64 1) with 128. change (Z.shiftl 8 1) with 16.
    clear -CEILB Ha FCX pa_CX0. unfold A_SB in *. Z.div_mod_to_equations. lia. }
  (* [comment removed for export] *)
  assert (FFCL : forall a, ((p_ff E <= a < p_ff E + 128) \/ (p_ff E / 8 + 2147450880 <= a < p_ff E / 8 + 2147450880 + 16)) ->
            ay_client_addr REST' (pLF E) (p_SQ E) a /\ ~ yin_ivs [] a).
  { intros a Ha. split; [| cbn; clear; tauto].
    right; right; left. exists (1, p_ff E). split; [left; reflexivity|]. cbn [fst snd]. unfold ff_bytes, A_SB. change (Z.shiftl 64 1) with 128. change (Z.shiftl 8 1) with 16.
    clear -CEILB Ha pa_ff0. lia. }
  split.
  { apply AYST_split. split; [| exact YS2]. eapply PERMY; [exact AHK2| | apply Permutation_refl].
    unfold yblocks, lexer_blocks, abl, REST'. cbn [mh_set_decbuf mh_id mh_addr mh_lid mh_lexer mh_lexbuf mh_decbuf mh_sid mh_stack h_set_decbuf h_lexer h_decbuf map app MallocBlocks.blk_addr MallocBlocks.blk_size fst snd].
    rewrite !map_app. cbn [map app MallocBlocks.blk_addr MallocBlocks.blk_size fst snd].
    replace (bs_blocks (mh_sid mh) (mh_stack mh) (h_set_decbuf h db')) with (bs_blocks (mh_sid mh) (mh_stack mh) h) by reflexivity.
    set (Dd := map _ (buf_blocks mbd' db')). set (Ll := map _ (buf_blocks (mh_lexbuf mh) (lx_buf (h_lexer h)))). set (Ss := map _ (bs_blocks (mh_sid mh) (mh_stack mh) h)).
    set (A2b := mkABlock (mh_addr mh) 104 :: mkABlock (mh_lexer mh) 48 :: Ll).
    rewrite <- !app_assoc.
    change (Permutation (Dd ++ LK' ++ A2b ++ Ss ++ LK ++ p_REST E) (A2b ++ Dd ++ Ss ++ LK' ++ LK ++ p_REST E)).
    transitivity (Dd ++ A2b ++ Ss ++ LK' ++ LK ++ p_REST E).
    - apply Permutation_app_head.
      replace (LK' ++ A2b ++ Ss ++ LK ++ p_REST E) with (LK' ++ (A2b ++ Ss) ++ (LK ++ p_REST E)) by (rewrite <- !app_assoc; reflexivity).
      replace (A2b ++ Ss ++ LK' ++ LK ++ p_REST E) with ((A2b ++ Ss) ++ LK' ++ (LK ++ p_REST E)) by (rewrite <- !app_assoc; reflexivity).
      apply Permutation_app_swap_app.
    - replace (Dd ++ A2b ++ Ss ++ LK' ++ LK ++ p_REST E) with (Dd ++ A2b ++ (Ss ++ LK' ++ LK ++ p_REST E)) by reflexivity.
      replace (A2b ++ Dd ++ Ss ++ LK' ++ LK ++ p_REST E) with (A2b ++ Dd ++ (Ss ++ LK' ++ LK ++ p_REST E)) by reflexivity.
      apply Permutation_app_swap_app. }
  split.
  { split; [| split; [| split]].
    - (* [comment removed for export] *)
      split; [| cbn [h_set_decbuf h_bytesConsumed h_stack_size h_stack_blk h_parseError mh_set_decbuf mh_stack]; split; [exact BC1| split; [exact BC2| split; [exact BC3| exact BC4]]]].
      exists pew, pad. split; [| exact PW].
      replace (hand_cells ayc (h_set_decbuf h db') (mh_set_decbuf mh mbd') pew pad) with (hand_cells ayc h mh pew pad)
        by (unfold hand_cells, hand_head_cells; cbn [h_set_decbuf h_bytesConsumed h_stack_size h_stack mh_set_decbuf mh_ctx mh_lexer mh_decbuf mh_stack mh_addr]; rewrite MBA; reflexivity).
      cbn [mh_addr mh_set_decbuf].
      eapply rw_cells_agree; [exact AG| exact HC|]. rewrite hand_cells_size. intros a Ha.
      eapply RCL; [exact IHR'| cbn [ab_addr ab_size]; unfold SIZEOF_HANDLE; clear -CEILB Ha; lia].
    - cbn [h_set_decbuf h_lexer mh_set_decbuf mh_lexer mh_lexbuf mh_addr]. eapply lexer_rep_agree; [exact AG| exact LXR| | |].
      + intros a Ha. eapply RCL; [exact IHL| cbn [ab_addr ab_size]; clear -CEILB Ha; lia].
      + intros a Ha. eapply RCL; [exact ILB| cbn [ab_addr ab_size]; clear -CEILB Ha; lia].
      + intros HD a Ha. destruct (yb_data (lx_buf (h_lexer h))) as [d|] eqn:Hd; [| exfalso; apply HD; reflexivity].
        eapply RCL; [exact (ILD d eq_refl)| cbn [ab_addr ab_size]; clear -CEILB Ha; lia].
    - cbn [h_set_decbuf h_decbuf mh_set_decbuf mh_decbuf mh_addr]. exact DBR2.
    - cbn [mh_set_decbuf mh_stack].
      eapply bs_rep_agree; [exact AG| | | unfold h_used; cbn [h_stack h_stack_size h_set_decbuf]; unfold h_used in BC3; clear -CEILB BC3; lia].
      + unfold RYajlRep.bs_rep in BSR |- *. cbn [h_stack_blk h_set_decbuf]. destruct (h_stack_blk h); [| exfalso; apply SB1; reflexivity].
        cbn [h_stack h_stack_size h_set_decbuf]. replace (h_used (h_set_decbuf h db')) with (h_used h) by reflexivity. exact BSR.
      + cbn [h_stack_size h_set_decbuf]. intros a Ha. eapply RCL; [exact ISB| cbn [ab_addr ab_size]; clear -CEILB Ha; lia]. }
  split.
  { unfold mh_same. cbn [mh_set_decbuf mh_id mh_addr mh_lid mh_lexer mh_lexbuf mh_decbuf mh_sid mh_stack mh_ctx]. rewrite MBA. exact SAME. }
  split. { eapply ctx_rep_agree; [exact AG| exact CXR|]. intros a Ha. apply CXCL. left. exact Ha. }
  split.
  { eapply text_at_agree; [exact AG| exact TXT|]. intros a Ha. eapply (RCL bt); [apply INR'; exact Hbt| clear -CEILB Ha B1 B2; lia]. }
  split.
  { exists k0, k224. eapply rw_cells_agree; [exact AG| exact FR|]. intros a Ha. apply HICL. clear -CEILB Ha. lia. }
  split.
  { eapply rw_cells_agree; [exact AG| exact SV|]. intros a Ha. apply HICL. clear -CEILB Ha pa_SQ0. lia. }
  split.
  { destruct pa_j0 as (J1 & J2 & J3). pose proof FF as (FFA & FOB & FJ2 & FOL & FJ3 & FSH).
    split; [eapply rw_cells_agree; [exact AG| exact FFA| intros a Ha; apply FFCL; unfold pffA in Ha; cbn [cells_size csize Nat.add] in Ha; clear -CEILB Ha; lia]|].
    split; [eapply rw_cells_agree; [exact AG| exact FOB| intros a Ha; apply FFCL; cbn [cells_size csize Nat.add] in Ha; clear -CEILB Ha; lia]|].
    split; [eapply rw_cells_agree; [exact AG| exact FJ2| intros a Ha; apply FFCL; cbn [cells_size csize Nat.add] in Ha; clear -CEILB Ha; lia]|].
    split; [eapply rw_cells_agree; [exact AG| exact FOL| intros a Ha; apply FFCL; cbn [cells_size csize Nat.add] in Ha; clear -CEILB Ha; lia]|].
    split; [eapply rw_cells_agree; [exact AG| exact FJ3| intros a Ha; apply FFCL; unfold pffZ in Ha; cbn [cells_size csize Nat.add] in Ha; clear -CEILB Ha; lia]|].
    eapply rw_cells_agree; [exact AG| exact FSH| intros a Ha; apply FFCL; unfold pffsh in Ha; cbn [cells_size csize Nat.add] in Ha; clear -CEILB Ha; lia]. }
  split. { eapply oshadow_agree; [exact AG| exact OCX|]. intros a Ha. apply CXCL. right. revert Ha. unfold oshw_lo, oshw_hi, A_SB, amem. clear. intros Ha. Z.div_mod_to_equations. lia. }
  split; [exact ST2|].
  split. { eapply stk_agree; [exact AG| exact GAP|]. intros a Ha. apply HICL; clear -CEILB Ha pa_SQ0 pa_ff0 pa_ceil0 pa_lo0; lia. }
  split; [exact MI2|].
  split.
  { eapply ay_pres_trans; [exact PRES|]. intros a Ha Hc Hx. apply PRES2; [exact Ha| | cbn; clear; tauto].
    destruct Hc as [Hc|[Hc|[Hc|Hc]]].
    + left. clear -CEILB Hc pa_SQ0. lia.
    + right; left. destruct Hc as (b & Hb & Hr). exists b. split; [apply INR'; exact Hb| exact Hr].
    + right; right; left. destruct Hc as (f' & Hf' & Hr). exists f'. split; [right; exact Hf'| exact Hr].
    + right; right; right. exact Hc. }
  split.
  { eapply UFRAME; [| exact UA]. intros a Ha. apply (proj1 (PRES2 a ltac:(clear -CEILB Ha SPR; lia) ltac:(left; clear -CEILB Ha pa_SQ0; lia) ltac:(cbn; clear; tauto))). }
  split. { destruct NONNEG as (_ & NB & _ & _). pose proof (NB db') as Y0. clear -CEILB Y0 PHI0 CRED2 HCR. split; lia. }
  split. { split; [rewrite SO2; exact SO1| eapply RRT; [exact R1| exact R2]]. }
  cbn [h_set_decbuf h_stack_blk]. split; [exact SB1| lk_nil].   (* [comment removed for export] *)
Qed.
End W.
End RC__1.
