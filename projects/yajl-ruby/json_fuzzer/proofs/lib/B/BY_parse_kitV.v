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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim YajlBase YajlLeaf YajlBuf YajlLex YajlDecode YajlParser YajlFactsBuf YajlFactsLex YajlFactsParse YajlFactsLoop.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RY_lib.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA AImages LazyModel NodesA Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import B_iface BYajlRep BYajl_iface BY_rz BY_hand BY_acct_needs BY_parse_kit BY_parse_kitD.
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
Section W.
Variable Y : ay_params.
Hypothesis BLKY : AHK_y_blocks_stmt Y.
Hypothesis LAYY : AHK_y_layout_stmt Y.
Hypothesis BSHY : AHK_y_block_shadow_stmt Y.

Ltac dconj H :=
  lazymatch type of H with
  | _ /\ _ => let A := fresh "SP" in let B := fresh "SP" in destruct H as [A B]; dconj A; dconj B
  | _ => idtac
  end.

(* [comment removed for export] *)
Record plex (E : apE Y) (LK : list ablock) (mh : mhand) (h : yhandle) : Prop := mkPL {
  pl_LT : 0 < pLEN E -> mh_lexer mh + 48 <= p_T E \/ p_T E + pLEN E <= mh_lexer mh;
  pl_LBT : 0 < pLEN E -> mb_addr (mh_lexbuf mh) + 32 <= p_T E \/ p_T E + pLEN E <= mb_addr (mh_lexbuf mh);
  pl_LLB : mh_lexer mh + 48 <= mb_addr (mh_lexbuf mh) \/ mb_addr (mh_lexbuf mh) + 32 <= mh_lexer mh;
  pl_HR : asep_from (mkABlock (mh_addr mh) 104) (LK ++ p_REST E);
  pl_LR : asep_from (mkABlock (mh_lexer mh) 48) (LK ++ p_REST E);
  pl_LBR : asep_from (mkABlock (mb_addr (mh_lexbuf mh)) 32) (LK ++ p_REST E)
}.

Lemma mk_plex : forall E s LK h mh h0 cx0 m mo,
  penvA E -> pok E h0 cx0 -> y_AHK Y s (abl (yblocks mh h) ++ LK ++ p_REST E) (pLF E) m mo ->
  mh_same (p_mh E) mh -> h_stack_blk h <> None -> plex E LK mh h.
Proof. aceil.
  intros E s LK h mh h0 cx0 m mo PA OK AHK SAME HSB.
  destruct SAME as (EH & EL & ELB & EDB & ECX).
  destruct OK as (_ & _ & _ & _ & TB & _).
  assert (SEPT : forall A n, asep_from (mkABlock A n) (LK ++ p_REST E) -> 0 < zlength (p_txt E) -> A + n <= p_T E \/ p_T E + zlength (p_txt E) <= A).
  { intros A n HS Hl. destruct TB as [(bt & Hbt & B1 & B2)| Z0]; [| exfalso; clear -CEILB Hl Z0; lia].
    pose proof (asep_from_In _ _ _ HS ltac:(apply in_or_app; right; exact Hbt)) as X. unfold absep in X. cbn [ab_addr ab_size] in X. clear -CEILB X B1 B2. lia. }
  pose proof (ay_all_sep Y BLKY _ _ _ _ _ AHK) as ASEP.
  unfold yblocks, lexer_blocks, buf_blocks, bs_blocks, abl in ASEP. rewrite !map_cons, !map_app, !map_cons in ASEP.
  destruct (h_stack_blk h) as [sid|]; [| exfalso; apply HSB; reflexivity].
  destruct (yb_data (lx_buf (h_lexer h))) as [dl|] eqn:HDL; destruct (yb_data (h_decbuf h)) as [dd|] eqn:HDD0;
    cbn [map app aall_sep asep_from MallocBlocks.blk_addr MallocBlocks.blk_size fst snd] in ASEP;
    rewrite <- ?app_assoc in ASEP; cbn [app asep_from] in ASEP;
    unfold absep in ASEP; cbn [ab_addr ab_size] in ASEP; unfold SIZEOF_HANDLE, SIZEOF_LEXER, SIZEOF_BUF in ASEP;
    dconj ASEP; split; rewrite ?HDL, ?HDD0;
    first [ assumption | intros Hl; apply SEPT; [assumption| exact Hl] ].
Qed.

(* [comment removed for export] *)
Definition ownL (E : apE Y) (mh : mhand) (iv : Z * Z) : Prop :=
  (p_lo E <= fst iv /\ snd iv <= p_SQ E)
  \/ (mh_addr mh <= fst iv /\ snd iv <= mh_addr mh + 72)
  \/ (mh_lexer mh <= fst iv /\ snd iv <= mh_lexer mh + 48)
  \/ (mb_addr (mh_lexbuf mh) <= fst iv /\ snd iv <= mb_addr (mh_lexbuf mh) + 32).
Lemma ownL_outside : forall E mh W a,
  Forall (ownL E mh) W -> (a < p_lo E \/ p_SQ E <= a) -> (a < mh_addr mh \/ mh_addr mh + 72 <= a) ->
  (a < mh_lexer mh \/ mh_lexer mh + 48 <= a) -> (a < mb_addr (mh_lexbuf mh) \/ mb_addr (mh_lexbuf mh) + 32 <= a) -> outside W a.
Proof. aceil.
  intros E mh W a HF H1 H2 H3 H4. induction HF as [| [lo hi] W HO HF IH]; [exact I|].
  cbn. split; [| exact IH]. unfold ownL in HO. cbn [fst snd] in HO. clear -CEILB HO H1 H2 H3 H4. lia.
Qed.

Hypothesis FRAMEY : AHK_y_frame_stmt Y.
Hypothesis UFRAME : forall m m' SP ra s0, (forall a, SP <= a < 2^47 -> m' (wa a) = m (wa a)) -> y_uanchor Y m SP ra s0 -> y_uanchor Y m' SP ra s0.

(* [comment removed for export] *)
Lemma pmem_updL : forall E m m' mo s LK h mh cx obw olw cr lx' h0 cx0 W,
  penvA E -> pok E h0 cx0 -> pmem E m mo s LK h mh cx obw olw cr -> 0 < h_stack_size h ->
  munch W m m' -> wmono bsegs m m' -> mem_inv bsegs m' ->
  Forall (ownL E mh) W ->
  yb_data (lx_buf lx') = yb_data (lx_buf (h_lexer h)) -> yb_len (lx_buf lx') = yb_len (lx_buf (h_lexer h)) ->
  ahand_struct m' (h_set_lexer h lx') mh -> alexer_rep m' (mh_lexer mh) lx' (mh_lexbuf mh) (mh_addr mh + 72) ->
  stk bsegs m' (p_lo E) (p_SQ E) ->
  pmem E m' mo s LK (h_set_lexer h lx') mh cx obw olw cr.
Proof. aceil.
  intros until W. intros PA OK PM SZ MU WM MI' OWN ED EL HS' LXR' STK'.
  pose proof PM as (AY & HR & SAME & CXR & TXT & FR & SV & FFC & OCX & STK & GAP & MI & PRES & UA & CRED & SOR & SB1 & LKZ).
  apply AYST_split in AY. destruct AY as [AHK YS].
  destruct HR as (HS & LXR & DBR & BSR). pose proof HS as (_ & BC1 & BC2 & BC3 & BC4).
  pose proof (mk_pblk BLKY LAYY BSHY E s LK h mh h0 cx0 m mo PA OK AHK SAME SB1 SZ) as PB.
  pose proof (mk_pdec BLKY E s LK h mh h0 cx0 m mo PA OK AHK SAME SB1) as PD.
  pose proof (mk_plex E s LK h mh h0 cx0 m mo PA OK AHK SAME SB1) as PL.
  destruct (BLKY _ _ _ _ _ AHK) as (RNG & SEP & ND).
  destruct (LAYY _ _ _ _ _ AHK) as (LAYF & LAYFB & LAYFF).
  pose proof OK as (_ & _ & _ & _ & TB & _ & (f & FIN & FCX & FCL) & _).
  pose proof (munch_agree _ _ _ MU WM) as AG.
  assert (YB : yblocks mh (h_set_lexer h lx') = yblocks mh h) by (unfold yblocks, lexer_blocks, buf_blocks, bs_blocks; cbn [h_set_lexer h_lexer h_decbuf h_stack_blk h_stack_size]; rewrite ED, EL; reflexivity).
  openPA PA. openPB PB. destruct PD as [pd_LDB0 pd_LBDB0 pd_LDDB0 pd_LDD0 pd_LBDD0 pd_LDDD0 pd_DBT0 pd_DDT0 pd_DBR0 pd_DDR0 pd_DBDD0]. destruct PL as [pl_LT0 pl_LBT0 pl_LLB0 pl_HR0 pl_LR0 pl_LBR0].
  pose proof SAME as (EH & ELx & ELB & EDB & ECX).
  assert (IN : forall b, In b (abl (yblocks mh h)) -> In b (abl (yblocks mh h) ++ LK ++ p_REST E)) by (intros b Hb; apply in_or_app; left; exact Hb).
  assert (INR : forall b, In b (LK ++ p_REST E) -> In b (abl (yblocks mh h) ++ LK ++ p_REST E)) by (intros b Hb; apply in_or_app; right; exact Hb).
  assert (WOK : Forall (ay_write_ok (abl (yblocks mh h) ++ LK ++ p_REST E) (pLF E)) W).
  { clear -CEILB OWN pa_ceil0 pa_SQ0 pa_lo0 IN. induction OWN as [| [lo hi] W HO HF IH]; constructor; [| exact IH].
    unfold ownL in HO. unfold ay_write_ok. cbn [fst snd] in *. destruct HO as [HO|[HO|[HO|HO]]].
    - left. aceil. lia.
    - right; left. exists (mkABlock (mh_addr mh) SIZEOF_HANDLE). split; [apply IN; apply yb_in_hand| cbn; unfold SIZEOF_HANDLE; lia].
    - right; left. exists (mkABlock (mh_lexer mh) SIZEOF_LEXER). split; [apply IN; apply yb_in_lexer| cbn; unfold SIZEOF_LEXER; lia].
    - right; left. exists (mkABlock (mb_addr (mh_lexbuf mh)) SIZEOF_BUF). split; [apply IN; apply yb_in_lexbuf| cbn; unfold SIZEOF_BUF; lia]. }
  (* [comment removed for export] *)
  assert (OUTsep : forall A n a, (A + n <= mh_addr mh \/ mh_addr mh + 72 <= A) -> (A + n <= mh_lexer mh \/ mh_lexer mh + 48 <= A) ->
            (A + n <= mb_addr (mh_lexbuf mh) \/ mb_addr (mh_lexbuf mh) + 32 <= A) -> A + n <= alloc_ceiling -> A <= a < A + n -> outside W a).
  { intros A n a D1 D2 D3 Rb Ha. eapply ownL_outside; [exact OWN| clear -CEILB Ha Rb pa_ceil0; lia| clear -CEILB Ha D1; lia| clear -CEILB Ha D2; lia| clear -CEILB Ha D3; lia]. }
  assert (OUTlow : forall a, (a < 6303744 \/ 2147446784 <= a < 17594333495296) -> outside W a).   (* [comment removed for export] *)
  { intros a Ha. eapply ownL_outside; [exact OWN| clear -CEILB Ha pa_ceil0; lia| clear -CEILB Ha pa_H0 EH; lia| clear -CEILB Ha pb_L0; lia| clear -CEILB Ha pb_LB0; lia]. }
  assert (OUThi : forall a, p_SQ E <= a -> outside W a).
  { intros a Ha. eapply ownL_outside; [exact OWN| clear -CEILB Ha; lia| clear -CEILB Ha pa_H0 EH pa_lo0 pa_ceil0 pa_SQ0; lia| clear -CEILB Ha pb_L0 pa_lo0 pa_ceil0 pa_SQ0; lia| clear -CEILB Ha pb_LB0 pa_lo0 pa_ceil0 pa_SQ0; lia]. }
  (* [comment removed for export] *)
  assert (OUTR : forall b a, In b (LK ++ p_REST E) -> ab_addr b <= a < ab_addr b + ab_size b -> outside W a).
  { intros b a Hb Ha.
    pose proof (asep_from_In _ _ _ pl_HR0 Hb) as D1. pose proof (asep_from_In _ _ _ pl_LR0 Hb) as D2. pose proof (asep_from_In _ _ _ pl_LBR0 Hb) as D3.
    unfold absep in D1, D2, D3. cbn [ab_addr ab_size] in D1, D2, D3.
    pose proof (RNG _ (INR _ Hb)) as Rb. unfold ablock_range in Rb. aceil.
    eapply (OUTsep (ab_addr b) (ab_size b)); [clear -CEILB D1; lia| clear -CEILB D2; lia| clear -CEILB D3; lia| clear -CEILB Rb; lia| exact Ha]. }
  split.
  { rewrite YB. apply AYST_split. split; [eapply FRAMEY; [exact AHK| exact MU| exact WM| exact WOK]|].
    eapply aystatics_munch; [exact YS| exact MU| exact WM|].
    clear -CEILB OWN pa_ceil0 pa_H0 EH pb_L0 pb_LB0. induction OWN as [| [lo hi] W HO HF IH]; constructor; [| exact IH].
    unfold ownL in HO. cbn [fst snd] in *. right. lia. }
  split.
  { split; [exact HS'|]. split; [cbn [h_set_lexer h_lexer]; exact LXR'|]. split.
    - cbn [h_set_lexer h_decbuf]. eapply buf_rep_agree; [exact AG| exact DBR| |].
      + intros a Ha. unfold SIZEOF_BUF in Ha. eapply (OUTsep (mb_addr (mh_decbuf mh)) 32); [clear -CEILB pb_HDB0 EH; lia| clear -CEILB pd_LDB0; lia| clear -CEILB pd_LBDB0; lia| clear -CEILB pb_DB0; lia| exact Ha].
      + intros HD a Ha. destruct (yb_data (h_decbuf h)) as [d|] eqn:Hd; [| exfalso; apply HD; reflexivity].
        eapply (OUTsep (mb_data (mh_decbuf mh)) (yb_len (h_decbuf h))); [pose proof (pb_HDD0 d eq_refl) as QQ; clear -CEILB QQ EH; lia| pose proof (pd_LDD0 d eq_refl) as QQ; clear -CEILB QQ; lia| pose proof (pd_LBDD0 d eq_refl) as QQ; clear -CEILB QQ; lia| pose proof (pb_DD0 d eq_refl) as QQ; clear -CEILB QQ; lia| exact Ha].
    - eapply bs_rep_agree; [exact AG| | | cbn [h_set_lexer h_stack_size]; unfold h_used; cbn [h_stack h_set_lexer]; unfold h_used in BC3; clear -CEILB BC3; lia].
      + unfold RYajlRep.bs_rep in BSR |- *. cbn [h_stack_blk h_set_lexer h_stack h_stack_size]. exact BSR.
      + cbn [h_set_lexer h_stack_size]. intros a Ha. eapply (OUTsep (mh_stack mh) (h_stack_size h)); [clear -CEILB pb_HSB0 EH; lia| clear -CEILB pb_LSB0; lia| clear -CEILB pb_LBSB0; lia| clear -CEILB pb_SB0; lia| exact Ha]. }
  split; [exact SAME|].
  split. { eapply ctx_rep_agree; [exact AG| exact CXR|]. intros a Ha. eapply (OUTsep (pCX E) 8); [clear -CEILB pa_CXH0 EH; lia| clear -CEILB pb_LCX0; lia| clear -CEILB pb_LBCX0; lia| clear -CEILB pa_CX0; lia| exact Ha]. }
  split.
  { eapply text_at_agree; [exact AG| exact TXT|]. intros a Ha.
    destruct TB as [(bt & Hbt & B1 & B2)| Z0]; [| exfalso; clear -CEILB Ha Z0; lia].
    eapply (OUTR bt); [apply in_or_app; right; exact Hbt| clear -CEILB Ha B1 B2; lia]. }
  split. { destruct FR as (k0 & k224 & FR). exists k0, k224. eapply rw_cells_agree_out; [exact MU| exact WM| exact FR| intros a Ha; apply OUThi; clear -CEILB Ha; lia]. }
  split. { eapply rw_cells_agree_out; [exact MU| exact WM| exact SV| intros a Ha; apply OUThi; clear -CEILB Ha pa_SQ0; lia]. }
  split.
  { assert (OF : forall A cs, rw_cells bsegs m A cs -> p_ff E <= A -> A + Z.of_nat (cells_size cs) <= p_ff E + 128 -> rw_cells bsegs m' A cs).
    { intros A cs HC' H1 H2. eapply rw_cells_agree_out; [exact MU| exact WM| exact HC'|]. intros a Ha.
      eapply (OUTsep (p_ff E) 128); [clear -CEILB pa_ffH0 EH; lia| clear -CEILB pb_Lff0; lia| clear -CEILB pb_LBff0; lia| clear -CEILB pa_ff0; lia| clear -CEILB Ha H1 H2; lia]. }
    destruct FFC as (F1 & F2 & F3 & F4 & F5 & F6). destruct pa_j0 as (J1 & J2 & J3).
    split; [apply (OF _ _ F1); [lia| unfold pffA; cbn [cells_size csize Nat.add]; lia]|].
    split; [apply (OF _ _ F2); [lia| cbn [cells_size csize Nat.add]; lia]|].
    split; [apply (OF _ _ F3); [lia| cbn [cells_size csize Nat.add]; lia]|].
    split; [apply (OF _ _ F4); [lia| cbn [cells_size csize Nat.add]; lia]|].
    split; [apply (OF _ _ F5); [lia| unfold pffZ; cbn [cells_size csize Nat.add]; lia]|].
    eapply rw_cells_agree_out; [exact MU| exact WM| exact F6|]. intros a Ha. apply OUTlow. revert Ha. unfold pffsh. cbn [cells_size csize Nat.add]. clear -CEILB pa_ff0. intros Ha. lia. }
  split. { eapply oshadow_agree; [exact AG| exact OCX|]. intros a Ha. apply OUTlow. revert Ha. unfold oshw_lo, oshw_hi, A_SB, amem. clear -CEILB pa_CX0. intros Ha. lia. }
  split; [exact STK'|]. split; [eapply stk_transport_disjoint; [exact GAP| exact MU| exact WM|]|].
  { clear -CEILB OWN pa_lo0 pa_ceil0 pa_SQ0 pa_H0 EH pb_L0 pb_LB0. induction OWN as [| [lo hi] W HO HF IH]; [exact I|]. cbn. split; [| exact IH].
    unfold ownL in HO. cbn [fst snd] in HO. lia. }
  split; [exact MI'|].
  split.
  { eapply ay_pres_trans; [exact PRES|]. eapply ay_pres_of_munch; [exact MU| exact WM|].
    intros a Ha Hc Hx. destruct Hc as [Hc|[Hc|[Hc|Hc]]].
    - apply OUThi. clear -CEILB Hc pa_SQ0. lia.
    - destruct Hc as (b & Hb & Hr). eapply OUTR; [apply in_or_app; right; exact Hb| exact Hr].
    - destruct Hc as (f' & Hf' & Hr).
      pose proof (LAYF f' (or_intror Hf')) as (F1' & F2' & _ & F4' & _). aceil.
      destruct Hr as [Hr|Hr].
      + pose proof (proj1 (LAYFB f' _ (or_intror Hf') (IN _ (yb_in_hand mh h)))) as D1. cbn [ab_addr ab_size] in D1. unfold SIZEOF_HANDLE in D1.
        pose proof (proj1 (LAYFB f' _ (or_intror Hf') (IN _ (yb_in_lexer mh h)))) as D2. cbn [ab_addr ab_size] in D2. unfold SIZEOF_LEXER in D2.
        pose proof (proj1 (LAYFB f' _ (or_intror Hf') (IN _ (yb_in_lexbuf mh h)))) as D3. cbn [ab_addr ab_size] in D3. unfold SIZEOF_BUF in D3.
        eapply ownL_outside; [exact OWN| clear -CEILB Hr F2' pa_ceil0 pa_SQ0 pa_lo0; lia| clear -CEILB Hr D1; lia| clear -CEILB Hr D2; lia| clear -CEILB Hr D3; lia].
      + apply OUTlow. revert Hr F1' F2' F4' CEILB. clear. unfold oshw_lo, oshw_hi, A_SB, amem. intros Hr F1' F2' F4' CEILB.
        assert (E0 : fst f' = 0 \/ fst f' = 1) by lia.
        destruct E0 as [E0|E0]; rewrite E0 in Hr, F1', F2';
          [change (ff_bytes 0) with 64 in F1', F2'; change (Z.shiftl 8 0) with 8 in Hr| change (ff_bytes 1) with 128 in F1', F2'; change (Z.shiftl 8 1) with 16 in Hr]; lia.
    - apply OUTlow. unfold ay_static in Hc. clear -CEILB Hc. lia. }
  pose proof (bv_unsigned_in_range 64 (p_sp E)) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  split; [eapply UFRAME; [| exact UA]; intros a Ha; apply MU; rewrite wa_unsigned by (clear -CEILB Ha SPR; lia); apply OUThi; clear -CEILB Ha pa_SQ0; lia|].
  split; [exact CRED|].
  split; [exact SOR|].
  cbn [h_set_lexer h_stack_blk]. split; [exact SB1| lk_nil].   (* [comment removed for export] *)
Qed.
End W.
End RC__1.
Arguments mk_plex {RC__} {Y}.
Arguments pmem_updL {RC__} {Y}.
Arguments ownL {Y}.
