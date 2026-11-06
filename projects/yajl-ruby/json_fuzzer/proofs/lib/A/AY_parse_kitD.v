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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import A_iface AYajlRep AYajl_iface AY_rz AY_hand AY_acct_needs AY_parse_kit.
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
Definition mh_set_decbuf (mh : mhand) (mbd : mbuf) : mhand :=
  mkMH (mh_id mh) (mh_addr mh) (mh_lid mh) (mh_lexer mh) (mh_lexbuf mh) mbd (mh_sid mh) (mh_stack mh) (mh_ctx mh).

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
Record pdec (E : apE Y) (LK : list ablock) (mh : mhand) (h : yhandle) : Prop := mkPD {
  pd_LDB : mh_lexer mh + 48 <= mb_addr (mh_decbuf mh) \/ mb_addr (mh_decbuf mh) + 32 <= mh_lexer mh;
  pd_LBDB : mb_addr (mh_lexbuf mh) + 32 <= mb_addr (mh_decbuf mh) \/ mb_addr (mh_decbuf mh) + 32 <= mb_addr (mh_lexbuf mh);
  pd_LDDB : forall d, yb_data (lx_buf (h_lexer h)) = Some d ->
              mb_data (mh_lexbuf mh) + yb_len (lx_buf (h_lexer h)) <= mb_addr (mh_decbuf mh) \/ mb_addr (mh_decbuf mh) + 32 <= mb_data (mh_lexbuf mh);
  pd_LDD : forall d, yb_data (h_decbuf h) = Some d -> mh_lexer mh + 48 <= mb_data (mh_decbuf mh) \/ mb_data (mh_decbuf mh) + yb_len (h_decbuf h) <= mh_lexer mh;
  pd_LBDD : forall d, yb_data (h_decbuf h) = Some d ->
              mb_addr (mh_lexbuf mh) + 32 <= mb_data (mh_decbuf mh) \/ mb_data (mh_decbuf mh) + yb_len (h_decbuf h) <= mb_addr (mh_lexbuf mh);
  pd_LDDD : forall d, yb_data (lx_buf (h_lexer h)) = Some d -> forall d', yb_data (h_decbuf h) = Some d' ->
              mb_data (mh_lexbuf mh) + yb_len (lx_buf (h_lexer h)) <= mb_data (mh_decbuf mh) \/ mb_data (mh_decbuf mh) + yb_len (h_decbuf h) <= mb_data (mh_lexbuf mh);
  pd_DBT : 0 < pLEN E -> mb_addr (mh_decbuf mh) + 32 <= p_T E \/ p_T E + pLEN E <= mb_addr (mh_decbuf mh);
  pd_DDT : forall d, yb_data (h_decbuf h) = Some d -> 0 < pLEN E -> mb_data (mh_decbuf mh) + yb_len (h_decbuf h) <= p_T E \/ p_T E + pLEN E <= mb_data (mh_decbuf mh);
  pd_DBR : asep_from (mkABlock (mb_addr (mh_decbuf mh)) 32) (LK ++ p_REST E);
  pd_DDR : forall d, yb_data (h_decbuf h) = Some d -> asep_from (mkABlock (mb_data (mh_decbuf mh)) (yb_len (h_decbuf h))) (LK ++ p_REST E);
  pd_DBDD : forall d, yb_data (h_decbuf h) = Some d ->
              mb_addr (mh_decbuf mh) + 32 <= mb_data (mh_decbuf mh) \/ mb_data (mh_decbuf mh) + yb_len (h_decbuf h) <= mb_addr (mh_decbuf mh)
}.

Lemma mk_pdec : forall E s LK h mh h0 cx0 m mo,
  penvA E -> pok E h0 cx0 -> y_AHK Y s (abl (yblocks mh h) ++ LK ++ p_REST E) (pLF E) m mo ->
  mh_same (p_mh E) mh -> h_stack_blk h <> None -> pdec E LK mh h.
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
    first [ assumption
          | intros d Hd; first [ discriminate Hd | assumption | intros d' Hd'; first [discriminate Hd' | assumption] | intros Hl; apply SEPT; [assumption| exact Hl] ]
          | intros Hl; apply SEPT; [assumption| exact Hl] ].
Qed.

(* [comment removed for export] *)
Definition ownD (E : apE Y) (mh : mhand) (h : yhandle) (iv : Z * Z) : Prop :=
  (p_lo E <= fst iv /\ snd iv <= p_SQ E)
  \/ (mb_addr (mh_decbuf mh) <= fst iv /\ snd iv <= mb_addr (mh_decbuf mh) + 32)
  \/ (yb_data (h_decbuf h) <> None /\ mb_data (mh_decbuf mh) <= fst iv /\ snd iv <= mb_data (mh_decbuf mh) + yb_len (h_decbuf h)).
Lemma ownD_outside : forall E mh h W a,
  Forall (ownD E mh h) W ->
  (a < p_lo E \/ p_SQ E <= a) ->
  (a < mb_addr (mh_decbuf mh) \/ mb_addr (mh_decbuf mh) + 32 <= a) ->
  (forall d, yb_data (h_decbuf h) = Some d -> a < mb_data (mh_decbuf mh) \/ mb_data (mh_decbuf mh) + yb_len (h_decbuf h) <= a) ->
  outside W a.
Proof. aceil.
  intros E mh h W a HF H1 H2 H3. induction HF as [| [lo hi] W HO HF IH]; [exact I|].
  cbn. split; [| exact IH]. unfold ownD in HO. cbn [fst snd] in HO.
  destruct HO as [HO|[HO|[HD HO]]]; [clear -CEILB HO H1; lia| clear -CEILB HO H2; lia|].
  destruct (yb_data (h_decbuf h)) as [d|] eqn:Hd; [| exfalso; apply HD; reflexivity]. specialize (H3 d eq_refl). clear -CEILB HO H3. lia.
Qed.
Lemma ownD_write_ok : forall E s LK h mh m mo W,
  penvA E -> y_AHK Y s (abl (yblocks mh h) ++ LK ++ p_REST E) (pLF E) m mo ->
  Forall (ownD E mh h) W -> Forall (ay_write_ok (abl (yblocks mh h) ++ LK ++ p_REST E) (pLF E)) W.
Proof. aceil.
  intros E s LK h mh m mo W PA AHK HF. openPA PA.
  induction HF as [| [lo hi] W HO HF IH]; constructor; [| exact IH].
  unfold ownD in HO. unfold ay_write_ok. cbn [fst snd] in *. destruct HO as [HO|[HO|[HD HO]]].
  - left. aceil. clear -CEILB HO pa_ceil0 pa_SQ0. lia.
  - right; left. exists (mkABlock (mb_addr (mh_decbuf mh)) SIZEOF_BUF). split; [apply in_or_app; left; apply yb_in_decbuf| cbn; unfold SIZEOF_BUF; lia].
  - right; left. exists (mkABlock (mb_data (mh_decbuf mh)) (yb_len (h_decbuf h))). split; [apply in_or_app; left; apply yb_in_decdata; exact HD| cbn; lia].
Qed.

Hypothesis FRAMEY : AHK_y_frame_stmt Y.
Hypothesis UFRAME : forall m m' SP ra s0, (forall a, SP <= a < 2^47 -> m' (wa a) = m (wa a)) -> y_uanchor Y m SP ra s0 -> y_uanchor Y m' SP ra s0.

(* [comment removed for export] *)
Lemma pmem_updD : forall E m m' mo s LK h mh cx obw olw cr b' h0 cx0 W,
  penvA E -> pok E h0 cx0 -> pmem E m mo s LK h mh cx obw olw cr -> 0 < h_stack_size h ->
  munch W m m' -> wmono asegs m m' -> mem_inv asegs m' ->
  Forall (ownD E mh h) W ->
  yb_data b' = yb_data (h_decbuf h) -> yb_len b' = yb_len (h_decbuf h) ->
  abuf_rep m' (mh_decbuf mh) b' (mh_addr mh + 72) ->
  stk asegs m' (p_lo E) (p_SQ E) ->
  pmem E m' mo s LK (h_set_decbuf h b') mh cx obw olw cr.
Proof. aceil.
  intros until W. intros PA OK PM SZ MU WM MI' OWN ED EL BR' STK'.
  pose proof PM as (AY & HR & SAME & CXR & TXT & FR & SV & FFC & OCX & STK & GAP & MI & PRES & UA & CRED & SOR & SB1 & LKZ).
  apply AYST_split in AY. destruct AY as [AHK YS].
  destruct HR as (HS & LXR & DBR & BSR). pose proof HS as ((pew & pad & HC & PW) & BC1 & BC2 & BC3 & BC4).
  pose proof (mk_pblk BLKY LAYY BSHY E s LK h mh h0 cx0 m mo PA OK AHK SAME SB1 SZ) as PB.
  pose proof (mk_pdec E s LK h mh h0 cx0 m mo PA OK AHK SAME SB1) as PD.
  pose proof (ownD_write_ok E s LK h mh m mo W PA AHK OWN) as WOK.
  destruct (BLKY _ _ _ _ _ AHK) as (RNG & SEP & ND).
  destruct (LAYY _ _ _ _ _ AHK) as (LAYF & LAYFB & LAYFF).
  pose proof OK as (_ & _ & _ & _ & TB & _ & (f & FIN & FCX & FCL) & _).
  pose proof (munch_agree _ _ _ MU WM) as AG.
  assert (YB : yblocks mh (h_set_decbuf h b') = yblocks mh h) by (unfold yblocks, lexer_blocks, buf_blocks, bs_blocks; cbn [h_set_decbuf h_lexer h_decbuf h_stack_blk h_stack_size]; rewrite ED, EL; reflexivity).
  openPA PA. openPB PB. destruct PD as [pd_LDB0 pd_LBDB0 pd_LDDB0 pd_LDD0 pd_LBDD0 pd_LDDD0 pd_DBT0 pd_DDT0 pd_DBR0 pd_DDR0 pd_DBDD0]. pose proof SAME as (EH & ELx & ELB & EDB & ECX).
  assert (IN : forall b, In b (abl (yblocks mh h)) -> In b (abl (yblocks mh h) ++ LK ++ p_REST E)) by (intros b Hb; apply in_or_app; left; exact Hb).
  assert (INR : forall b, In b (LK ++ p_REST E) -> In b (abl (yblocks mh h) ++ LK ++ p_REST E)) by (intros b Hb; apply in_or_app; right; exact Hb).
  assert (DDLO : forall d, yb_data (h_decbuf h) = Some d -> (6303744 <= mb_data (mh_decbuf mh) /\ (mb_data (mh_decbuf mh) + yb_len (h_decbuf h) <= 2147446784 \/ 17594333495296 <= mb_data (mh_decbuf mh)))).
  { intros d Hd. destruct DBR as (_ & BD & _). unfold RYajlRep.buf_data in BD. rewrite Hd in BD. destruct BD as (UL & _).
    pose proof (proj2 (BSHY _ _ _ _ _ _ AHK (IN _ (yb_in_decdata mh h ltac:(rewrite Hd; discriminate))) ltac:(cbn; clear -CEILB UL; lia))) as X.
    cbn [ab_addr ab_size] in X. unfold oshw_hi, A_SB, amem in X. clear -CEILB X. lia. }
  (* [comment removed for export] *)
  assert (OUTsep : forall A n a, (A + n <= mb_addr (mh_decbuf mh) \/ mb_addr (mh_decbuf mh) + 32 <= A) ->
            (forall d, yb_data (h_decbuf h) = Some d -> A + n <= mb_data (mh_decbuf mh) \/ mb_data (mh_decbuf mh) + yb_len (h_decbuf h) <= A) ->
            A + n <= alloc_ceiling -> A <= a < A + n -> outside W a).
  { intros A n a D1 D2 Rb Ha. eapply ownD_outside; [exact OWN| clear -CEILB Ha Rb pa_ceil0; lia| clear -CEILB Ha D1; lia| intros d Hd; specialize (D2 d Hd); clear -CEILB Ha D2; lia]. }
  assert (OUTlow : forall a, (a < 6303744 \/ 2147446784 <= a < 17594333495296) -> outside W a).   (* [comment removed for export] *)
  { intros a Ha. eapply ownD_outside; [exact OWN| clear -CEILB Ha pa_ceil0; lia| clear -CEILB Ha pb_DB0; lia| intros d Hd; pose proof (DDLO d Hd) as QQ; clear -CEILB Ha QQ; lia]. }
  assert (OUThi : forall a, p_SQ E <= a -> outside W a).
  { intros a Ha. eapply ownD_outside; [exact OWN| clear -CEILB Ha; lia| clear -CEILB Ha pb_DB0 pa_lo0 pa_ceil0 pa_SQ0; lia| intros d Hd; pose proof (pb_DD0 d Hd) as QQ; pose proof (DDLO d Hd) as QQ2; clear -CEILB Ha QQ QQ2 pa_lo0 pa_ceil0 pa_SQ0; lia]. }
  (* [comment removed for export] *)
  assert (OUTR : forall b a, In b (LK ++ p_REST E) -> ab_addr b <= a < ab_addr b + ab_size b -> outside W a).
  { intros b a Hb Ha.
    pose proof (asep_from_In _ _ _ pd_DBR0 Hb) as D1. unfold absep in D1. cbn [ab_addr ab_size] in D1.
    pose proof (RNG _ (INR _ Hb)) as Rb. unfold ablock_range in Rb. aceil.
    eapply (OUTsep (ab_addr b) (ab_size b)); [clear -CEILB D1; lia| | clear -CEILB Rb; lia| exact Ha].
    intros d Hd. pose proof (asep_from_In _ _ _ (pd_DDR0 d Hd) Hb) as D2. unfold absep in D2. cbn [ab_addr ab_size] in D2. clear -CEILB D2. lia. }
  split.
  { rewrite YB. apply AYST_split. split; [eapply FRAMEY; [exact AHK| exact MU| exact WM| exact WOK]|].
    eapply aystatics_munch; [exact YS| exact MU| exact WM|].
    clear -CEILB OWN pb_DB0 DDLO pa_ceil0. induction OWN as [| [lo hi] W HO HF IH]; constructor; [| exact IH].
    unfold ownD in HO. cbn [fst snd] in *. right. destruct HO as [HO|[HO|[HD HO]]]; [lia| lia|].
    destruct (yb_data (h_decbuf h)) as [d|] eqn:Hd; [| exfalso; apply HD; reflexivity]. pose proof (DDLO d eq_refl) as QQ. lia. }
  split.
  { split; [| split; [| split]].
    - (* [comment removed for export] *)
      split; [| cbn [h_set_decbuf h_bytesConsumed h_stack_size h_stack_blk h_parseError]; split; [exact BC1| split; [exact BC2| split; [exact BC3| exact BC4]]]].
      exists pew, pad. split; [| exact PW].
      eapply rw_cells_agree; [exact AG| exact HC|]. rewrite hand_cells_size. intros a Ha.
      eapply (OUTsep (mh_addr mh) 104); [clear -CEILB pb_HDB0 EH; lia| intros d Hd; pose proof (pb_HDD0 d Hd) as QQ; clear -CEILB QQ EH; lia| clear -CEILB pa_H0 EH; lia| exact Ha].
    - cbn [h_set_decbuf h_lexer]. eapply lexer_rep_agree; [exact AG| exact LXR| | |].
      + intros a Ha. unfold SIZEOF_LEXER in Ha. eapply (OUTsep (mh_lexer mh) 48); [exact pd_LDB0| exact pd_LDD0| clear -CEILB pb_L0; lia| exact Ha].
      + intros a Ha. unfold SIZEOF_BUF in Ha. eapply (OUTsep (mb_addr (mh_lexbuf mh)) 32); [exact pd_LBDB0| exact pd_LBDD0| clear -CEILB pb_LB0; lia| exact Ha].
      + intros HD a Ha. destruct (yb_data (lx_buf (h_lexer h))) as [d|] eqn:Hd; [| exfalso; apply HD; reflexivity].
        eapply (OUTsep (mb_data (mh_lexbuf mh)) (yb_len (lx_buf (h_lexer h)))); [exact (pd_LDDB0 d eq_refl)| exact (pd_LDDD0 d eq_refl)| pose proof (pb_LD0 d eq_refl) as QQ; clear -CEILB QQ; lia| exact Ha].
    - cbn [h_set_decbuf h_decbuf]. exact BR'.
    - eapply bs_rep_agree; [exact AG| | | cbn [h_set_decbuf h_stack_size]; unfold h_used; cbn [h_stack h_set_decbuf]; unfold h_used in BC3; clear -CEILB BC3; lia].
      + unfold RYajlRep.bs_rep in BSR |- *. cbn [h_stack_blk h_set_decbuf h_stack h_stack_size]. exact BSR.
      + cbn [h_set_decbuf h_stack_size]. intros a Ha. eapply (OUTsep (mh_stack mh) (h_stack_size h)); [clear -CEILB pb_DBSB0; lia| intros d Hd; pose proof (pb_DDSB0 d Hd) as QQ; clear -CEILB QQ; lia| clear -CEILB pb_SB0; lia| exact Ha]. }
  split; [exact SAME|].
  split. { eapply ctx_rep_agree; [exact AG| exact CXR|]. intros a Ha. eapply (OUTsep (pCX E) 8); [clear -CEILB pb_DBCX0; lia| intros d Hd; pose proof (pb_DDCX0 d Hd) as QQ; clear -CEILB QQ; lia| clear -CEILB pa_CX0; lia| exact Ha]. }
  split.
  { eapply text_at_agree; [exact AG| exact TXT|]. intros a Ha.
    destruct (Z.eq_dec (zlength (p_txt E)) 0) as [Z0|NZ]; [exfalso; clear -CEILB Ha Z0; lia|].
    assert (Hl : 0 < zlength (p_txt E)) by (clear -CEILB NZ pa_len0; lia).
    pose proof (pa_OT0 Hl) as (_ & _ & T5 & _ & T6).
    eapply (OUTsep (p_T E) (zlength (p_txt E))); [pose proof (pd_DBT0 Hl) as QQ; clear -CEILB QQ; lia| intros d Hd; pose proof (pd_DDT0 d Hd Hl) as QQ; clear -CEILB QQ; lia| clear -CEILB T5 T6; lia| exact Ha]. }
  split. { destruct FR as (k0 & k224 & FR). exists k0, k224. eapply rw_cells_agree_out; [exact MU| exact WM| exact FR| intros a Ha; apply OUThi; clear -CEILB Ha; lia]. }
  split. { eapply rw_cells_agree_out; [exact MU| exact WM| exact SV| intros a Ha; apply OUThi; clear -CEILB Ha pa_SQ0; lia]. }
  split.
  { assert (OF : forall A cs, rw_cells asegs m A cs -> p_ff E <= A -> A + Z.of_nat (cells_size cs) <= p_ff E + 128 -> rw_cells asegs m' A cs).
    { intros A cs HC' H1 H2. eapply rw_cells_agree_out; [exact MU| exact WM| exact HC'|]. intros a Ha.
      eapply (OUTsep (p_ff E) 128); [clear -CEILB pb_DBff0; lia| intros d Hd; pose proof (pb_DDff0 d Hd) as QQ; clear -CEILB QQ; lia| clear -CEILB pa_ff0; lia| clear -CEILB Ha H1 H2; lia]. }
    destruct FFC as (F1 & F2 & F3 & F4 & F5 & F6). destruct pa_j0 as (J1 & J2 & J3).
    split; [apply (OF _ _ F1); [lia| unfold pffA; cbn [cells_size csize Nat.add]; lia]|].
    split; [apply (OF _ _ F2); [lia| cbn [cells_size csize Nat.add]; lia]|].
    split; [apply (OF _ _ F3); [lia| cbn [cells_size csize Nat.add]; lia]|].
    split; [apply (OF _ _ F4); [lia| cbn [cells_size csize Nat.add]; lia]|].
    split; [apply (OF _ _ F5); [lia| unfold pffZ; cbn [cells_size csize Nat.add]; lia]|].
    eapply rw_cells_agree_out; [exact MU| exact WM| exact F6|]. intros a Ha. apply OUTlow. revert Ha. unfold pffsh. cbn [cells_size csize Nat.add]. clear -CEILB pa_ff0. intros Ha. lia. }
  split. { eapply oshadow_agree; [exact AG| exact OCX|]. intros a Ha. apply OUTlow. revert Ha. unfold oshw_lo, oshw_hi, A_SB, amem. clear -CEILB pa_CX0. intros Ha. lia. }
  split; [exact STK'|]. split; [eapply stk_transport_disjoint; [exact GAP| exact MU| exact WM|]|].
  { clear -CEILB OWN pb_DB0 pb_DD0 DDLO pa_lo0 pa_ceil0 pa_SQ0. induction OWN as [| [lo hi] W HO HF IH]; [exact I|]. cbn. split; [| exact IH].
    unfold ownD in HO. cbn [fst snd] in HO. destruct HO as [HO|[HO|[HD HO]]]; [clear -CEILB HO; lia| clear -CEILB HO pb_DB0 pa_lo0 pa_ceil0 pa_SQ0; lia|].
    destruct (yb_data (h_decbuf h)) as [d|] eqn:Hd; [| exfalso; apply HD; reflexivity]. pose proof (DDLO d eq_refl) as QQ. pose proof (pb_DD0 d eq_refl) as QQ2.
    clear -CEILB HO QQ QQ2 pa_lo0 pa_ceil0 pa_SQ0. lia. }
  split; [exact MI'|].
  split.
  { eapply ay_pres_trans; [exact PRES|]. eapply ay_pres_of_munch; [exact MU| exact WM|].
    intros a Ha Hc Hx. destruct Hc as [Hc|[Hc|[Hc|Hc]]].
    - apply OUThi. clear -CEILB Hc pa_SQ0. lia.
    - destruct Hc as (b & Hb & Hr). eapply OUTR; [apply in_or_app; right; exact Hb| exact Hr].
    - destruct Hc as (f' & Hf' & Hr).
      pose proof (LAYF f' (or_intror Hf')) as (F1' & F2' & _ & F4' & _). aceil.
      destruct Hr as [Hr|Hr].
      + pose proof (proj1 (LAYFB f' _ (or_intror Hf') (IN _ (yb_in_decbuf mh h)))) as D1. cbn [ab_addr ab_size] in D1. unfold SIZEOF_BUF in D1.
        eapply ownD_outside; [exact OWN| clear -CEILB Hr F2' pa_ceil0 pa_SQ0 pa_lo0; lia| clear -CEILB Hr D1; lia|].
        intros d Hd. pose proof (proj1 (LAYFB f' _ (or_intror Hf') (IN _ (yb_in_decdata mh h ltac:(rewrite Hd; discriminate))))) as D2. cbn [ab_addr ab_size] in D2. clear -CEILB Hr D2. lia.
      + apply OUTlow. revert Hr F1' F2' F4' CEILB. clear. unfold oshw_lo, oshw_hi, A_SB, amem. intros Hr F1' F2' F4' CEILB.
        assert (E0 : fst f' = 0 \/ fst f' = 1) by lia.
        destruct E0 as [E0|E0]; rewrite E0 in Hr, F1', F2';
          [change (ff_bytes 0) with 64 in F1', F2'; change (Z.shiftl 8 0) with 8 in Hr| change (ff_bytes 1) with 128 in F1', F2'; change (Z.shiftl 8 1) with 16 in Hr]; lia.
    - apply OUTlow. unfold ay_static in Hc. clear -CEILB Hc. lia. }
  pose proof (bv_unsigned_in_range 64 (p_sp E)) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  split; [eapply UFRAME; [| exact UA]; intros a Ha; apply MU; rewrite wa_unsigned by (clear -CEILB Ha SPR; lia); apply OUThi; clear -CEILB Ha pa_SQ0; lia|].
  split; [exact CRED|].
  split; [exact SOR|].
  cbn [h_set_decbuf h_stack_blk]. split; [exact SB1| lk_nil].   (* [comment removed for export] *)
Qed.

(* [comment removed for export] *)
Definition ownO (E : apE Y) (iv : Z * Z) : Prop :=
  (p_lo E <= fst iv /\ snd iv <= p_SQ E)
  \/ (fst iv = p_ff E + 32 /\ snd iv = p_ff E + 40)
  \/ (fst iv = p_ff E + 64 /\ snd iv = p_ff E + 68).
Lemma ownO_outside : forall E W a,
  Forall (ownO E) W -> (a < p_lo E \/ p_SQ E <= a) ->
  (a < p_ff E + 32 \/ p_ff E + 40 <= a) -> (a < p_ff E + 64 \/ p_ff E + 68 <= a) -> outside W a.
Proof. aceil.
  intros E W a HF H1 H2 H3. induction HF as [| [lo hi] W HO HF IH]; [exact I|].
  cbn. split; [| exact IH]. unfold ownO in HO. cbn [fst snd] in HO. clear -CEILB HO H1 H2 H3. lia.
Qed.

(* [comment removed for export] *)
Lemma pmem_updO : forall E m m' mo s LK h mh cx obw olw cr obw' olw' h0 cx0 W,
  penvA E -> pok E h0 cx0 -> pmem E m mo s LK h mh cx obw olw cr -> 0 < h_stack_size h ->
  munch W m m' -> wmono asegs m m' -> mem_inv asegs m' ->
  Forall (ownO E) W ->
  rw_cells asegs m' (p_ff E + 32) [C8 obw'] -> rw_cells asegs m' (p_ff E + 64) [C4 olw'] ->
  stk asegs m' (p_lo E) (p_SQ E) ->
  pmem E m' mo s LK h mh cx obw' olw' cr.
Proof. aceil.
  intros until W. intros PA OK PM SZ MU WM MI' OWN OB' OL' STK'.
  pose proof PM as (AY & HR & SAME & CXR & TXT & FR & SV & FFC & OCX & STK & GAP & MI & PRES & UA & CRED & SOR & SB1 & LKZ).
  apply AYST_split in AY. destruct AY as [AHK YS].
  pose proof (mk_pblk BLKY LAYY BSHY E s LK h mh h0 cx0 m mo PA OK AHK SAME SB1 SZ) as PB.
  destruct (BLKY _ _ _ _ _ AHK) as (RNG & SEP & ND).
  destruct (LAYY _ _ _ _ _ AHK) as (LAYF & LAYFB & LAYFF).
  pose proof OK as (_ & _ & _ & _ & TB & _ & (f & FIN & FCX & FCL) & _ & _ & _ & _ & _ & FFR0).
  pose proof (munch_agree _ _ _ MU WM) as AG.
  openPA PA. openPB PB. pose proof SAME as (EH & ELx & ELB & EDB & ECX).
  assert (WOK : Forall (ay_write_ok (abl (yblocks mh h) ++ LK ++ p_REST E) (pLF E)) W).
  { clear -CEILB OWN pa_ceil0 pa_SQ0 pa_lo0. induction OWN as [| [lo hi] W HO HF IH]; constructor; [| exact IH].
    unfold ownO in HO. unfold ay_write_ok. cbn [fst snd] in *. destruct HO as [HO|[HO|HO]].
    - left. aceil. lia.
    - right; right; left. exists (1, p_ff E). split; [left; reflexivity|]. cbn [fst snd]. unfold ff_bytes. change (Z.shiftl 64 1) with 128. lia.
    - right; right; left. exists (1, p_ff E). split; [left; reflexivity|]. cbn [fst snd]. unfold ff_bytes. change (Z.shiftl 64 1) with 128. lia. }
  (* [comment removed for export] *)
  assert (OUTlow : forall a, a < p_ff E + 32 -> outside W a).
  { intros a Ha. eapply ownO_outside; [exact OWN| clear -CEILB Ha pa_ff0 pa_ceil0; lia| clear -CEILB Ha; lia| clear -CEILB Ha; lia]. }
  assert (OUTsh : forall a, 2147446784 <= a < 17594333495296 -> outside W a).   (* [comment removed for export] *)
  { intros a Ha. yshow pa_ffP0. eapply ownO_outside; [exact OWN| clear -CEILB Ha pa_ceil0; lia| clear -CEILB Ha pa_ff0 pa_ffP0; lia| clear -CEILB Ha pa_ff0 pa_ffP0; lia]. }
  assert (OUThi : forall a, p_SQ E <= a -> outside W a).
  { intros a Ha. eapply ownO_outside; [exact OWN| clear -CEILB Ha; lia| clear -CEILB Ha pa_ff0 pa_ceil0 pa_SQ0 pa_lo0; lia| clear -CEILB Ha pa_ff0 pa_ceil0 pa_SQ0 pa_lo0; lia]. }
  assert (OUTff : forall a, (a < p_ff E \/ p_ff E + 128 <= a) -> a < alloc_ceiling -> outside W a).
  { intros a Ha Hc. eapply ownO_outside; [exact OWN| clear -CEILB Hc pa_ceil0; lia| clear -CEILB Ha; lia| clear -CEILB Ha; lia]. }
  (* [comment removed for export] *)
  assert (OUTB : forall b a, In b (abl (yblocks mh h) ++ LK ++ p_REST E) -> ab_addr b <= a < ab_addr b + ab_size b -> outside W a).
  { intros b a Hb Ha. pose proof (proj1 (LAYFB (1, p_ff E) b (or_introl eq_refl) Hb)) as D. cbn [fst snd] in D. unfold ff_bytes in D. change (Z.shiftl 64 1) with 128 in D.
    pose proof (RNG _ Hb) as Rb. unfold ablock_range in Rb. aceil.
    apply OUTff; [clear -CEILB D Ha; lia| clear -CEILB Rb Ha; lia]. }
  assert (IN : forall b, In b (abl (yblocks mh h)) -> In b (abl (yblocks mh h) ++ LK ++ p_REST E)) by (intros b Hb; apply in_or_app; left; exact Hb).
  split.
  { apply AYST_split. split; [eapply FRAMEY; [exact AHK| exact MU| exact WM| exact WOK]|].
    eapply aystatics_munch; [exact YS| exact MU| exact WM|].
    clear -CEILB OWN pa_ff0 pa_ceil0. induction OWN as [| [lo hi] W HO HF IH]; constructor; [| exact IH].
    unfold ownO in HO. cbn [fst snd] in *. right. lia. }
  split.
  { eapply hand_rep_agree; [exact AG| exact HR|]. intros a Ha.
    unfold yfoot in Ha. destruct Ha as (b & Hb & Hr). eapply OUTB; [apply IN; exact Hb| exact Hr]. }
  split; [exact SAME|].
  split. { eapply ctx_rep_agree; [exact AG| exact CXR|]. intros a Ha. apply OUTff; [clear -CEILB Ha pa_ffCX0; lia| clear -CEILB Ha pa_CX0; lia]. }
  split.
  { eapply text_at_agree; [exact AG| exact TXT|]. intros a Ha.
    destruct TB as [(bt & Hbt & B1 & B2)| Z0]; [| exfalso; clear -CEILB Ha Z0; lia].
    eapply (OUTB bt); [apply in_or_app; right; apply in_or_app; right; exact Hbt| clear -CEILB Ha B1 B2; lia]. }
  split. { destruct FR as (k0 & k224 & FR). exists k0, k224. eapply rw_cells_agree_out; [exact MU| exact WM| exact FR| intros a Ha; apply OUThi; clear -CEILB Ha; lia]. }
  split. { eapply rw_cells_agree_out; [exact MU| exact WM| exact SV| intros a Ha; apply OUThi; clear -CEILB Ha pa_SQ0; lia]. }
  split.
  { destruct FFC as (F1 & F2 & F3 & F4 & F5 & F6). destruct pa_j0 as (J1 & J2 & J3).
    split; [eapply rw_cells_agree_out; [exact MU| exact WM| exact F1| intros a Ha; apply OUTlow; unfold pffA in Ha; cbn [cells_size csize Nat.add] in Ha; clear -CEILB Ha; lia]|].
    split; [exact OB'|].
    split; [eapply rw_cells_agree_out; [exact MU| exact WM| exact F3| intros a Ha; cbn [cells_size csize Nat.add] in Ha;
            eapply ownO_outside; [exact OWN| clear -CEILB Ha pa_ff0 pa_ceil0; lia| clear -CEILB Ha; lia| clear -CEILB Ha; lia]]|].
    split; [exact OL'|].
    split; [eapply rw_cells_agree_out; [exact MU| exact WM| exact F5| intros a Ha; unfold pffZ in Ha; cbn [cells_size csize Nat.add] in Ha;
            eapply ownO_outside; [exact OWN| clear -CEILB Ha pa_ff0 pa_ceil0; lia| clear -CEILB Ha; lia| clear -CEILB Ha; lia]]|].
    eapply rw_cells_agree_out; [exact MU| exact WM| exact F6|]. intros a Ha. apply OUTsh. revert Ha. unfold pffsh. cbn [cells_size csize Nat.add]. clear -CEILB pa_ff0. intros Ha. lia. }
  split. { eapply oshadow_agree; [exact AG| exact OCX|]. intros a Ha. apply OUTsh. revert Ha. unfold oshw_lo, oshw_hi, A_SB, amem. clear -CEILB pa_CX0 pa_ff0. intros Ha. lia. }
  split; [exact STK'|]. split; [eapply stk_transport_disjoint; [exact GAP| exact MU| exact WM|]|].
  { clear -CEILB OWN pa_ff0 pa_lo0 pa_ceil0 pa_SQ0. induction OWN as [| [lo hi] W HO HF IH]; [exact I|]. cbn. split; [| exact IH].
    unfold ownO in HO. cbn [fst snd] in HO. lia. }
  split; [exact MI'|].
  split.
  { eapply ay_pres_trans; [exact PRES|]. eapply ay_pres_of_munch; [exact MU| exact WM|].
    intros a Ha Hc Hx. destruct Hc as [Hc|[Hc|[Hc|Hc]]].
    - apply OUThi. clear -CEILB Hc pa_SQ0. lia.
    - destruct Hc as (b & Hb & Hr). eapply OUTB; [apply in_or_app; right; apply in_or_app; right; exact Hb| exact Hr].
    - destruct Hc as (f' & Hf' & Hr). pose proof (FFR0 f' Hf') as D.
      pose proof (LAYF f' (or_intror Hf')) as (F1' & F2' & _ & F4' & _). aceil.
      destruct Hr as [Hr|Hr]; [apply OUTff; [clear -CEILB D Hr; lia| clear -CEILB Hr F2'; lia]|].
      apply OUTsh. yshow pa_ffP0. revert Hr F1' F2' F4' pa_ff0 pa_ffP0 CEILB. clear. unfold oshw_lo, oshw_hi, A_SB, amem. intros Hr F1' F2' F4' PFF PFFP CEILB.
      assert (E0 : fst f' = 0 \/ fst f' = 1) by lia.
      destruct E0 as [E0|E0]; rewrite E0 in Hr, F1', F2';
        [change (ff_bytes 0) with 64 in F1', F2'; change (Z.shiftl 8 0) with 8 in Hr| change (ff_bytes 1) with 128 in F1', F2'; change (Z.shiftl 8 1) with 16 in Hr]; lia.
    - apply OUTlow. unfold ay_static in Hc. clear -CEILB Hc pa_ff0. lia. }
  pose proof (bv_unsigned_in_range 64 (p_sp E)) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  split; [eapply UFRAME; [| exact UA]; intros a Ha; apply MU; rewrite wa_unsigned by (clear -CEILB Ha SPR; lia); apply OUThi; clear -CEILB Ha pa_SQ0; lia|].
  split; [exact CRED|].
  split; [exact SOR|].
  split; [exact SB1| lk_nil].   (* [comment removed for export] *)
Qed.
End W.
End RC__1.
Arguments mk_pdec {RC__} {Y}.
Arguments pmem_updD {RC__} {Y}.
Arguments pmem_updO {RC__} {Y}.
Arguments ownO {Y}.
