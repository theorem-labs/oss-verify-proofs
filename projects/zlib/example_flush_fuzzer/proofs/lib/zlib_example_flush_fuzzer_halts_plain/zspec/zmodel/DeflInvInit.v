(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import Prog ZIface DeflateState Trees DeflateLz DeflateBlk Deflate
  DeflateInvHash DeflateInvKeep OverlayFBS TreeModel AdlerModel FillWinModel RefDeflateRel DeflInitLib.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import DeflateInv.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import DeflInvTally.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Lemma cfg_table_eq : forall lv, (cfg_good lv, cfg_lazy lv, cfg_nice lv, cfg_chain lv) = configuration_table lv.
Proof. intros lv. unfold cfg_good, cfg_lazy, cfg_nice, cfg_chain. destruct (configuration_table lv) as [[[g l] n] c]. reflexivity. Qed.

Lemma u16a_init : forall n f, (forall i, 0 <= f i < 65536) -> u16a (arr_init n f).
Proof. intros n f H i _. rewrite arr_get_init. apply H. Qed.
Lemma u8a_init : forall n f, (forall i, 0 <= f i < 256) -> u8a (arr_init n f).
Proof. intros n f H i _. rewrite arr_get_init. apply H. Qed.
Lemma u16a_fill0 : forall a o n, u16a a -> u16a (arr_fill a o n 0).
Proof. intros a o n H. apply u16a_fill; [exact H | lia]. Qed.

Section V.
  Variables (g0 gw gp gh gb : Z -> Z).
  Variables (b0 bw bp bh bb : blk) (cs : cstrm) (wrp wb9 meml lv strat method : Z).
  Local Notation sLM := (DeflInitLib.sLM g0 gw gp gh gb b0 bw bp bh bb cs wrp wb9 meml lv strat method).
  Local Notation sTI := (DeflInitLib.sTI g0 gw gp gh gb b0 bw bp bh bb cs wrp wb9 meml lv strat method).
  Local Notation sRK := (DeflInitLib.sRK g0 gw gp gh gb b0 bw bp bh bb cs wrp wb9 meml lv strat method).

  Lemma scalars_LM :
    ds_strstart sLM = 0 /\ ds_lookahead sLM = 0 /\ ds_insert sLM = 0 /\ ds_block_start sLM = 0 /\ ds_high_water sLM = 0
    /\ ds_ins_h sLM = 0 /\ ds_match_start sLM = init_u32 g0 176 0 /\ ds_prev_match sLM = init_u32 g0 164 0
    /\ ds_match_length sLM = 2 /\ ds_prev_length sLM = 2 /\ ds_match_available sLM = 0 /\ ds_matches sLM = 0
    /\ ds_sym_next sLM = 0 /\ ds_bi_valid sLM = 0 /\ ds_bi_buf sLM = 0 /\ ds_pending sLM = 0 /\ ds_pending_out sLM = 0
    /\ ds_last_flush sLM = -2 /\ ds_opt_len sLM = 0 /\ ds_static_len sLM = 0
    /\ ds_good_match sLM = cfg_good lv /\ ds_max_lazy_match sLM = cfg_lazy lv /\ ds_nice_match sLM = cfg_nice lv
    /\ ds_max_chain_length sLM = cfg_chain lv.
  Proof. vals_nf. repeat split; reflexivity. Qed.

  Lemma DI_LM_plain : 9 <= wb9 <= 15 -> 1 <= meml <= 9 -> 0 <= lv <= 9 -> 0 <= strat <= 4 -> method = 8 -> 0 <= wrp <= 2 ->
    u8a (cs_input cs) -> dcfg sLM /\ dinv sLM.
  Proof.
    intros Hwb Hml Hlv Hst Hm Hwr Hin.
    pose proof (sizes_LM g0 gw gp gh gb b0 bw bp bh bb cs wrp wb9 meml lv strat method) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17).
    pose proof (blks_LM g0 gw gp gh gb b0 bw bp bh bb cs wrp wb9 meml lv strat method) as (B1 & B2 & B3 & B4 & B5).
    pose proof (arrs_LM g0 gw gp gh gb b0 bw bp bh bb cs wrp wb9 meml lv strat method) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13).
    pose proof (tree_lens_LM g0 gw gp gh gb b0 bw bp bh bb cs wrp wb9 meml lv strat method) as TL.
    pose proof (strm_LM g0 gw gp gh gb b0 bw bp bh bb cs wrp wb9 meml lv strat method) as SM.
    pose proof scalars_LM as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12 & S13 & S14 & S15 & S16 & S17 & S18 & S19 & S20 & S21 & S22 & S23 & S24).
    pose proof (dwf_LM g0 gw gp gh gb b0 bw bp bh bb cs wrp wb9 meml lv strat method Hwb Hml Hlv Hst Hm Hwr) as WF.
    assert (Hp1 : 512 <= Z.shiftl 1 wb9 <= 32768).
    { rewrite Z.shiftl_1_l. split; [change 512 with (2 ^ 9); apply Z.pow_le_mono_r; lia | change 32768 with (2 ^ 15); apply Z.pow_le_mono_r; lia]. }
    assert (Hp2 : 256 <= Z.shiftl 1 (meml + 7) <= 65536).
    { rewrite Z.shiftl_1_l. split; [change 256 with (2 ^ 8); apply Z.pow_le_mono_r; lia | change 65536 with (2 ^ 16); apply Z.pow_le_mono_r; lia]. }
    assert (Hp3 : 128 <= Z.shiftl 1 (meml + 6) <= 32768).
    { rewrite Z.shiftl_1_l. split; [change 128 with (2 ^ 7); apply Z.pow_le_mono_r; lia | change 32768 with (2 ^ 15); apply Z.pow_le_mono_r; lia]. }
    assert (ST : ds_status sLM = (if wrp =? 2 then 57 else 42)) by (rewrite E10; reflexivity).
    pose proof (init_u32_range g0 176 0) as MS. pose proof (init_u32_range g0 164 0) as PM.
    assert (LU : forall off st n, arr_len (arr_u16_of g0 off st n) = n) by (intros; unfold arr_u16_of; apply arr_len_init).
    assert (DS : dsyms [] sLM).
    { constructor; cbn [length Z.of_nat zcount filter Z.mul]; rewrite ?S13, ?S19, ?S20; try reflexivity; try (apply Forall_nil).
      - intros i d lc Hi. destruct i; discriminate Hi.
      - intros c Hc. unfold Freq. cbn [tree_fc]. rewrite A1. unfold L_CODES, END_BLOCK in *.
        rewrite arr_get_set. unfold arr_inb. rewrite arr_len_fill, LU.
        destruct (Z.eqb_spec 256 c) as [<-|Hne]; cbn [andb].
        + reflexivity.
        + replace (c =? 256) with false by (symmetry; apply Z.eqb_neq; lia).
          rewrite arr_get_fill. unfold arr_inb. rewrite LU.
          replace ((0 <=? c) && (c <? 0 + Z.max 0 286) && ((0 <=? c) && (c <? 573))) with true
            by (symmetry; rewrite !Bool.andb_true_iff, !Z.leb_le, !Z.ltb_lt; lia).
          reflexivity.
      - intros j Hj. unfold Freq. cbn [tree_fc]. rewrite A3. unfold D_CODES in *.
        rewrite arr_get_fill. unfold arr_inb. rewrite LU.
        replace ((0 <=? j) && (j <? 0 + Z.max 0 30) && ((0 <=? j) && (j <? 61))) with true
          by (symmetry; rewrite !Bool.andb_true_iff, !Z.leb_le, !Z.ltb_lt; lia).
        reflexivity.
      - intros j Hj. unfold Freq. cbn [tree_fc]. rewrite A5. unfold BL_CODES in *.
        rewrite arr_get_fill. unfold arr_inb. rewrite LU.
        replace ((0 <=? j) && (j <? 0 + Z.max 0 19) && ((0 <=? j) && (j <? 39))) with true
          by (symmetry; rewrite !Bool.andb_true_iff, !Z.leb_le, !Z.ltb_lt; lia).
        reflexivity. }
    assert (HZ : forall h, 0 <= h < ds_hash_size sLM -> arr_get (ds_head sLM) h = 0).
    { intros h Hh. rewrite A13. rewrite E2 in Hh. apply head_clearedg; lia. }
    split.
    -
      destruct WF. constructor; try assumption. all: try exact TL.
      rewrite S21, S22, S23, S24, E6. apply cfg_table_eq.
    - constructor; rewrite ?S1, ?S2, ?S3, ?S4, ?S5, ?S6, ?S7, ?S8, ?S9, ?S10, ?S11, ?S12, ?S13, ?S14, ?S15, ?S16, ?S17, ?S18, ?S19, ?S20,
        ?E1, ?E2, ?E3, ?E6, ?E7, ?E9, ?E17, ?ST; unfold MAX_MATCH, MIN_MATCH, MIN_LOOKAHEAD, lz_strat in *.
      all: try (clear -Hp1 Hp2 Hp3 Hwr Hlv MS PM; lia).
      all: try (intros _; exists (fun _ : Z => False); rewrite Z.add_0_r; apply hc_inv_empty; intros h Hh; apply HZ; rewrite E2; exact Hh).
      all: try (exists (@nil (Z * Z)); split; [exact DS | intros _; cbn; lia]).
      all: try (rewrite E17; clear -Hp3; lia).
      all: try (lazymatch goal with |- _ <> _ /\ _ => idtac end; destruct (wrp =? 2); repeat split; discriminate).
      all: try (intros _; repeat split; try reflexivity; clear -Hwr; lia).
      all: try (destruct (Z.eqb_spec wrp 2) as [W|W]; [intros _; exact W | intros X; discriminate X]).
      all: try (intros W; exfalso; clear -W Hwr; lia).
      all: try (destruct (Z.eqb_spec wrp 2) as [W|W]; [intros X; discriminate X | intros _; clear -W Hwr; lia]).
      all: try (destruct (wrp =? 2); intros X; discriminate X).
      all: try (intros X; exfalso; exact (X eq_refl)).
      all: try (intros _; reflexivity).
      constructor; rewrite ?A1, ?A2, ?A3, ?A4, ?A5, ?A6, ?A7, ?A8, ?A9, ?A10, ?A11, ?A12, ?A13, ?SM.
      all: try (cbn; exact Hin).
      all: repeat lazymatch goal with |- u16a (arr_set _ _ _) => apply u16a_set; [| clear; lia] | |- u16a (arr_fill _ _ _ 0) => apply u16a_fill0 end;
           unfold arr_u16_of, arr_u8_of, blk_bytes, blk_ush;
           first [ apply u16a_init; intros i; apply init_u16_range | apply u8a_init; intros i; apply init_u8_range ].
  Qed.

  Lemma zin_sLM : zin sLM = DeflInitLib.sLM g0 gw gp gh gb b0 bw bp bh bb (cset_input cs arr0) wrp wb9 meml lv strat method.
  Proof.
    unfold zin. destruct cs. vals_nf. cbn [cset_input cset_adler cset_data_type cset_msg cset_total_out cset_total_in]. reflexivity.
  Qed.
End V.

Lemma dcfg_of_zin : forall s, dcfg (zin s) -> dcfg s.
Proof. intros s C. unfold zin in C. destruct C; constructor; dsr in *; assumption. Qed.

Theorem DI_LM : forall g0 gw gp gh gb b0 bw bp bh bb cs wrp wb9 meml lv strat method,
  9 <= wb9 <= 15 -> 1 <= meml <= 9 -> 0 <= lv <= 9 -> 0 <= strat <= 4 -> method = 8 -> 0 <= wrp <= 2 ->
  DI (DeflInitLib.sLM g0 gw gp gh gb b0 bw bp bh bb cs wrp wb9 meml lv strat method).
Proof.
  intros. split.
  - apply dcfg_of_zin. rewrite zin_sLM.
    refine (proj1 (DI_LM_plain g0 gw gp gh gb b0 bw bp bh bb (cset_input cs arr0) wrp wb9 meml lv strat method _ _ _ _ _ _ _)); try assumption.
    cbn. exact u8a_arr0.
  - rewrite zin_sLM. apply (proj2 (DI_LM_plain g0 gw gp gh gb b0 bw bp bh bb (cset_input cs arr0) wrp wb9 meml lv strat method
                                     ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(cbn; exact u8a_arr0))).
Qed.

