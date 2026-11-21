(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import CompressModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import FlushBlockModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import BuildTreeModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import BitsModel2.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import TrSmallModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import Trees.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateBlk.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import Deflate.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateSafe.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateOverlay.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflateRel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeL1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeZ.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeG.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflFastM.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflFast1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeS.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeI1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeI2.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeI3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition BFPRE (c0 : cstrm) (s : deflate_state) (flush : Z) : Prop :=
  C0OK' c0 /\ DC c0 s /\ ds_pending s = 0 /\ ds_status s <> FINISH_STATE /\ 0 <= flush <= 5.

Definition BFPOST (c0 : cstrm) (s : deflate_state) (flush : Z) (r : deflate_state * block_state) : Prop :=
  let s' := fst r in let b := snd r in
  DC c0 s' /\ KV s' = KV s /\ OUTLE s s'
  /\ (b = block_done -> ds_pending s' = 0 /\ flush <> Z_FINISH /\ ds_match_available s' = 0)
  /\ (b = finish_started \/ b = finish_done -> ds_lookahead s' = 0)
  /\ (b = finish_done -> ds_pending s' = 0).

Definition BF_SPEC (m : Z) (SAFE : deflate_state -> Z -> Prop) (f : deflate_state -> Z -> deflate_state * block_state) : Prop :=
  forall c0 s flush, BFPRE c0 s flush -> dmode s = m -> SAFE s flush /\ BFPOST c0 s flush (f s flush).

Section Integrate.
  Variable SAFEs : deflate_state -> Z -> Prop.
Variable SAFEf : deflate_state -> Z -> Prop.
Variable SAFEw : deflate_state -> Z -> Prop.
  Variable FB : deflate_state -> option Z -> Z -> Z -> Prop.

  Hypothesis Hst : BF_SPEC 0 SAFEs deflate_stored.
  Hypothesis Hhf : BF_SPEC 1 (huff_ok FB) deflate_huff.
  Hypothesis Hrl : BF_SPEC 2 (rle_ok FB) deflate_rle.
  Hypothesis Hfa : BF_SPEC 3 SAFEf deflate_fast.
  Hypothesis Hsl : BF_SPEC 4 SAFEw deflate_slow.

  Local Notation DOK := (@DOK).
  Local Notation dpost_ok := (dpost_ok dwf).

  (* [comment removed for export] *)
  Section Call.
    Variable c0 : cstrm.
Variable s0 : deflate_state.
    Hypothesis HC0 : C0OK' c0.
    Hypothesis Hs0 : ds_strm s0 = c0.
    Hypothesis D0 : dwf s0.
    Let HC0w : C0OK c0 := c0'_ok _ HC0.

    (* [comment removed for export] *)
    Definition ST (s : deflate_state) : Prop := DC c0 s /\ KV s = KV s0.

    Lemma ST_DOK : forall s, ST s -> DOK s.
    Proof. intros s [H _]. exact (DC_DOK c0 s HC0w H). Qed.

    Lemma ST_dpost : forall s rc, ST s -> - 2 ^ 31 <= rc < 2 ^ 31 -> dpost_ok s0 s rc.
    Proof. intros s rc [H K] Hrc. exact (DC_dpost c0 s0 s rc HC0 Hs0 D0 H K Hrc). Qed.

    Lemma ST_err_return : forall s e, ST s -> ST (fst (err_return s e)).
    Proof. intros s e [H K]. split; [apply DC_err_return; exact H | rewrite KV_err_return; exact K]. Qed.

    Lemma ST_set_last_flush : forall s v, ST s -> - 2 <= v <= 5 -> ST (set_last_flush s v).
    Proof. intros s v [H K] Hv. split; [apply DC_set_last_flush; [exact Hv | exact H] | rewrite KV_set_last_flush; exact K]. Qed.

    Lemma ST_flush_pending : forall s, ST s ->
      ST (flush_pending s) /\ fp_ok s /\ (ds_pending (flush_pending s) = 0 \/ cs_avail_out (ds_strm (flush_pending s)) = 0)
      /\ 0 <= ds_pending (flush_pending s) <= ds_pending s
      /\ ds_status (flush_pending s) = ds_status s /\ ds_wrap (flush_pending s) = ds_wrap s
      /\ ds_lookahead (flush_pending s) = ds_lookahead s /\ cs_avail_in (ds_strm (flush_pending s)) = cs_avail_in (ds_strm s).
    Proof.
      intros s [H K].
      destruct (DC_flush_pending c0 s HC0w H) as (H' & K' & _ & C2 & Hfp & Hp & Hor & _ & _ & _ & Hai & _).
      pose proof (dx_core2_fields _ _ C2) as F.
      split; [split; [exact H' | rewrite K'; exact K]|]. split; [exact Hfp|]. split; [exact Hor|]. split; [exact Hp|].
      destruct F as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F17 & _ & _ & _ & F21 & F22 & _).
      repeat split; assumption.
    Qed.

    Lemma Z_OK_range : - 2 ^ 31 <= Z_OK < 2 ^ 31. Proof. unfold Z_OK. lia. Qed.

    Lemma Z_STREAM_END_range : - 2 ^ 31 <= Z_STREAM_END < 2 ^ 31. Proof. unfold Z_STREAM_END. lia. Qed.

    (* [comment removed for export] *)
    Lemma hdr_zlib : forall s, ST s -> ds_pending s = 0 -> ds_status s = INIT_STATE ->
      hdr_ok dwf s0 s (zhdr_st s) 6
      /\ ST (flush_pending (zhdr_st s))
      /\ ds_status (flush_pending (zhdr_st s)) = BUSY_STATE
      /\ (ds_pending (flush_pending (zhdr_st s)) = 0 \/ cs_avail_out (ds_strm (flush_pending (zhdr_st s))) = 0)
      /\ cs_avail_in (ds_strm (flush_pending (zhdr_st s))) = cs_avail_in (ds_strm s)
      /\ ds_lookahead (flush_pending (zhdr_st s)) = ds_lookahead s /\ ds_wrap (flush_pending (zhdr_st s)) = ds_wrap s.
    Proof.
      intros s HS Hp Hst0. pose proof HS as [H K]. pose proof H as [[D X] V]. pose proof (dwf_sizes s D) as (_ & _ & Sl & _).
      destruct (zhdr_facts c0 s H Hp Hst0) as ((H1 & Po1 & P1) & K1 & O1 & St1 & Ai1 & Lk1 & Wr1).
      assert (HS1 : ST (zhdr_st s)) by (split; [exact H1 | rewrite K1; exact K]).
      destruct (ST_flush_pending _ HS1) as (HS2 & Hfp & Hor & Hp2 & St2 & Wr2 & Lk2 & Ai2).
      pose proof HS2 as [[[D2 X2] V2] K2]. pose proof (df_pend _ D2).
      split.
      { unfold hdr_ok. split; [exact (ST_DOK s HS)|]. split; [lia|]. split; [exact (ST_DOK _ HS1)|]. split; [exact Hfp|].
        cbv zeta. split; [exact (ST_DOK _ HS2)|]. split; [pose proof (dwf_sizes _ D2); lia|].
        intros _. apply ST_dpost; [apply ST_set_last_flush; [exact HS2 | lia] | apply Z_OK_range]. }
      split; [exact HS2|]. split; [rewrite St2; exact St1|]. split; [exact Hor|].
      rewrite Ai2, Lk2, Wr2. split; [exact Ai1 | split; [exact Lk1 | exact Wr1]].
    Qed.

    Lemma hdr_gzip : forall s, ST s -> ds_pending s = 0 -> ds_status s = GZIP_STATE ->
      hdr_ok dwf s0 s (gzhdr_st s) 10
      /\ ST (flush_pending (gzhdr_st s))
      /\ ds_status (flush_pending (gzhdr_st s)) = BUSY_STATE
      /\ (ds_pending (flush_pending (gzhdr_st s)) = 0 \/ cs_avail_out (ds_strm (flush_pending (gzhdr_st s))) = 0)
      /\ cs_avail_in (ds_strm (flush_pending (gzhdr_st s))) = cs_avail_in (ds_strm s)
      /\ ds_lookahead (flush_pending (gzhdr_st s)) = ds_lookahead s /\ ds_wrap (flush_pending (gzhdr_st s)) = ds_wrap s.
    Proof.
      intros s HS Hp Hst0. pose proof HS as [H K]. pose proof H as [[D X] V]. pose proof (dwf_sizes s D) as (_ & _ & Sl & _).
      destruct (gzhdr_facts c0 s H Hp Hst0) as ((H1 & Po1 & P1) & K1 & O1 & St1 & Ai1 & Lk1 & Wr1).
      assert (HS1 : ST (gzhdr_st s)) by (split; [exact H1 | rewrite K1; exact K]).
      destruct (ST_flush_pending _ HS1) as (HS2 & Hfp & Hor & Hp2 & St2 & Wr2 & Lk2 & Ai2).
      pose proof HS2 as [[[D2 X2] V2] K2]. pose proof (df_pend _ D2).
      split.
      { unfold hdr_ok. split; [exact (ST_DOK s HS)|]. split; [lia|]. split; [exact (ST_DOK _ HS1)|]. split; [exact Hfp|].
        cbv zeta. split; [exact (ST_DOK _ HS2)|]. split; [pose proof (dwf_sizes _ D2); lia|].
        intros _. apply ST_dpost; [apply ST_set_last_flush; [exact HS2 | lia] | apply Z_OK_range]. }
      split; [exact HS2|]. split; [rewrite St2; exact St1|]. split; [exact Hor|].
      rewrite Ai2, Lk2, Wr2. split; [exact Ai1 | split; [exact Lk1 | exact Wr1]].
    Qed.

    (* [comment removed for export] *)
    Lemma dmode_cases : forall s (P0 P1 P2 P3 P4 : Prop),
      (dmode s = 0 -> P0) -> (dmode s = 1 -> P1) -> (dmode s = 2 -> P2) -> (dmode s = 3 -> P3) -> (dmode s = 4 -> P4) ->
      (if ds_level s =? 0 then P0
       else if ds_strategy s =? Z_HUFFMAN_ONLY then P1
       else if ds_strategy s =? Z_RLE then P2
       else if ds_level s <=? 3 then P3 else P4).
    Proof.
      intros s P0 P1 P2 P3 P4 H0 H1 H2 H3 H4. unfold dmode in *.
      destruct (ds_level s =? 0); [exact (H0 eq_refl)|]. destruct (ds_strategy s =? Z_HUFFMAN_ONLY); [exact (H1 eq_refl)|].
      destruct (ds_strategy s =? Z_RLE); [exact (H2 eq_refl)|]. destruct (ds_level s <=? 3); [exact (H3 eq_refl) | exact (H4 eq_refl)].
    Qed.

    (* [comment removed for export] *)
    Lemma bf_call : forall s flush, ST s -> ds_pending s = 0 -> ds_status s <> FINISH_STATE -> 0 <= flush <= 5 ->
      (if ds_level s =? 0 then SAFEs s flush
       else if ds_strategy s =? Z_HUFFMAN_ONLY then huff_ok FB s flush
       else if ds_strategy s =? Z_RLE then rle_ok FB s flush
       else if ds_level s <=? 3 then SAFEf s flush else SAFEw s flush)
      /\ BFPOST c0 s flush (run_compress_func s flush).
    Proof.
      intros s flush [H K] Hp Hst0 Hfl.
      assert (PRE : BFPRE c0 s flush) by (split; [exact HC0|]; split; [exact H|]; split; [exact Hp|]; split; [exact Hst0 | exact Hfl]).
      rewrite run_compress_func_dmode.
      pose proof (dmode_range s) as Hm.
      destruct (Z.eq_dec (dmode s) 0) as [E0|E0]; [destruct (Hst c0 s flush PRE E0) as [A B]; rewrite E0; split; [| exact B]; apply dmode_cases; intros; first [exact A | congruence]|].
      destruct (Z.eq_dec (dmode s) 1) as [E1|E1]; [destruct (Hhf c0 s flush PRE E1) as [A B]; rewrite E1; split; [| exact B]; apply dmode_cases; intros; first [exact A | congruence]|].
      destruct (Z.eq_dec (dmode s) 2) as [E2|E2]; [destruct (Hrl c0 s flush PRE E2) as [A B]; rewrite E2; split; [| exact B]; apply dmode_cases; intros; first [exact A | congruence]|].
      destruct (Z.eq_dec (dmode s) 3) as [E3|E3]; [destruct (Hfa c0 s flush PRE E3) as [A B]; rewrite E3; split; [| exact B]; apply dmode_cases; intros; first [exact A | congruence]|].
      assert (E4 : dmode s = 4) by lia.
      destruct (Hsl c0 s flush PRE E4) as [A B]. rewrite E4. split; [| exact B]. apply dmode_cases; intros; first [exact A | congruence].
    Qed.

    (* [comment removed for export] *)
    Lemma blocks_stage : forall s flush, ST s -> ds_pending s = 0 -> 0 <= flush <= 5 ->
      (ds_status s = FINISH_STATE -> cs_avail_in (ds_strm s) = 0) ->
      blocks_ok SAFEs SAFEf SAFEw FB dwf s0 s flush
      /\ let r := deflate_blocks s flush in
         ST (fst r)
         /\ (snd r = None -> ds_pending (fst r) = 0 /\ (flush = Z_FINISH -> ds_status (fst r) = FINISH_STATE)).
    Proof.
      intros s flush HS Hp Hfl Hfin. pose proof HS as [H K]. pose proof H as [[D X] V].
      unfold blocks_ok, deflate_blocks.
      match goal with |- context [if ?c then _ else (s, None)] => destruct c eqn:Hcond end.
      2:{ (* [comment removed for export] *)
          split; [split; [exact (ST_DOK s HS) | intros HH; discriminate HH]|].
          cbn [fst snd]. split; [exact HS|]. intros _. split; [exact Hp|].
          intros Hf. apply orb_false_iff in Hcond as [Hcond C3]. apply orb_false_iff in Hcond as [C1 C2].
          apply andb_false_iff in C3. destruct C3 as [C3|C3].
          - exfalso. rewrite Hf in C3. cbn in C3. discriminate C3.
          - destruct (Z.eqb_spec (ds_status s) FINISH_STATE); [assumption | discriminate C3]. }
      assert (Hst0 : ds_status s <> FINISH_STATE).
      { intros Ef. rewrite (Hfin Ef), (dx_fin _ X Ef), Ef in Hcond. cbn in Hcond.
        rewrite andb_false_r in Hcond. discriminate Hcond. }
      destruct (bf_call s flush HS Hp Hst0 Hfl) as [HSAFE HPOST].
      destruct (run_compress_func s flush) as [s1 bst] eqn:Erun. cbv beta iota zeta.
      unfold BFPOST in HPOST. cbn [fst snd] in HPOST. destruct HPOST as (H1 & K1 & O1 & Pbd & Pfin & Pfd).
      assert (HS1 : ST s1) by (split; [exact H1 | rewrite K1; exact K]).
      pose proof H1 as [[D1 X1] V1].
      set (s2 := if block_state_eqb bst finish_started || block_state_eqb bst finish_done then set_status s1 FINISH_STATE else s1) in *.
      assert (HS2 : ST s2 /\ ds_pending s2 = ds_pending s1 /\ ds_strm s2 = ds_strm s1
                    /\ (block_state_eqb bst finish_started || block_state_eqb bst finish_done = true -> ds_status s2 = FINISH_STATE)
                    /\ (block_state_eqb bst finish_started || block_state_eqb bst finish_done = false -> s2 = s1)).
      { subst s2. destruct (block_state_eqb bst finish_started || block_state_eqb bst finish_done) eqn:Eb.
        - assert (Hl : ds_lookahead s1 = 0).
          { apply Pfin. destruct bst; cbn in Eb; try discriminate Eb; [left | right]; reflexivity. }
          destruct (DC_set_status c0 s1 FINISH_STATE H1 ltac:(unfold FINISH_STATE; lia) ltac:(intros; reflexivity) ltac:(intros _; exact Hl)) as (H2 & K2 & S2).
          split; [split; [exact H2 | rewrite K2, K1; exact K]|].
          split; [reflexivity|]. split; [exact S2|]. split; [intros; reflexivity | intros HH; discriminate HH].
        - split; [exact HS1|]. split; [reflexivity|]. split; [reflexivity|]. split; [intros HH; discriminate HH | intros; reflexivity]. }
      clearbody s2. destruct HS2 as (HS2 & P2 & S2 & Fin2 & NFin2).
      split.
      - (* [comment removed for export] *)
        split; [exact (ST_DOK s HS)|]. intros _.
        split.
        { unfold blocks_call_ok. rewrite Erun. cbn [fst]. split; [| split; [exact (ST_DOK s1 HS1) | exact HSAFE]].
          eapply (lz_keeps_intro c0); [exact D | exact D1 | exact V | exact V1 | exact K1 | exact O1]. }
        split; [exact (ST_DOK s2 HS2)|].
        split.
        { intros _. destruct (cs_avail_out (ds_strm s2) =? 0).
          - apply ST_dpost; [apply ST_set_last_flush; [exact HS2 | lia] | apply Z_OK_range].
          - apply ST_dpost; [exact HS2 | apply Z_OK_range]. }
        intros Ebd. subst bst. destruct (Pbd eq_refl) as (Hp1 & Hnf & Hma1). rewrite (NFin2 eq_refl) in *.
        pose proof HS1 as [H1' _].
        destruct (bdone_facts c0 s1 flush H1 Hp1 Hma1) as (B1 & B2 & B3 & B4 & B5 & R1 & R2).
        assert (HSb : ST (bdone_st s1 flush)) by (split; [exact B1 | rewrite B2, K1; exact K]).
        destruct (ST_flush_pending _ HSb) as (HSf & Hfp & _).
        split.
        { unfold bdone_ok. cbv zeta. pose proof (df_bi _ D1). pose proof (df_pend _ D1). pose proof (dwf_sizes _ D1).
          split; [exact (ST_DOK s1 HS1)|]. split; [unfold BINV; lia|].
          split; [exact R1|]. split; [exact R2|].
          split; [exact (ST_DOK _ HSb)|]. split; [exact Hfp | exact (ST_DOK _ HSf)]. }
        intros _. apply ST_dpost; [apply ST_set_last_flush; [exact HSf | lia] | apply Z_OK_range].
      - (* [comment removed for export] *)
        destruct (block_state_eqb bst need_more || block_state_eqb bst finish_started) eqn:Enm.
        { cbn [fst snd]. split; [| intros HH; discriminate HH].
          destruct (cs_avail_out (ds_strm s2) =? 0); [apply ST_set_last_flush; [exact HS2 | lia] | exact HS2]. }
        destruct (block_state_eqb bst block_done) eqn:Ebd.
        + assert (Eb : bst = block_done) by (destruct bst; cbn in Ebd; try discriminate Ebd; reflexivity). subst bst.
          destruct (Pbd eq_refl) as (Hp1 & Hnf & Hma1). cbn in NFin2. rewrite (NFin2 eq_refl).
          destruct (bdone_facts c0 s1 flush H1 Hp1 Hma1) as (B1 & B2 & B3 & B4 & B5 & R1 & R2).
          assert (HSb : ST (bdone_st s1 flush)) by (split; [exact B1 | rewrite B2, K1; exact K]).
          destruct (ST_flush_pending _ HSb) as (HSf & _ & Hor & _).
          match goal with |- context [flush_pending ?b] => replace b with (bdone_st s1 flush) by (unfold bdone_st; reflexivity) end.
          destruct (Z.eqb_spec (cs_avail_out (ds_strm (flush_pending (bdone_st s1 flush)))) 0) as [Ea|Ea]; cbn [fst snd].
          * split; [apply ST_set_last_flush; [exact HSf | lia] | intros HH; discriminate HH].
          * split; [exact HSf|]. intros _. split; [lia|]. intros Hf. exfalso. exact (Hnf Hf).
        + (* [comment removed for export] *)
          assert (Eb : bst = finish_done) by (destruct bst; cbn in Enm, Ebd; try discriminate Enm; try discriminate Ebd; reflexivity). subst bst.
          cbn [fst snd]. split; [exact HS2|]. intros _. split; [rewrite P2; exact (Pfd eq_refl)|].
          intros _. apply Fin2. reflexivity.
    Qed.

    (* [comment removed for export] *)
    Lemma finish_stage : forall s flush, ST s -> ds_pending s = 0 -> 0 <= flush <= 5 ->
      (flush = Z_FINISH -> ds_status s = FINISH_STATE) ->
      finish_ok dwf s0 s flush
      /\ (flush = Z_FINISH -> 0 < ds_wrap s -> ST (fst (deflate_trailer s))).
    Proof.
      intros s flush HS Hp Hfl Hfin. pose proof HS as [H K]. pose proof H as [[D X] V]. pose proof (dwf_sizes s D) as (_ & _ & Sl & _).
      destruct (trailer_facts c0 s H Hp) as ((H1 & Po1 & P1) & K1 & O1 & St1 & Wr1 & Lk1).
      assert (HS1 : ST (trailer_st s)) by (split; [exact H1 | rewrite K1; exact K]).
      destruct (ST_flush_pending _ HS1) as (HS2 & Hfp & Hor & Hp2 & St2 & Wr2 & Lk2 & Ai2).
      pose proof HS2 as [[[D2 X2] V2] K2].
      assert (HS3 : flush = Z_FINISH -> ST (set_wrap (flush_pending (trailer_st s)) (- ds_wrap (flush_pending (trailer_st s))))).
      { intros Hf. pose proof HS2 as [H2 _].
        destruct (DC_set_wrap_neg c0 _ (- ds_wrap (flush_pending (trailer_st s))) H2
                    ltac:(pose proof (df_wrap _ D2); lia) ltac:(rewrite St2, St1; exact (Hfin Hf))) as (H3 & K3 & _).
        split; [exact H3 | rewrite K3; exact K2]. }
      split.
      - unfold finish_ok. split; [exact (ST_DOK s HS)|].
        split; [intros _; apply ST_dpost; [exact HS | apply Z_OK_range]|].
        split; [intros _ _; apply ST_dpost; [exact HS | apply Z_STREAM_END_range]|].
        intros Hf Hw. unfold trailer_ok. cbv zeta.
        split; [exact (ST_DOK s HS)|]. split; [exact Hw|].
        split; [destruct (ds_wrap s =? 2); lia|].
        split; [exact (ST_DOK _ HS1)|]. split; [exact Hfp|].
        split; [exact (ST_DOK _ HS2)|]. split; [pose proof (df_pend _ D2); pose proof (dwf_sizes _ D2); lia|].
        split; [rewrite Wr2, Wr1; exact Hw|].
        apply ST_dpost; [exact (HS3 Hf)|]. destruct (negb _); [apply Z_OK_range | apply Z_STREAM_END_range].
      - intros Hf Hw. rewrite deflate_trailer_eq. cbv zeta.
        replace (0 <? ds_wrap (flush_pending (trailer_st s))) with true by (symmetry; apply Z.ltb_lt; rewrite Wr2, Wr1; exact Hw).
        cbn [fst]. exact (HS3 Hf).
    Qed.

    (* [comment removed for export] *)

    (* [comment removed for export] *)
    Lemma core_result : forall flush, ST s0 -> 0 <= flush < 16 -> ST (fst (deflate_core s0 flush)).
    Proof.
      intros flush HS0 Hfl. pose proof HS0 as [H K]. pose proof H as [[D X] V].
      unfold deflate_core.
      destruct (deflateStateCheck s0 || (Z_BLOCK <? flush) || (flush <? 0)) eqn:Echk; [cbn [fst]; exact HS0|].
      apply orb_false_iff in Echk as [Echk C3]. apply orb_false_iff in Echk as [C1 C2].
      apply Z.ltb_ge in C2. apply Z.ltb_ge in C3. unfold Z_BLOCK in C2.
      destruct ((ds_status s0 =? FINISH_STATE) && negb (flush =? Z_FINISH)); [apply ST_err_return; exact HS0|].
      destruct (cs_avail_out (ds_strm s0) =? 0); [apply ST_err_return; exact HS0|].
      cbv zeta.
      pose proof (ST_set_last_flush s0 flush HS0 ltac:(lia)) as HS1.
      set (s1 := set_last_flush s0 flush) in *.
      match goal with |- ST (fst (let '(s, r) := ?head in _)) => destruct head as [s2 r2] eqn:Ehead end.
      assert (H2 : ST s2 /\ (r2 = None -> ds_pending s2 = 0)).
      { destruct (negb (ds_pending s1 =? 0)) eqn:Ep.
        - destruct (ST_flush_pending s1 HS1) as (HSf & _ & Hor & _).
          destruct (Z.eqb_spec (cs_avail_out (ds_strm (flush_pending s1))) 0) as [Ea|Ea]; inversion Ehead; subst.
          + split; [apply ST_set_last_flush; [exact HSf | lia] | intros HH; discriminate HH].
          + split; [exact HSf | intros _; lia].
        - destruct ((cs_avail_in (ds_strm s1) =? 0) && (RANK flush <=? RANK (ds_last_flush s0)) && negb (flush =? Z_FINISH)).
          + unfold err_return in Ehead. inversion Ehead; subst. split; [| intros HH; discriminate HH].
            exact (ST_err_return s1 Z_BUF_ERROR HS1).
          + inversion Ehead; subst. split; [exact HS1|]. intros _. destruct (Z.eqb_spec (ds_pending s1) 0); [assumption | discriminate Ep]. }
      clear Ehead. destruct H2 as [HS2 Hp2].
      destruct r2 as [rc|]; [cbn [fst]; exact HS2|]. specialize (Hp2 eq_refl).
      destruct ((ds_status s2 =? FINISH_STATE) && negb (cs_avail_in (ds_strm s2) =? 0)) eqn:Efa; [apply ST_err_return; exact HS2|].
      set (s4 := if (ds_status s2 =? INIT_STATE) && (ds_wrap s2 =? 0) then set_status s2 BUSY_STATE else s2).
      assert (HS4 : ST s4 /\ ds_pending s4 = 0 /\ cs_avail_in (ds_strm s4) = cs_avail_in (ds_strm s2)
                    /\ (ds_status s4 = FINISH_STATE -> ds_status s2 = FINISH_STATE)).
      { subst s4. destruct ((ds_status s2 =? INIT_STATE) && (ds_wrap s2 =? 0)) eqn:E.
        - apply andb_prop in E as [E1 E2]. apply Z.eqb_eq in E1. apply Z.eqb_eq in E2. pose proof HS2 as [H2' _].
          destruct (DC_set_status c0 s2 BUSY_STATE H2' ltac:(unfold BUSY_STATE; lia) ltac:(intros; exfalso; lia) ltac:(unfold BUSY_STATE, FINISH_STATE; intros; lia)) as (H4 & K4 & S4).
          split; [split; [exact H4 | rewrite K4; exact (proj2 HS2)]|]. unfold set_status; dsred. split; [exact Hp2|]. split; [reflexivity|].
          unfold BUSY_STATE, FINISH_STATE. intros; lia.
        - split; [exact HS2|]. split; [exact Hp2|]. split; [reflexivity | intros E'; exact E']. }
      clearbody s4. destruct HS4 as (HS4 & Hp4 & Ai4 & Fin4).
      rewrite deflate_zlib_header_eq.
      match goal with |- ST (fst (let '(s, r) := ?head in _)) => destruct head as [s5 r5] eqn:Ehead end.
      assert (H5 : ST s5 /\ (r5 = None -> ds_pending s5 = 0 /\ cs_avail_in (ds_strm s5) = cs_avail_in (ds_strm s2)
                                          /\ (ds_status s5 = FINISH_STATE -> ds_status s2 = FINISH_STATE))).
      { destruct (Z.eqb_spec (ds_status s4) INIT_STATE) as [E|E].
        - destruct (hdr_zlib s4 HS4 Hp4 E) as (_ & HSz & Stz & Horz & Aiz & _).
          cbv zeta in Ehead. destruct (negb (ds_pending (flush_pending (zhdr_st s4)) =? 0)) eqn:Ep; inversion Ehead; subst.
          + split; [apply ST_set_last_flush; [exact HSz | lia] | intros HH; discriminate HH].
          + split; [exact HSz|]. intros _. rewrite Aiz, Stz. split; [destruct (Z.eqb_spec (ds_pending (flush_pending (zhdr_st s4))) 0); [assumption | discriminate Ep]|].
            split; [exact Ai4 | unfold BUSY_STATE, FINISH_STATE; intros; lia].
        - inversion Ehead; subst. split; [exact HS4|]. intros _. split; [exact Hp4|]. split; [exact Ai4 | exact Fin4]. }
      clear Ehead. destruct H5 as [HS5 Hr5].
      destruct r5 as [rc|]; [cbn [fst]; exact HS5|]. destruct (Hr5 eq_refl) as (Hp5 & Ai5 & Fin5).
      rewrite deflate_gzip_header_eq.
      match goal with |- ST (fst (let '(s, r) := ?head in _)) => destruct head as [s6 r6] eqn:Ehead end.
      assert (H6 : ST s6 /\ (r6 = None -> ds_pending s6 = 0 /\ cs_avail_in (ds_strm s6) = cs_avail_in (ds_strm s2)
                                          /\ (ds_status s6 = FINISH_STATE -> ds_status s2 = FINISH_STATE))).
      { destruct (Z.eqb_spec (ds_status s5) GZIP_STATE) as [E|E].
        - destruct (hdr_gzip s5 HS5 Hp5 E) as (_ & HSz & Stz & Horz & Aiz & _).
          cbv zeta in Ehead. destruct (negb (ds_pending (flush_pending (gzhdr_st s5)) =? 0)) eqn:Ep; inversion Ehead; subst.
          + split; [apply ST_set_last_flush; [exact HSz | lia] | intros HH; discriminate HH].
          + split; [exact HSz|]. intros _. rewrite Aiz, Stz. split; [destruct (Z.eqb_spec (ds_pending (flush_pending (gzhdr_st s5))) 0); [assumption | discriminate Ep]|].
            split; [exact Ai5 | unfold BUSY_STATE, FINISH_STATE; intros; lia].
        - inversion Ehead; subst. split; [exact HS5|]. intros _. split; [exact Hp5|]. split; [exact Ai5 | exact Fin5]. }
      clear Ehead. destruct H6 as [HS6 Hr6].
      destruct r6 as [rc|]; [cbn [fst]; exact HS6|]. destruct (Hr6 eq_refl) as (Hp6 & Ai6 & Fin6).
      assert (Hfin6 : ds_status s6 = FINISH_STATE -> cs_avail_in (ds_strm s6) = 0).
      { intros E. rewrite Ai6. pose proof (Fin6 E) as E2. rewrite E2 in Efa. cbn in Efa.
        destruct (Z.eqb_spec (cs_avail_in (ds_strm s2)) 0); [assumption | discriminate Efa]. }
      destruct (blocks_stage s6 flush HS6 Hp6 ltac:(lia) Hfin6) as (_ & HSr & Hr).
      destruct (deflate_blocks s6 flush) as [s7 r7]. cbn [fst snd] in HSr, Hr.
      destruct r7 as [rc|]; [cbn [fst]; exact HSr|]. destruct (Hr eq_refl) as [Hp7 Hfin7].
      destruct (negb (flush =? Z_FINISH)) eqn:Ef; [cbn [fst]; exact HSr|].
      assert (Hf : flush = Z_FINISH) by (destruct (Z.eqb_spec flush Z_FINISH); [assumption | discriminate Ef]).
      destruct (Z.leb_spec (ds_wrap s7) 0); [cbn [fst]; exact HSr|].
      exact (proj2 (finish_stage s7 flush HSr Hp7 ltac:(lia) Hfin7) Hf ltac:(lia)).
    Qed.

  End Call.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Theorem deflate_m_DD : forall ds zc flush, DD ds -> dcall_wf zc -> 0 <= flush < 16 -> DD (fst (deflate_m ds zc flush)).
  Proof.
    intros ds zc flush HDD Hzc Hfl.
    set (c0 := cstrm_of_call zc). set (s0 := set_strm ds c0).
    pose proof (C0OK'_of_call zc Hzc) as HC0. fold c0 in HC0.
    assert (H0 : DC c0 s0) by (split; [apply DD_set_strm; exact HDD | subst s0 c0; apply SV_entry; exact Hzc]).
    pose proof H0 as [[D0 X0] V0].
    assert (HS0 : ST c0 s0 s0) by (split; [exact H0 | reflexivity]).
    unfold deflate_m. fold c0 s0.
    pose proof (core_result c0 s0 HC0 eq_refl D0 flush HS0 Hfl) as [[HDD' _] _].
    destruct (deflate_core s0 flush) as [s' rc]. cbn [fst] in HDD' |- *. exact HDD'.
  Qed.

End Integrate.
