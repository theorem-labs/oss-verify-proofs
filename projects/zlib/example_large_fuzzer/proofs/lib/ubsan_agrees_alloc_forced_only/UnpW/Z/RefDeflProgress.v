(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import TrSmallModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import FlushBlockModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import Trees.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateBlk.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import Deflate.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateSafe.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflateRel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflFastM.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflFast6.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflSlow6.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflStored4.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflStored2.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflStored5.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflStored6.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflStored7.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflSafeF.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflSafeFB.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflSafeI1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflSafeI2.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflSafeI3.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflSafeI4.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflSafeL0.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflSafeL2.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflSafeL3.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflSafeL4.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflSafeL5.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflSafeI6.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeE1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateTaintRel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateTaintBits.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import DeflateTaintTrees.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefCompress2Spec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition HF (flush : Z) (s : deflate_state) : Prop :=
  flush = Z_FINISH \/ (flush = Z_NO_FLUSH /\ 0 < cs_avail_in (ds_strm s)).

(* [comment removed for export] *)
Definition BPOST (flush : Z) (s : deflate_state) (r : deflate_state * block_state) : Prop :=
  snd r <> block_done
  /\ (snd r = finish_done -> flush = Z_FINISH)
  /\ (snd r = need_more \/ snd r = finish_started ->
      cs_avail_out (ds_strm (fst r)) = 0
      \/ cs_avail_in (ds_strm (fst r)) < cs_avail_in (ds_strm s)
      \/ cs_avail_out (ds_strm (fst r)) < cs_avail_out (ds_strm s)).

(* [comment removed for export] *)
Definition LPROG (flush : Z) (s' : deflate_state) : Prop :=
  cs_avail_out (ds_strm s') = 0 \/ (flush = Z_NO_FLUSH /\ cs_avail_in (ds_strm s') = 0).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma st_fill_prog : forall c0 s flush, C0OK c0 -> DC c0 s -> dmode s <> 0 -> ds_status s <> FINISH_STATE ->
  match snd (st_fill s flush) with
  | Some (LRet _) => LPROG flush (fst (st_fill s flush))
  | Some LBreak => flush <> Z_NO_FLUSH
  | _ => True
  end.
Proof.
  intros c0 s flush HC0 HDC Hm Hst. unfold st_fill.
  destruct (Z.ltb_spec (ds_lookahead s) MIN_LOOKAHEAD) as [Hlt|Hge]; [| cbn [snd]; exact I].
  pose proof (DC_fill_window c0 s HC0 HDC Hm Hst Hlt) as FW. cbv zeta in FW.
  destruct FW as (_ & _ & _ & _ & _ & _ & HX & _).
  destruct (Z.ltb_spec (ds_lookahead (fill_window s)) MIN_LOOKAHEAD) as [L1|L1].
  - destruct (Z.eqb_spec flush Z_NO_FLUSH) as [F|F]; cbn [andb fst snd].
    + right. split; [exact F | exact (proj1 (HX L1))].
    + destruct (ds_lookahead (fill_window s) =? 0); cbn [fst snd]; [exact F | exact I].
  - cbn [andb]. destruct (Z.eqb_spec (ds_lookahead (fill_window s)) 0) as [E0|E0]; cbn [fst snd]; [| exact I].
    exfalso. unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in L1. lia.
Qed.

(* [comment removed for export] *)
Lemma st_bflush_prog : forall flush s b,
  match snd (st_bflush s b) with
  | LRet _ => LPROG flush (fst (st_bflush s b))
  | LBreak => False
  | LCont => True
  end.
Proof.
  intros flush s b. unfold st_bflush. destruct b; [| cbn [snd]; exact I].
  unfold flush_block.
  destruct (Z.eqb_spec (cs_avail_out (ds_strm (flush_block_only s 0))) 0) as [A|A]; cbn [fst snd]; [left; exact A | exact I].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section FastP.
  Variable c0 : cstrm.
Variable s0 : deflate_state.
Variable flush : Z.
  Hypothesis HC0 : C0OK' c0.
  Let HC0w : C0OK c0 := c0'_ok _ HC0.
  Local Notation FTI := (RefDeflSafeL2.FTI c0 s0).

  Lemma st_body_prog : forall s, FTI s ->
    match snd (st_body s flush) with
    | LRet _ => LPROG flush (fst (st_body s flush))
    | LBreak => flush <> Z_NO_FLUSH
    | LCont => True
    end.
  Proof.
    intros s HF. pose proof HF as (HDC & HK & Hp & Hm & Hst & Ho).
    pose proof (st_fill_prog c0 s flush HC0w HDC ltac:(rewrite Hm; lia) Hst) as P.
    unfold st_body. destruct (st_fill s flush) as [s1 [o|]]; cbn [fst snd] in P |- *.
    - destruct o; cbn [fst snd]; exact P.
    - destruct (st_hash s1) as [s2 hh]. destruct (st_tally (st_match s2 hh)) as [s7 bf].
      pose proof (st_bflush_prog flush s7 bf) as Q. destruct (snd (st_bflush s7 bf)); [exact Q | destruct Q | exact Q].
  Qed.

  Lemma fast_loop_prog : forall fuel s, FTI s -> lz_meas s < Z.of_nat fuel ->
    match snd (deflate_fast_loop fuel s flush) with
    | Some _ => LPROG flush (fst (deflate_fast_loop fuel s flush))
    | None => flush <> Z_NO_FLUSH
    end.
  Proof.
    induction fuel as [|f IH]; intros s HI Hmz.
    { exfalso. pose proof (FTI_facts c0 s0 s HI) as (D & _ & V & _). pose proof (sv_ain _ _ V). pose proof (df_look _ D).
      unfold lz_meas in Hmz. cbn [Z.of_nat] in Hmz. lia. }
    rewrite loop_step. pose proof (fast_step c0 s0 flush HC0 FB_CALL_ok s HI) as [_ HC]. pose proof (st_body_prog s HI) as P.
    destruct (snd (st_body s flush)).
    - destruct HC as [HI' Hm']. exact (IH _ HI' ltac:(lia)).
    - cbn [fst snd]. exact P.
    - cbn [fst snd]. exact P.
  Qed.
End FastP.

Lemma deflate_tail_finish : forall s r, deflate_tail s Z_FINISH = r ->
  (snd r = finish_started /\ cs_avail_out (ds_strm (fst r)) = 0) \/ snd r = finish_done.
Proof.
  intros s r <-. unfold deflate_tail. change (Z_FINISH =? Z_FINISH) with true. cbv beta iota.
  unfold flush_block. change (negb (1 =? 0)) with true. cbv beta iota.
  destruct (Z.eqb_spec (cs_avail_out (ds_strm (flush_block_only s 1))) 0) as [A|A]; cbn [fst snd].
  - left. split; [reflexivity | exact A].
  - right. reflexivity.
Qed.

Lemma BPOST_of_tail : forall flush s s1, flush = Z_FINISH -> BPOST flush s (deflate_tail s1 flush).
Proof.
  intros flush s s1 ->.
  destruct (deflate_tail_finish s1 _ eq_refl) as [[E A]|E]; unfold BPOST; rewrite E.
  - split; [intros X; discriminate X|]. split; [intros X; discriminate X|]. intros _. left. exact A.
  - split; [intros X; discriminate X|]. split; [intros _; reflexivity|]. intros [X|X]; discriminate X.
Qed.

Lemma BPOST_of_LPROG : forall flush s s' bs, HF flush s -> LPROG flush s' -> bs = need_more ->
  BPOST flush s (s', bs).
Proof.
  intros flush s s' bs HH LP ->. unfold BPOST; cbn [fst snd].
  split; [intros X; discriminate X|]. split; [intros X; discriminate X|]. intros _.
  destruct LP as [A|[F A]]; [left; exact A|]. right; left.
  destruct HH as [F'|[_ Hai]]; [exfalso; rewrite F in F'; discriminate F'|]. rewrite A. exact Hai.
Qed.

Lemma deflate_fast_prog : forall c0 s flush, C0OK' c0 -> RefDeflSafeL2.FTI c0 s s -> HF flush s ->
  BPOST flush s (deflate_fast s flush).
Proof.
  intros c0 s flush HC0 HF HH. pose proof HF as (HDC & _). pose proof HDC as [[D X] V].
  assert (Hmz : 0 <= lz_meas s) by (unfold lz_meas; pose proof (df_look _ D); pose proof (sv_ain _ _ V); lia).
  pose proof (fast_loop_prog c0 s flush HC0 (lz_fuel s) s HF (lz_fuel_meas s Hmz)) as LP.
  pose proof (fast_loop c0 s flush HC0 FB_CALL_ok (lz_fuel s) s HF (lz_fuel_meas s Hmz)) as [_ LR].
  unfold deflate_fast. destruct (deflate_fast_loop (lz_fuel s) s flush) as [s' [bs|]]; cbn [fst snd] in LP, LR.
  - destruct LR as (_ & _ & _ & E). exact (BPOST_of_LPROG flush s s' bs HH LP E).
  - apply BPOST_of_tail. destruct HH as [F|[F _]]; [exact F | exfalso; exact (LP F)].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section SlowP.
  Variable c0 : cstrm.
Variable s0 : deflate_state.
Variable flush : Z.
  Hypothesis HC0 : C0OK' c0.
  Let HC0w : C0OK c0 := c0'_ok _ HC0.
  Local Notation STI := (RefDeflSafeL5.STI c0 s0).

  Lemma st_sbody_prog : forall s, STI s ->
    match snd (st_sbody s flush) with
    | LRet _ => LPROG flush (fst (st_sbody s flush))
    | LBreak => flush <> Z_NO_FLUSH
    | LCont => True
    end.
  Proof.
    intros s HS. pose proof HS as (HDC & HK & Hp & Hm & Hst & Ho).
    pose proof (st_fill_prog c0 s flush HC0w HDC ltac:(rewrite Hm; lia) Hst) as P.
    unfold st_sbody. destruct (snd (st_fill s flush)) as [o|].
    - destruct o; cbn [fst snd]; exact P.
    - unfold st_srest.
      match goal with |- context [st_decide ?x] => set (s4 := x) end. clearbody s4. unfold st_decide.
      destruct (dist_cond s4).
      + pose proof (st_bflush_prog flush (fst (st_sdist s4)) (snd (st_sdist s4))) as Q.
        destruct (snd (st_bflush (fst (st_sdist s4)) (snd (st_sdist s4)))); [exact Q | destruct Q | exact Q].
      + destruct (negb (ds_match_available s4 =? 0)).
        * unfold st_slit. destruct (tr_tally_lit s4 (arr_get (ds_window s4) (ds_strstart s4 - 1))) as [s1 b]. cbv zeta.
          match goal with |- context [(_, if ?c then LRet need_more else LCont)] => destruct c eqn:A end; cbn [fst snd]; [| exact I].
          left. apply Z.eqb_eq in A. exact A.
        * unfold st_avail. cbn [snd]. exact I.
  Qed.

  Lemma slow_loop_prog : forall fuel s, STI s -> lz_meas s < Z.of_nat fuel ->
    match snd (deflate_slow_loop fuel s flush) with
    | Some _ => LPROG flush (fst (deflate_slow_loop fuel s flush))
    | None => flush <> Z_NO_FLUSH
    end.
  Proof.
    induction fuel as [|f IH]; intros s HI Hmz.
    { exfalso. pose proof (STI_facts c0 s0 s HI) as (D & _ & V & _). pose proof (sv_ain _ _ V). pose proof (df_look _ D).
      unfold lz_meas in Hmz. cbn [Z.of_nat] in Hmz. lia. }
    rewrite sloop_step'. pose proof (sstep c0 s0 flush HC0 FB_CALL_ok s HI) as [_ HC]. pose proof (st_sbody_prog s HI) as P.
    destruct (snd (st_sbody s flush)).
    - destruct HC as [HI' Hm']. exact (IH _ HI' ltac:(lia)).
    - cbn [fst snd]. exact P.
    - cbn [fst snd]. exact P.
  Qed.
End SlowP.

Lemma deflate_slow_prog : forall c0 s flush, C0OK' c0 -> RefDeflSafeL5.STI c0 s s -> HF flush s ->
  BPOST flush s (deflate_slow s flush).
Proof.
  intros c0 s flush HC0 HS HH. pose proof HS as (HDC & _). pose proof HDC as [[D X] V].
  assert (Hmz : 0 <= lz_meas s) by (unfold lz_meas; pose proof (df_look _ D); pose proof (sv_ain _ _ V); lia).
  pose proof (slow_loop_prog c0 s flush HC0 (lz_fuel s) s HS (lz_fuel_meas s Hmz)) as LP.
  pose proof (sloop c0 s flush HC0 FB_CALL_ok (lz_fuel s) s HS (lz_fuel_meas s Hmz)) as [_ LR].
  rewrite deflate_slow_eq. destruct (snd (deflate_slow_loop (lz_fuel s) s flush)) as [bs|]; cbn [fst snd] in LP, LR.
  - destruct LR as (_ & _ & _ & E). exact (BPOST_of_LPROG flush s _ bs HH LP E).
  - cbv zeta. apply BPOST_of_tail. destruct HH as [F|[F _]]; [exact F | exfalso; exact (LP F)].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma MIN_le_l : forall a b, MIN a b <= a.
Proof. intros a b. unfold MIN. destruct (Z.ltb_spec b a); lia. Qed.
Lemma MIN_le_r : forall a b, MIN a b <= b.
Proof. intros a b. unfold MIN. destruct (Z.ltb_spec b a); lia. Qed.
Lemma MIN_nonneg : forall a b, 0 <= a -> 0 <= b -> 0 <= MIN a b.
Proof. intros a b Ha Hb. unfold MIN. destruct (Z.ltb_spec b a); lia. Qed.

(* [comment removed for export] *)
Lemma flush_pending_avail : forall s, 0 <= cs_avail_out (ds_strm s) -> 0 <= ds_pending s -> ds_pending s + 2 < 2 ^ 32 ->
  cs_avail_in (ds_strm (flush_pending s)) = cs_avail_in (ds_strm s)
  /\ cs_avail_out (ds_strm (flush_pending s)) <= cs_avail_out (ds_strm s)
  /\ (0 < ds_pending s -> 0 < cs_avail_out (ds_strm s) -> cs_avail_out (ds_strm (flush_pending s)) < cs_avail_out (ds_strm s)).
Proof.
  intros s A0 P0 P32.
  pose proof (flush_pending_shape s A0 P0 P32) as SH. cbv zeta in SH. destruct SH as (po & st & E & _ & _ & Eai & Eao & _ & Hlen & _).
  pose proof (bi_flush_pending_le s) as BL.
  rewrite E. unfold set_pending_out, set_pending, set_strm. cbn [ds_strm]. rewrite Eai, Eao.
  split; [reflexivity|]. split; [lia|]. intros Hp Ha. lia.
Qed.

Section StoredP.
  Variable c0 : cstrm.
Variable s0 : deflate_state.
Variable flush : Z.
  Hypothesis HC0 : C0OK' c0.
  Let HC0w : C0OK c0 := c0'_ok _ HC0.
  Local Notation SI := (RefDeflSafeL0.SI c0 s0).

  (* [comment removed for export] *)
  Lemma trip_prog : forall t mb, SI t -> sb_broke t flush mb = false ->
    let t' := st_trip t flush in
    SI t' /\ cs_avail_in (ds_strm t') <= cs_avail_in (ds_strm t) /\ cs_avail_out (ds_strm t') < cs_avail_out (ds_strm t).
  Proof.
    intros t mb HS Hb t'. subst t'. pose proof HS as (HDC & HK & Hm & Hst & Ho & Hp).
    pose proof (SI_facts c0 s0 HC0 t HS) as (D & X & V & Sw & Sl & Epbs & Hl0 & Hbs & Hsn & Hmt & Hstr & Ewsz & Hwr & Hpo & Hbv & Hbb & Hao & Hai & Hins & Hinsw & Hhw).
    unfold sb_broke in Hb. apply Bool.orb_false_iff in Hb. destruct Hb as [Hb _]. apply Z.ltb_ge in Hb.
    pose proof (sb_len_range t ltac:(clear - Hai; lia) Hb) as (Rl1 & Rl2 & Rl3).
    pose proof (sb_len1_eq t ltac:(clear - Hai; lia)) as (_ & _ & Rl4).
    pose proof (sb_hdr_eq t ltac:(clear - Hbv; lia)) as [Ehdr Hh5].
    assert (Eleft : sb_left t = ds_strstart t - ds_block_start t) by (unfold sb_left; apply wrap32_id; clear - Hbs Hstr Sw; lia).
    unfold st_trip.
    pose proof (emit_stage c0 s0 flush HC0 t HS Hb) as E. cbv zeta in E. destruct E as (HS3 & ESF3 & ELZ3 & Ebs3 & Eao3 & Eai3 & Eni3 & Ein3).
    pose proof (LZS_fields _ _ ELZ3) as (Ew3 & Estr3 & _).
    set (t3 := st_emit1 t flush) in *. clearbody t3.
    unfold st_copy. rewrite Eleft in Rl4 |- *.
    destruct (Z.eqb_spec (ds_strstart t - ds_block_start t) 0) as [L0|L0]; cbn [negb fst snd].
    - destruct (Z.eq_dec (sb_len t) 0) as [N0|N0].
      + rewrite N0. unfold st_rdo. cbn [negb Z.eqb]. split; [exact HS3|]. rewrite Eai3, Eao3, Ehdr. clear - Hh5. lia.
      + pose proof (rdo_stage c0 s0 HC0 t3 (sb_len t) HS3 ltac:(rewrite Eai3; clear - Rl1 Rl3 Rl4 L0 N0; lia) ltac:(rewrite Eao3; exact Rl2)) as R. cbv zeta in R.
        destruct R as (HS5 & _ & _ & _ & Eao5 & Eai5 & _).
        split; [exact HS5|]. rewrite Eai5, Eao5, Eai3, Eao3, Ehdr. clear - Rl1 Hh5. lia.
    - set (l := lc_len (ds_strstart t - ds_block_start t) (sb_len t)).
      assert (Hl : 0 <= l <= sb_len t /\ l <= ds_strstart t - ds_block_start t /\ sb_len t - l <= cs_avail_in (ds_strm t)).
      { subst l. unfold lc_len. destruct (Z.ltb_spec (sb_len t) (ds_strstart t - ds_block_start t)) as [l0|l0]; clear - l0 Rl1 Rl3 Rl4 Hbs Hai; lia. }
      pose proof (lcopy_stage c0 s0 HC0 t3 l HS3 ltac:(clear - Hl; lia) ltac:(rewrite Ebs3, Estr3; clear - Hl; lia) ltac:(rewrite Eao3; clear - Hl Rl2; lia)) as C. cbv zeta in C.
      destruct C as (HS4 & _ & _ & _ & Eao4 & Eai4 & _).
      set (t4 := st_lcopy t3 l) in *. clearbody t4.
      destruct (Z.eq_dec (sb_len t - l) 0) as [N0|N0].
      + rewrite N0. unfold st_rdo. cbn [negb Z.eqb]. split; [exact HS4|]. rewrite Eai4, Eao4, Eai3, Eao3, Ehdr. clear - Hh5 Hl. lia.
      + pose proof (rdo_stage c0 s0 HC0 t4 (sb_len t - l) HS4 ltac:(rewrite Eai4, Eai3; clear - Hl N0; lia) ltac:(rewrite Eao4, Eao3; clear - Hl Rl2; lia)) as R. cbv zeta in R.
        destruct R as (HS5 & _ & _ & _ & Eao5 & Eai5 & _).
        split; [exact HS5|]. rewrite Eai5, Eao5, Eai4, Eao4, Eai3, Eao3, Ehdr. clear - Hl Hh5 Rl1. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma loop_prog : forall fuel t mb, SI t ->
    let r := deflate_stored_loop fuel t flush mb in
    SI (fst r) /\ cs_avail_in (ds_strm (fst r)) <= cs_avail_in (ds_strm t) /\ cs_avail_out (ds_strm (fst r)) <= cs_avail_out (ds_strm t).
  Proof.
    induction fuel as [|f IH]; intros t mb HS r; subst r.
    - cbn [deflate_stored_loop fst]. split; [exact HS | lia].
    - rewrite sloop_S'. destruct (sb_broke t flush mb) eqn:Hb; [cbn [fst]; split; [exact HS | lia]|].
      pose proof (trip_prog t mb HS Hb) as T. cbv zeta in T. destruct T as (HS1 & Hai1 & Hao1).
      destruct (sb_lastv t flush =? 0).
      + pose proof (IH (st_trip t flush) mb HS1) as T. cbv zeta in T. destruct T as (HS2 & Hai2 & Hao2). split; [exact HS2 | lia].
      + cbn [fst]. split; [exact HS1 | lia].
  Qed.

  (* [comment removed for export] *)
  Lemma loop_last : forall fuel t mb, flush <> Z_FINISH -> snd (deflate_stored_loop fuel t flush mb) = 0.
  Proof.
    induction fuel as [|f IH]; intros t mb Hnf.
    - reflexivity.
    - rewrite sloop_S'. destruct (sb_broke t flush mb); [reflexivity|].
      rewrite (sb_lastv_nf t flush Hnf). cbn [Z.eqb]. apply IH. exact Hnf.
  Qed.

  (* [comment removed for export] *)
  Lemma loop_facts : forall f t mb, SI t ->
    let r := deflate_stored_loop (S f) t flush mb in
    SI (fst r) /\ cs_avail_in (ds_strm (fst r)) <= cs_avail_in (ds_strm t)
    /\ (cs_avail_out (ds_strm (fst r)) < cs_avail_out (ds_strm t) \/ (fst r = t /\ snd r = 0))
    /\ (snd r <> 0 -> flush = Z_FINISH).
  Proof.
    intros f t mb HS r. subst r. rewrite sloop_S'.
    destruct (sb_broke t flush mb) eqn:Hb.
    - cbn [fst snd]. split; [exact HS|]. split; [lia|]. split; [right; split; reflexivity|]. intros X. exfalso. exact (X eq_refl).
    - pose proof (trip_prog t mb HS Hb) as T. cbv zeta in T. destruct T as (HS1 & Hai1 & Hao1).
      destruct (Z.eqb_spec (sb_lastv t flush) 0) as [El|El].
      + pose proof (loop_prog f (st_trip t flush) mb HS1) as T. cbv zeta in T. destruct T as (HS2 & Hai2 & Hao2).
        split; [exact HS2|]. split; [lia|]. split; [left; lia|].
        intros Hl. destruct (Z.eq_dec flush Z_FINISH) as [F|F]; [exact F|]. exfalso. apply Hl. apply loop_last. exact F.
      + cbn [fst snd]. split; [exact HS1|]. split; [lia|]. split; [left; lia|].
        intros _. destruct (Z.eq_dec flush Z_FINISH) as [F|F]; [exact F|]. exfalso. apply El. apply sb_lastv_nf. exact F.
  Qed.

  (* [comment removed for export] *)
  Lemma slide3_bs : forall t have,
    let r := st_slide3 t have in
    (fst r = t /\ snd r = have /\ ((have <? cs_avail_in (ds_strm t)) && (ds_w_size t <=? ds_block_start t)) = false)
    \/ (ds_block_start (fst r) = ds_block_start t - ds_w_size t /\ ((have <? cs_avail_in (ds_strm t)) && (ds_w_size t <=? ds_block_start t)) = true).
  Proof.
    intros t have r. subst r. unfold st_slide3.
    destruct ((have <? cs_avail_in (ds_strm t)) && (ds_w_size t <=? ds_block_start t)) eqn:C.
    - right. split; [| reflexivity]. cbv zeta. cbn [fst]. dsred.
      destruct (ds_matches t <? 2); dsred; destruct (ds_strstart t - ds_w_size t <? ds_insert t); dsred; reflexivity.
    - left. cbn [fst snd]. repeat split; reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma final_prog : forall t, SI t ->
    let r := st_final t flush in
    cs_avail_in (ds_strm (fst r)) = cs_avail_in (ds_strm t)
    /\ cs_avail_out (ds_strm (fst r)) <= cs_avail_out (ds_strm t)
    /\ ((t_mb t <= ds_strstart t - ds_block_start t \/ (flush = Z_FINISH /\ cs_avail_in (ds_strm t) = 0)) ->
        0 < cs_avail_out (ds_strm t) -> cs_avail_out (ds_strm (fst r)) < cs_avail_out (ds_strm t))
    /\ (snd r = finish_started \/ snd r = need_more).
  Proof.
    intros t HS r. subst r. pose proof HS as (HDC & HK & Hm & Hst & Ho & Hp).
    pose proof (SI_facts c0 s0 HC0 t HS) as (D & X & V & Sw & Sl & Epbs & Hl0 & Hbs & Hsn & Hmt & Hstr & Ewsz & Hwr & Hpo & Hbv & Hbb & Hao & Hai & Hins & Hinsw & Hhw).
    unfold st_final. cbv zeta.
    assert (Hleft : wrap32 (ds_strstart t - ds_block_start t) = ds_strstart t - ds_block_start t) by (apply wrap32_id; clear - Hbs Hstr Sw; lia).
    rewrite Hleft.
    pose proof (t_have_eq t ltac:(clear - Hbv; lia) ltac:(rewrite Epbs; clear - Sl; lia)) as (Eh & Rh & Rhdr).
    assert (Hmb : t_mb t <= t_have t /\ t_mb t <= ds_w_size t) by (unfold t_mb; split; [apply MIN_le_l | apply MIN_le_r]).
    match goal with |- context [if ?c then _ else (t, need_more)] => destruct c eqn:Hcond end.
    2:{ cbn [fst snd]. split; [reflexivity|]. split; [lia|]. split; [| right; reflexivity].
        intros HC Hao0. exfalso. apply orb_false_iff in Hcond as [C1 C2]. apply Z.leb_gt in C1.
        destruct HC as [HC|[HF0 Hai0]]; [clear - HC C1; lia|].
        rewrite HF0, Hai0 in C2.
        replace (Z_FINISH =? Z_FINISH) with true in C2 by reflexivity.
        replace (negb (Z_FINISH =? Z_NO_FLUSH)) with true in C2 by reflexivity.
        rewrite orb_true_r in C2. change (0 =? 0) with true in C2. cbn [andb] in C2.
        apply Z.leb_gt in C2. clear - C1 C2 Hmb. lia. }
    set (len := MIN (ds_strstart t - ds_block_start t) (t_have t)).
    assert (Hlen : 0 <= len <= t_have t) by (subst len; split; [apply MIN_nonneg; [clear - Hbs; lia | clear - Rh; lia] | apply MIN_le_r]).
    set (last := if (flush =? Z_FINISH) && (cs_avail_in (ds_strm t) =? 0) && (len =? ds_strstart t - ds_block_start t) then 1 else 0). clearbody last.
    pose proof (k_tr_stored_block ds_strm true true keeps_strm eq_refl t (Some (ds_block_start t)) len last) as Est1.
    pose proof (tr_stored_block_pending t (Some (ds_block_start t)) len last) as Ep1.
    pose proof (bi_windup_pending_mono (send_bits t (Z.shiftl STORED_BLOCK 1 + last) 3)) as B1.
    pose proof (send_bits_pending_mono t (Z.shiftl STORED_BLOCK 1 + last) 3) as B2.
    set (X1 := tr_stored_block t (Some (ds_block_start t)) len last) in *. clearbody X1.
    set (X2 := set_block_start X1 (ds_block_start X1 + len)).
    assert (Est2 : ds_strm X2 = ds_strm t) by (subst X2; dsred; exact Est1).
    assert (Ep2 : ds_pending X2 = ds_pending X1) by (subst X2; dsred; reflexivity).
    clearbody X2.
    pose proof (flush_pending_avail X2 ltac:(rewrite Est2; clear - Hao; lia) ltac:(rewrite Ep2, Ep1; clear - B1 B2 Hp Hlen; lia)
                  ltac:(rewrite Ep2, Ep1; clear - B1 B2 Hp Hlen Rh; lia)) as (Fai & Fao & Fdec).
    cbn [fst snd]. rewrite Fai, Est2. split; [reflexivity|]. split; [rewrite <- Est2; exact Fao|].
    split; [| destruct (negb (last =? 0)); [left | right]; reflexivity].
    intros _ Hao0. rewrite <- Est2. apply Fdec; [rewrite Ep2, Ep1; clear - B1 B2 Hp Hlen; lia | rewrite Est2; exact Hao0].
  Qed.
End StoredP.

Lemma deflate_stored_prog : forall c0 s flush, C0OK' c0 -> RefDeflSafeL0.SI c0 s s -> HF flush s -> 0 < cs_avail_out (ds_strm s) ->
  BPOST flush s (deflate_stored s flush).
Proof.
  intros c0 s flush HC0 HS HH Hao0. pose proof (c0'_ok _ HC0) as HC0w.
  pose proof HS as (HDC & _ & Hm & Hst & _ & Hp). pose proof HDC as [[D X] V].
  pose proof (SI_facts c0 s HC0 s HS) as (_ & _ & _ & Sw & Sl & Epbs & Hl0 & Hbs & Hsn & Hmt & Hstr & Ewsz & Hwr & Hpo & Hbv & Hbb & Hao & Hai & _).
  rewrite deflate_stored_eq. cbv zeta.
  set (mb := wrap32 (MIN (ds_pending_buf_size s - 5) (ds_w_size s))). clearbody mb.
  set (fuel := Z.to_nat (cs_avail_out (ds_strm s) + 1)).
  destruct fuel as [|f] eqn:Ef.
  { exfalso. subst fuel. clear - Ef Hao0. lia. }
  clear Ef.
  pose proof (loop_facts c0 s flush HC0 f s mb HS) as LF. cbv zeta in LF. destruct LF as (HSL & HaiL & Hprog & Hlast).
  set (sL := fst (deflate_stored_loop (S f) s flush mb)) in *. clearbody sL.
  set (last := snd (deflate_stored_loop (S f) s flush mb)) in *. clearbody last.
  pose proof (SI_facts c0 s HC0 sL HSL) as (DL & XL & VL & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HaiL2 & _).
  assert (Eused : wrap32 (cs_avail_in (ds_strm s) - cs_avail_in (ds_strm sL)) = cs_avail_in (ds_strm s) - cs_avail_in (ds_strm sL))
    by (apply wrap32_id; clear - HaiL Hai HaiL2; lia).
  rewrite Eused.
  pose proof (sv_inlen _ _ V) as Il. pose proof (sv_inlen _ _ VL) as IlL. pose proof (sv_nin _ _ V) as Ni.
  pose proof (wupd_stage c0 s HC0 sL (cs_avail_in (ds_strm s) - cs_avail_in (ds_strm sL)) HSL ltac:(clear - HaiL Il IlL Ni; lia)) as W. cbv zeta in W.
  destruct W as (HSW & EstrmW & HbsW).
  set (sW := st_wupd sL (cs_avail_in (ds_strm s) - cs_avail_in (ds_strm sL))) in *. clearbody sW.
  pose proof (hw_stage c0 s HC0 sW HSW) as (HS2 & Estrm2 & Estr2 & Ebs2 & Ewsz2 & Ews2 & _).
  set (s2 := hw_st sW) in *. clearbody s2.
  pose proof (SI_facts c0 s HC0 s2 HS2) as (D2 & X2 & V2 & Sw2 & _ & _ & Hl02 & Hbs2 & _ & _ & Hstr2 & Ewsz2' & _ & _ & _ & _ & _ & Hai2 & _).
  destruct (Z.eqb_spec last 0) as [El|El]; cbn [negb].
  2:{ unfold BPOST; cbn [fst snd]. split; [intros HH'; discriminate HH'|]. split; [intros _; exact (Hlast El)|]. intros [HH'|HH']; discriminate HH'. }
  match goal with |- context [if ?c then (s2, block_done) else _] => destruct c eqn:Hcond end.
  { exfalso. destruct HH as [F|[F _]]; rewrite F in Hcond; cbn in Hcond; discriminate Hcond. }
  clear Hcond.
  assert (Ehave : wrap32 (ds_window_size s2 - ds_strstart s2) = 2 * ds_w_size s2 - ds_strstart s2) by (rewrite Ewsz2'; apply wrap32_id; clear - Hstr2 Hbs2 Sw2; lia).
  rewrite Ehave.
  pose proof (slide3_stage c0 s HC0 s2 _ HS2 eq_refl) as SL3. cbv zeta in SL3. destruct SL3 as (HS3 & Estrm3 & Ehave3 & Ews3).
  pose proof (slide3_bs s2 (2 * ds_w_size s2 - ds_strstart s2)) as SB. cbv zeta in SB.
  destruct (st_slide3 s2 (2 * ds_w_size s2 - ds_strstart s2)) as [s3 have]. cbn [fst snd] in *.
  pose proof (SI_facts c0 s HC0 s3 HS3) as (_ & _ & _ & _ & _ & _ & _ & Hbs3 & _ & _ & Hstr3 & _ & _ & _ & _ & _ & _ & Hai3 & _).
  assert (Hfm : 0 <= fmin have (cs_avail_in (ds_strm s3)) <= cs_avail_in (ds_strm s3) /\ fmin have (cs_avail_in (ds_strm s3)) <= 2 * ds_w_size s3 - ds_strstart s3).
  { unfold fmin. rewrite Ehave3, Ews3. destruct (Z.ltb_spec (cs_avail_in (ds_strm s3)) (2 * ds_w_size s2 - ds_strstart s3)) as [l|l]; clear - l Hai3 Hstr3 Hbs3 Ews3; lia. }
  pose proof (fillw_stage c0 s HC0 s3 (fmin have (cs_avail_in (ds_strm s3))) HS3 (proj1 Hfm) (proj2 Hfm)) as FW. cbv zeta in FW.
  destruct FW as (HS4 & Estr4 & Ebs4 & Ews4 & Eai4 & Eao4 & _).
  set (n := fmin have (cs_avail_in (ds_strm s3))) in *.
  assert (Hn : n = 0 -> cs_avail_in (ds_strm s3) = 0 \/ (have = 0 /\ 0 < cs_avail_in (ds_strm s3))).
  { subst n. unfold fmin. destruct (Z.ltb_spec (cs_avail_in (ds_strm s3)) have) as [l|l]; intros E0; [left; exact E0|].
    destruct (Z.eq_dec (cs_avail_in (ds_strm s3)) 0) as [A|A]; [left; exact A | right; split; [exact E0 | clear - A Hai3; lia]]. }
  clearbody n.
  set (s4 := st_fillw s3 n) in *. clearbody s4.
  pose proof (hw_stage c0 s HC0 s4 HS4) as (HS5 & Estrm5 & Estr5 & Ebs5 & _ & Ews5 & _).
  set (s5 := hw_st s4) in *. clearbody s5.
  pose proof (final_prog c0 s flush HC0 s5 HS5) as FN. cbv zeta in FN. destruct FN as (Eaif & Haof & Hdecf & Hbsf).
  destruct (st_final s5 flush) as [sf bs]. cbn [fst snd] in *.
  unfold BPOST; cbn [fst snd].
  split; [destruct Hbsf as [-> | ->]; intros HH'; discriminate HH'|].
  split; [destruct Hbsf as [-> | ->]; intros HH'; discriminate HH'|].
  intros _.
  assert (Eai5 : cs_avail_in (ds_strm s5) = cs_avail_in (ds_strm sL) - n).
  { rewrite Estrm5, Eai4, Estrm3, Estrm2, EstrmW. reflexivity. }
  assert (Eao5 : cs_avail_out (ds_strm s5) = cs_avail_out (ds_strm sL)).
  { rewrite Estrm5, Eao4, Estrm3, Estrm2, EstrmW. reflexivity. }
  destruct Hprog as [Hlt | [EsL _]].
  - right; right. rewrite <- Eao5 in Hlt. clear - Hlt Haof. lia.
  - subst sL.
    destruct (Z.eq_dec n 0) as [N0|N0].
    2:{ right; left. rewrite Eaif, Eai5. clear - N0 Hfm. lia. }
    right; right.
    assert (Hao5 : 0 < cs_avail_out (ds_strm s5)) by (rewrite Eao5; exact Hao0).
    rewrite <- Eao5. apply Hdecf; [| exact Hao5].
    destruct (Hn N0) as [A0 | [Hv0 Aip]].
    + (* [comment removed for export] *)
      right. destruct HH as [F|[F Aip]]; [| exfalso; rewrite Estrm3, Estrm2, EstrmW in A0; clear - A0 Aip; lia].
      split; [exact F|]. rewrite Eai5, N0. rewrite Estrm3, Estrm2, EstrmW in A0. clear - A0. lia.
    + (* [comment removed for export] *)
      left. rewrite Estr5, Ebs5, Estr4, Ebs4, N0, Z.add_0_r.
      assert (Hmb5 : t_mb s5 <= ds_w_size s5) by (unfold t_mb; apply MIN_le_r).
      rewrite Ews5, Ews4 in Hmb5.
      assert (Hbs3w : ds_block_start s3 <= ds_w_size s3).
      { rewrite Ews3. destruct SB as [(Es3 & Ehv & C) | (Ebs3' & C)].
        - subst s3. apply andb_false_iff in C. destruct C as [C|C].
          + apply Z.ltb_ge in C. exfalso. clear - C Hv0 Aip Ehv. subst have. lia.
          + apply Z.leb_gt in C. clear - C. lia.
        - rewrite Ebs3'. clear - Hbs2 Hstr2. lia. }
      clear - Hmb5 Hbs3w Ehave3 Hv0 Ews3. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Local Notation Hst := stored_bf_spec.
Local Notation Hhf := (huff_bf_spec FB_CALL_ok).
Local Notation Hrl := (rle_bf_spec FB_CALL_ok).
Local Notation Hfa := (fast_bf_spec FB_CALL_ok).
Local Notation Hsl := (slow_bf_spec FB_CALL_ok).

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma strategy_put_byte : forall s b, ds_strategy (put_byte s b) = ds_strategy s. Proof. reflexivity. Qed.
Lemma strategy_putShortMSB : forall s w, ds_strategy (putShortMSB s w) = ds_strategy s.
Proof. intros s w. unfold putShortMSB. rewrite !strategy_put_byte. reflexivity. Qed.
Lemma strstart_putShortMSB : forall s w, ds_strstart (putShortMSB s w) = ds_strstart s. Proof. reflexivity. Qed.
Lemma strategy_set_status : forall s v, ds_strategy (set_status s v) = ds_strategy s. Proof. reflexivity. Qed.
Lemma strategy_set_strm : forall s v, ds_strategy (set_strm s v) = ds_strategy s. Proof. reflexivity. Qed.
Lemma strategy_zhdr_st : forall s, ds_strategy (zhdr_st s) = ds_strategy s.
Proof.
  intros s. unfold zhdr_st. cbv zeta. rewrite !strstart_putShortMSB, strategy_set_status, strategy_set_strm.
  destruct (negb _); rewrite !strategy_putShortMSB; reflexivity.
Qed.
Lemma strategy_gzhdr_st : forall s, ds_strategy (gzhdr_st s) = ds_strategy s.
Proof. intros s. unfold gzhdr_st. cbv zeta. rewrite strategy_set_status, !strategy_put_byte, strategy_set_strm. reflexivity. Qed.
Lemma strategy_flush_pending : forall c0 s, C0OK c0 -> DC c0 s -> ds_strategy (flush_pending s) = ds_strategy s.
Proof.
  intros c0 s HC0 HDC. destruct (DC_flush_pending c0 s HC0 HDC) as (_ & _ & _ & C2 & _).
  pose proof (dx_core2_fields _ _ C2) as (_ & _ & _ & _ & _ & E & _). exact E.
Qed.

(* [comment removed for export] *)
Lemma dmode_strategy0 : forall s, ds_strategy s = 0 -> dmode s = 0 \/ dmode s = 3 \/ dmode s = 4.
Proof.
  intros s Hsg. unfold dmode. rewrite Hsg. change (0 =? Z_HUFFMAN_ONLY) with false. change (0 =? Z_RLE) with false.
  destruct (ds_level s =? 0); [left; reflexivity|]. destruct (ds_level s <=? 3); [right; left | right; right]; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma ao_mono : forall c0 a b, SV c0 a -> SV c0 b -> OUTLE a b -> cs_avail_out (ds_strm b) <= cs_avail_out (ds_strm a).
Proof.
  intros c0 a b Va Vb Ho. pose proof (sv_out _ _ Va) as A. pose proof (sv_out _ _ Vb) as B. pose proof (OUTLE_len _ _ Ho) as L.
  unfold zlen in A, B. lia.
Qed.

Section CoreP.
  Variable c0 : cstrm.
Variable s0 : deflate_state.
  Hypothesis HC0 : C0OK' c0.
  Hypothesis Hs0 : ds_strm s0 = c0.
  Hypothesis D0 : dwf s0.
  Let HC0w : C0OK c0 := c0'_ok _ HC0.

  Local Notation ST := (RefDeflSafeI4.ST c0 s0).

  (* [comment removed for export] *)
  Definition HFc (flush : Z) : Prop := flush = Z_FINISH \/ (flush = Z_NO_FLUSH /\ 0 < cs_avail_in c0).

  (* [comment removed for export] *)
  Definition PRG (s : deflate_state) : Prop :=
    0 < cs_avail_out c0
    /\ (cs_avail_out (ds_strm s) = 0 \/ cs_avail_in (ds_strm s) < cs_avail_in c0 \/ cs_avail_out (ds_strm s) < cs_avail_out c0).

  Definition RES (r : deflate_state * Z) : Prop := ST (fst r) /\ (snd r = Z_OK -> PRG (fst r)).

  Lemma ST_aout_le : forall s, ST s -> 0 <= cs_avail_out (ds_strm s) <= cs_avail_out c0.
  Proof.
    intros s [[[D X] V] K]. pose proof (sv_out _ _ V) as A. pose proof (sv_aout _ _ V) as B. pose proof (c0_out _ HC0w) as O0.
    rewrite O0 in A. unfold zlen in A. cbn [length Z.of_nat] in A. pose proof (Zle_0_nat (length (cs_out_rev (ds_strm s)))). lia.
  Qed.

  Lemma RES_noprog : forall s rc, ST s -> rc <> Z_OK -> RES (s, rc).
  Proof. intros s rc HS Hrc. split; [exact HS | intros E; exfalso; exact (Hrc E)]. Qed.
  Lemma RES_err : forall s e, ST s -> e <> Z_OK -> RES (err_return s e).
  Proof. intros s e HS He. split; [exact (ST_err_return c0 s0 s e HS) | cbn [snd err_return]; intros E; exfalso; exact (He E)]. Qed.

  (* [comment removed for export] *)
  Lemma blocks_prog : forall s flush, ST s -> ds_pending s = 0 -> ds_strategy s = 0 -> 0 <= flush <= 5 -> HFc flush ->
    cs_avail_in (ds_strm s) = cs_avail_in c0 -> 0 < cs_avail_out c0 ->
    (ds_status s = FINISH_STATE -> cs_avail_in (ds_strm s) = 0) ->
    let r := deflate_blocks s flush in
    ST (fst r)
    /\ (snd r = Some Z_OK -> PRG (fst r))
    /\ (snd r = None -> ds_pending (fst r) = 0 /\ (flush = Z_FINISH -> ds_status (fst r) = FINISH_STATE) /\ (flush <> Z_FINISH -> PRG (fst r))).
  Proof.
    intros s flush HS Hp Hsg Hfl HH Eai Hao0 Hfin r. subst r. pose proof HS as [H K]. pose proof H as [[D X] V].
    unfold deflate_blocks.
    match goal with |- context [if ?c then _ else (s, None)] => destruct c eqn:Hcond end.
    2:{ cbn [fst snd]. split; [exact HS|]. split; [intros HH'; discriminate HH'|]. intros _. split; [exact Hp|].
        apply orb_false_iff in Hcond as [Hcond C3]. apply orb_false_iff in Hcond as [C1 C2].
        split.
        - intros Hf. apply andb_false_iff in C3. destruct C3 as [C3|C3].
          + exfalso. rewrite Hf in C3. cbn in C3. discriminate C3.
          + destruct (Z.eqb_spec (ds_status s) FINISH_STATE); [assumption | discriminate C3].
        - intros Hnf. exfalso. destruct HH as [F|[F Hai]]; [exact (Hnf F)|].
          destruct (Z.eqb_spec (cs_avail_in (ds_strm s)) 0) as [A|A]; [| discriminate C1]. rewrite Eai in A. clear - A Hai. lia. }
    assert (Hst0 : ds_status s <> FINISH_STATE).
    { intros Ef. rewrite (Hfin Ef), (dx_fin _ X Ef), Ef in Hcond. cbn in Hcond. rewrite andb_false_r in Hcond. discriminate Hcond. }
    assert (HHs : HF flush s) by (destruct HH as [F|[F Hai]]; [left; exact F | right; split; [exact F | rewrite Eai; exact Hai]]).
    destruct (bf_call _ _ _ _ Hst Hhf Hrl Hfa Hsl c0 s0 HC0 s flush HS Hp Hst0 Hfl) as [_ HPOST].
    assert (PRE : BFPRE c0 s flush) by (split; [exact HC0|]; split; [exact H|]; split; [exact Hp|]; split; [exact Hst0 | exact Hfl]).
    assert (HB : 0 < cs_avail_out (ds_strm s) -> BPOST flush s (run_compress_func s flush)).
    { intros Hao. rewrite run_compress_func_dmode.
      destruct (dmode_strategy0 s Hsg) as [Em|[Em|Em]]; rewrite Em.
      - apply (deflate_stored_prog c0 s flush HC0); [| exact HHs | exact Hao].
        split; [exact H|]. split; [reflexivity|]. split; [exact Em|]. split; [exact Hst0|]. split; [apply OUTLE_refl | exact Hp].
      - apply (deflate_fast_prog c0 s flush HC0); [| exact HHs].
        split; [exact H|]. split; [reflexivity|]. split; [exact Hp|]. split; [exact Em|]. split; [exact Hst0 | apply OUTLE_refl].
      - apply (deflate_slow_prog c0 s flush HC0); [| exact HHs].
        split; [exact H|]. split; [reflexivity|]. split; [exact Hp|]. split; [exact Em|]. split; [exact Hst0 | apply OUTLE_refl]. }
    destruct (run_compress_func s flush) as [s1 bst]. cbv beta iota zeta.
    unfold BFPOST in HPOST. cbn [fst snd] in HPOST. destruct HPOST as (H1 & K1 & O1 & Pbd & Pfin & Pfd).
    assert (HS1 : ST s1) by (split; [exact H1 | rewrite K1; exact K]).
    pose proof H1 as [[D1 X1] V1].
    pose proof (ao_mono c0 s s1 V V1 O1) as AO1. pose proof (ST_aout_le s HS) as AOs. pose proof (ST_aout_le s1 HS1) as AOs1.
    unfold BPOST in HB. cbn [fst snd] in HB.
    set (s2 := if block_state_eqb bst finish_started || block_state_eqb bst finish_done then set_status s1 FINISH_STATE else s1) in *.
    assert (HS2 : ST s2 /\ ds_pending s2 = ds_pending s1 /\ ds_strm s2 = ds_strm s1
                  /\ (block_state_eqb bst finish_started || block_state_eqb bst finish_done = true -> ds_status s2 = FINISH_STATE)
                  /\ (block_state_eqb bst finish_started || block_state_eqb bst finish_done = false -> s2 = s1)).
    { subst s2. destruct (block_state_eqb bst finish_started || block_state_eqb bst finish_done) eqn:Eb.
      - assert (Hl : ds_lookahead s1 = 0).
        { apply Pfin. destruct bst; cbn in Eb; try discriminate Eb; [left | right]; reflexivity. }
        destruct (DC_set_status c0 s1 FINISH_STATE H1 ltac:(unfold FINISH_STATE; lia) ltac:(intros; reflexivity) ltac:(intros _; exact Hl)) as (H2 & K2 & S2).
        split; [split; [exact H2 | rewrite K2, K1; exact K]|].
        split; [reflexivity|]. split; [exact S2|]. split; [intros; reflexivity | intros HH'; discriminate HH'].
      - split; [exact HS1|]. split; [reflexivity|]. split; [reflexivity|]. split; [intros HH'; discriminate HH' | intros; reflexivity]. }
    clearbody s2. destruct HS2 as (HS2 & P2 & S2 & Fin2 & NFin2).
    destruct (block_state_eqb bst need_more || block_state_eqb bst finish_started) eqn:Enm.
    { assert (Hnm : bst = need_more \/ bst = finish_started) by (destruct bst; cbn in Enm; try discriminate Enm; [left | right]; reflexivity).
      assert (HP : PRG s2).
      { split; [exact Hao0|]. rewrite S2.
        destruct (Z.eq_dec (cs_avail_out (ds_strm s)) 0) as [A0|A0].
        - left. clear - A0 AO1 AOs1. lia.
        - destruct (HB ltac:(clear - A0 AOs; lia)) as (_ & _ & HB3). destruct (HB3 Hnm) as [B|[B|B]].
          + left; exact B.
          + right; left. rewrite <- Eai. exact B.
          + right; right. clear - B AOs. lia. }
      cbn [fst snd]. destruct (cs_avail_out (ds_strm s2) =? 0).
      - split; [apply (ST_set_last_flush c0 s0); [exact HS2 | lia]|]. split; [intros _; exact HP | intros HH'; discriminate HH'].
      - split; [exact HS2|]. split; [intros _; exact HP | intros HH'; discriminate HH']. }
    destruct (block_state_eqb bst block_done) eqn:Ebd.
    + assert (Eb : bst = block_done) by (destruct bst; cbn in Ebd; try discriminate Ebd; reflexivity). subst bst.
      (* [comment removed for export] *)
      assert (A0 : cs_avail_out (ds_strm s) = 0).
      { destruct (Z.eq_dec (cs_avail_out (ds_strm s)) 0) as [A0|A0]; [exact A0|]. exfalso.
        destruct (HB ltac:(clear - A0 AOs; lia)) as (HB1 & _). exact (HB1 eq_refl). }
      destruct (Pbd eq_refl) as (Hp1 & Hnf & Hma1). cbn in NFin2. rewrite (NFin2 eq_refl).
      destruct (bdone_facts c0 s1 flush H1 Hp1 Hma1) as (B1 & B2 & B3 & _).
      assert (HSb : ST (bdone_st s1 flush)) by (split; [exact B1 | rewrite B2, K1; exact K]).
      destruct (ST_flush_pending c0 s0 HC0 _ HSb) as (HSf & _).
      pose proof (DC_flush_pending c0 (bdone_st s1 flush) HC0w B1) as FP. cbv zeta in FP. destruct FP as (Bf & _ & Of & _).
      pose proof (ao_mono c0 (bdone_st s1 flush) (flush_pending (bdone_st s1 flush)) (proj2 B1) (proj2 Bf) Of) as AOf.
      rewrite B3 in AOf. pose proof (ST_aout_le _ HSf) as AOf0.
      match goal with |- context [flush_pending ?b] => replace b with (bdone_st s1 flush) by (unfold bdone_st; reflexivity) end.
      assert (HP : PRG (flush_pending (bdone_st s1 flush))) by (split; [exact Hao0 | left; clear - A0 AO1 AOf AOf0; lia]).
      destruct (Z.eqb_spec (cs_avail_out (ds_strm (flush_pending (bdone_st s1 flush)))) 0) as [Ea|Ea]; cbn [fst snd].
      * split; [apply (ST_set_last_flush c0 s0); [exact HSf | lia]|]. split; [intros _; exact HP | intros HH'; discriminate HH'].
      * exfalso. apply Ea. clear - A0 AO1 AOf AOf0. lia.
    + (* [comment removed for export] *)
      assert (Eb : bst = finish_done) by (destruct bst; cbn in Enm, Ebd; try discriminate Enm; try discriminate Ebd; reflexivity). subst bst.
      cbn [fst snd]. split; [exact HS2|]. split; [intros HH'; discriminate HH'|].
      intros _. split; [rewrite P2; exact (Pfd eq_refl)|]. split; [intros _; apply Fin2; reflexivity|].
      intros Hnf. split; [exact Hao0|]. rewrite S2.
      destruct (Z.eq_dec (cs_avail_out (ds_strm s)) 0) as [A0|A0]; [left; clear - A0 AO1 AOs1; lia|].
      exfalso. destruct (HB ltac:(clear - A0 AOs; lia)) as (_ & HB2 & _). exact (Hnf (HB2 eq_refl)).
  Qed.

  (* [comment removed for export] *)
  Lemma trailer_prog : forall s, ST s -> ds_pending s = 0 -> ds_status s = FINISH_STATE -> 0 < ds_wrap s -> 0 < cs_avail_out c0 ->
    RES (deflate_trailer s).
  Proof.
    intros s HS Hp Hfs Hw Hao0. pose proof HS as [H K].
    destruct (finish_stage c0 s0 HC0 Hs0 D0 s Z_FINISH HS Hp ltac:(unfold Z_FINISH; lia) ltac:(intros _; exact Hfs)) as [_ HT].
    pose proof (HT eq_refl Hw) as HSt.
    split; [exact HSt|].
    revert HSt. rewrite deflate_trailer_eq. cbv zeta.
    destruct (trailer_facts c0 s H Hp) as ((Ht & _ & _) & Kt & _).
    assert (HSh : ST (trailer_st s)) by (split; [exact Ht | rewrite Kt; exact K]).
    destruct (ST_flush_pending c0 s0 HC0 _ HSh) as (HSf & _ & Hor & _).
    set (f := flush_pending (trailer_st s)) in *. clearbody f.
    intros _. cbn [fst snd].
    assert (Es : ds_strm (if 0 <? ds_wrap f then set_wrap f (- ds_wrap f) else f) = ds_strm f /\ ds_pending (if 0 <? ds_wrap f then set_wrap f (- ds_wrap f) else f) = ds_pending f).
    { destruct (0 <? ds_wrap f); dsred; split; reflexivity. }
    destruct Es as [Es Ep]. rewrite Ep. intros Hrc.
    destruct (Z.eqb_spec (ds_pending f) 0) as [P0|P0]; [cbn in Hrc; discriminate Hrc|].
    split; [exact Hao0|]. left. rewrite Es. destruct Hor as [X|X]; [exfalso; exact (P0 X) | exact X].
  Qed.

  (* [comment removed for export] *)
  Definition core_fin (s : deflate_state) (flush : Z) : deflate_state * Z :=
    let '(s, r) := deflate_blocks s flush in
    match r with Some rc => (s, rc) | None =>
    if negb (Z.eqb flush Z_FINISH) then (s, Z_OK)
    else if Z.leb (ds_wrap s) 0 then (s, Z_STREAM_END)
    else deflate_trailer s
    end.

  Lemma fin_prog : forall s flush, ST s -> ds_pending s = 0 -> ds_strategy s = 0 -> 0 <= flush <= 5 -> HFc flush ->
    cs_avail_in (ds_strm s) = cs_avail_in c0 -> 0 < cs_avail_out c0 ->
    (ds_status s = FINISH_STATE -> cs_avail_in (ds_strm s) = 0) ->
    RES (core_fin s flush).
  Proof.
    intros s flush HS Hp Hsg Hfl HH Eai Hao0 Hfin.
    pose proof (blocks_prog s flush HS Hp Hsg Hfl HH Eai Hao0 Hfin) as B. cbv zeta in B. destruct B as (HSr & HZ & HN).
    unfold core_fin. destruct (deflate_blocks s flush) as [b r]. cbn [fst snd] in HSr, HZ, HN.
    destruct r as [rc|].
    { split; [exact HSr | cbn [fst snd]; intros ->; exact (HZ eq_refl)]. }
    destruct (HN eq_refl) as (Hpb & Hfs & Hnf).
    destruct (Z.eqb_spec flush Z_FINISH) as [F|F]; cbn [negb].
    2:{ split; [exact HSr | cbn [fst snd]; intros _; exact (Hnf F)]. }
    destruct (Z.leb_spec (ds_wrap b) 0) as [W|W].
    { apply RES_noprog; [exact HSr | intros X; discriminate X]. }
    exact (trailer_prog b HSr Hpb (Hfs F) W Hao0).
  Qed.

  (* [comment removed for export] *)
  Definition core_tail (s : deflate_state) (flush : Z) : deflate_state * Z :=
    if Z.eqb (ds_status s) FINISH_STATE && negb (Z.eqb (cs_avail_in (ds_strm s)) 0)
    then err_return s Z_BUF_ERROR
    else
    let s := if Z.eqb (ds_status s) INIT_STATE && Z.eqb (ds_wrap s) 0 then set_status s BUSY_STATE else s in
    let '(s, r) := if Z.eqb (ds_status s) INIT_STATE then deflate_zlib_header s else (s, None) in
    match r with Some rc => (s, rc) | None =>
    let '(s, r) := if Z.eqb (ds_status s) GZIP_STATE then deflate_gzip_header s else (s, None) in
    match r with Some rc => (s, rc) | None =>
    core_fin s flush
    end end.

  Lemma tail_prog : forall s flush, ST s -> ds_pending s = 0 -> ds_strategy s = 0 -> 0 <= flush <= 5 -> HFc flush ->
    cs_avail_in (ds_strm s) = cs_avail_in c0 -> 0 < cs_avail_out c0 ->
    RES (core_tail s flush).
  Proof.
    intros s flush HS Hp Hsg Hfl HH Eai Hao0. pose proof HS as [H K].
    unfold core_tail.
    destruct ((ds_status s =? FINISH_STATE) && negb (cs_avail_in (ds_strm s) =? 0)) eqn:Efa.
    { apply RES_err; [exact HS | intros X; discriminate X]. }
    assert (Hnf : ~ (ds_status s = FINISH_STATE /\ cs_avail_in (ds_strm s) <> 0)).
    { intros [A1 A2]. rewrite A1 in Efa. cbn in Efa. destruct (Z.eqb_spec (cs_avail_in (ds_strm s)) 0); [exact (A2 ltac:(assumption)) | discriminate Efa]. }
    cbv zeta.
    set (v := if (ds_status s =? INIT_STATE) && (ds_wrap s =? 0) then set_status s BUSY_STATE else s).
    assert (HV : ST v /\ ds_pending v = 0 /\ ds_strategy v = 0 /\ cs_avail_in (ds_strm v) = cs_avail_in c0
                 /\ (ds_status v = FINISH_STATE -> ds_status s = FINISH_STATE)).
    { subst v. destruct ((ds_status s =? INIT_STATE) && (ds_wrap s =? 0)) eqn:E.
      - apply andb_prop in E as [E1 E2]. apply Z.eqb_eq in E1. apply Z.eqb_eq in E2.
        destruct (DC_set_status c0 s BUSY_STATE H ltac:(unfold BUSY_STATE; lia) ltac:(intros; exfalso; lia) ltac:(unfold BUSY_STATE, FINISH_STATE; intros; lia)) as (G1 & KG1 & _).
        split; [split; [exact G1 | rewrite KG1; exact K]|]. dsred. split; [exact Hp|]. split; [exact Hsg|]. split; [exact Eai|].
        unfold BUSY_STATE, FINISH_STATE. intros; lia.
      - split; [exact HS|]. split; [exact Hp|]. split; [exact Hsg|]. split; [exact Eai|]. intros X0; exact X0. }
    clearbody v. destruct HV as (HSv & Hpv & Hsgv & Aiv & Finv). pose proof HSv as [Hv Kv].
    (* [comment removed for export] *)
    destruct (Z.eqb_spec (ds_status v) INIT_STATE) as [Ei|Ei].
    - rewrite deflate_zlib_header_eq. cbv zeta.
      destruct (hdr_zlib c0 s0 HC0 Hs0 D0 v HSv Hpv Ei) as (_ & HSz & Stz & Horz & Aiz & _).
      pose proof (strategy_flush_pending c0 (zhdr_st v) HC0w (proj1 (proj1 (zhdr_facts c0 v Hv Hpv Ei)))) as Sgz.
      rewrite strategy_zhdr_st in Sgz.
      set (z := flush_pending (zhdr_st v)) in *. clearbody z.
      destruct (Z.eqb_spec (ds_pending z) 0) as [Pz|Pz]; cbn [negb].
      + rewrite Stz. change (BUSY_STATE =? GZIP_STATE) with false. cbv beta iota.
        apply fin_prog; [exact HSz | exact Pz | rewrite Sgz; exact Hsgv | exact Hfl | exact HH | rewrite Aiz; exact Aiv | exact Hao0 |].
        rewrite Stz. unfold BUSY_STATE, FINISH_STATE. intros; lia.
      + split; [apply (ST_set_last_flush c0 s0); [exact HSz | lia]|]. cbn [fst snd]. intros _.
        split; [exact Hao0|]. left. dsred. destruct Horz as [X0|X0]; [exfalso; exact (Pz X0) | exact X0].
    - cbn [negb].
      (* [comment removed for export] *)
      destruct (Z.eqb_spec (ds_status v) GZIP_STATE) as [Eg|Eg].
      + rewrite deflate_gzip_header_eq. cbv zeta.
        destruct (hdr_gzip c0 s0 HC0 Hs0 D0 v HSv Hpv Eg) as (_ & HSz & Stz & Horz & Aiz & _).
        pose proof (strategy_flush_pending c0 (gzhdr_st v) HC0w (proj1 (proj1 (gzhdr_facts c0 v Hv Hpv Eg)))) as Sgz.
        rewrite strategy_gzhdr_st in Sgz.
        set (z := flush_pending (gzhdr_st v)) in *. clearbody z.
        destruct (Z.eqb_spec (ds_pending z) 0) as [Pz|Pz]; cbn [negb].
        * apply fin_prog; [exact HSz | exact Pz | rewrite Sgz; exact Hsgv | exact Hfl | exact HH | rewrite Aiz; exact Aiv | exact Hao0 |].
          rewrite Stz. unfold BUSY_STATE, FINISH_STATE. intros; lia.
        * split; [apply (ST_set_last_flush c0 s0); [exact HSz | lia]|]. cbn [fst snd]. intros _.
          split; [exact Hao0|]. left. dsred. destruct Horz as [X0|X0]; [exfalso; exact (Pz X0) | exact X0].
      + apply fin_prog; [exact HSv | exact Hpv | exact Hsgv | exact Hfl | exact HH | exact Aiv | exact Hao0 |].
        intros Ef. rewrite Aiv, <- Eai. destruct (Z.eq_dec (cs_avail_in (ds_strm s)) 0) as [A|A]; [exact A|]. exfalso. apply Hnf. split; [exact (Finv Ef) | exact A].
  Qed.

  (* [comment removed for export] *)
  Lemma core_prog : forall flush, ST s0 -> ds_strategy s0 = 0 -> 0 <= flush <= 5 -> HFc flush ->
    RES (deflate_core s0 flush).
  Proof.
    intros flush HS Hsg Hfl HH. pose proof HS as [H K]. pose proof H as [[D X] V].
    unfold deflate_core.
    destruct (deflateStateCheck s0 || (Z_BLOCK <? flush) || (flush <? 0)) eqn:Echk.
    { apply RES_noprog; [exact HS | intros X0; discriminate X0]. }
    destruct ((ds_status s0 =? FINISH_STATE) && negb (flush =? Z_FINISH)).
    { apply RES_err; [exact HS | intros X0; discriminate X0]. }
    destruct (Z.eqb_spec (cs_avail_out (ds_strm s0)) 0) as [Hao|Hao].
    { apply RES_err; [exact HS | intros X0; discriminate X0]. }
    assert (Hao0 : 0 < cs_avail_out c0) by (rewrite <- Hs0; pose proof (ST_aout_le s0 HS); lia).
    cbv zeta.
    pose proof (ST_set_last_flush c0 s0 s0 flush HS ltac:(lia)) as HSu.
    assert (Eu : ds_strm (set_last_flush s0 flush) = c0 /\ ds_pending (set_last_flush s0 flush) = ds_pending s0 /\ ds_strategy (set_last_flush s0 flush) = 0).
    { dsred. split; [exact Hs0 | split; [reflexivity | exact Hsg]]. }
    set (u := set_last_flush s0 flush) in *. clearbody u. destruct Eu as (Esu & Epu & Hsgu).
    pose proof HSu as [Hu Ku]. pose proof Hu as [[DWu Xu] Vu].
    destruct (Z.eqb_spec (ds_pending u) 0) as [Ep|Ep]; cbn [negb].
    - (* [comment removed for export] *)
      destruct ((cs_avail_in (ds_strm u) =? 0) && (RANK flush <=? RANK (ds_last_flush s0)) && negb (flush =? Z_FINISH)).
      + unfold err_return. cbn [negb]. apply RES_err; [exact HSu | intros X0; discriminate X0].
      + apply tail_prog; [exact HSu | exact Ep | exact Hsgu | exact Hfl | exact HH | rewrite Esu; reflexivity | exact Hao0].
    - (* [comment removed for export] *)
      destruct (ST_flush_pending c0 s0 HC0 u HSu) as (HSf & _ & Hor & _ & _ & _ & _ & Aif).
      pose proof (strategy_flush_pending c0 u HC0w Hu) as Sgf. rewrite Hsgu in Sgf.
      set (f := flush_pending u) in *. clearbody f.
      destruct (Z.eqb_spec (cs_avail_out (ds_strm f)) 0) as [Ea|Ea]; cbn [negb].
      + split; [apply (ST_set_last_flush c0 s0); [exact HSf | lia]|]. cbn [fst snd]. intros _. split; [exact Hao0|]. left. dsred. exact Ea.
      + assert (Hpf : ds_pending f = 0) by (destruct Hor as [X0|X0]; [exact X0 | exfalso; exact (Ea X0)]).
        apply tail_prog; [exact HSf | exact Hpf | exact Sgf | exact Hfl | exact HH | rewrite Aif, Esu; reflexivity | exact Hao0].
  Qed.
End CoreP.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

