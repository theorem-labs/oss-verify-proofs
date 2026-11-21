(** * BtExports — re-exports of landed [build_tree] facts in the exact
      shapes the emitter side consumes (relay requests R1/R2, 2026-08-19).

    OWNER: an earlier development run.  R1: blcount support round-trips a build (the TK_D and
    TK_BL builds take entry support as a premise, so the TK_L build's output
    must deliver it).  R2: pointwise [tr_dl] non-negativity survives a build
    (LdDynV's HLnn/HDnn quantify ALL indices, not just the live range);
    [KraftDlNn] has every per-write step, this file adds the loop walks. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Huff Trees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  BtWin BtCensus2 BtCensus4 BtCensus5 BtPass1 BtItem6 BtItem6b BuildTree
  HuffGenCodes KraftAdjust KraftDlNn BtLive.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

(** ** R1: blcount support at the output *)

Theorem build_tree_blc0 :
  forall k s t0 hp0 dep0 hlen0 maxc0 t1 hp1 dep1 hlen1 maxc1 ol1 sl1 stf,
  3 <= sd_elems k <= L_CODES ->
  1 <= sd_max_length k <= 15 ->
  4 * (hlen1 - 1) < 2 ^ sd_max_length k ->
  (forall b, b < 0 \/ 15 < b -> ts_blcount s b = 0) ->
  bt_init (Z.to_nat L_CODES + 2) 0 (sd_elems k) (ts_trees s k) (ts_heap s)
          (ts_depth s) 0 (-1) = (t0, hp0, dep0, hlen0, maxc0) ->
  bt_force2 3%nat (sd_stree k) t0 hp0 dep0 hlen0 maxc0
            (ts_optlen s) (ts_statlen s)
    = (t1, hp1, dep1, hlen1, maxc1, ol1, sl1) ->
  bt_loop (Z.to_nat HEAP_SIZE)
          {| b_tree := t1;
             b_heap := bt_heapify (Z.to_nat HEAP_SIZE) t1 dep1 hp1 hlen1
                                  (hlen1 / 2);
             b_dep := dep1; b_hlen := hlen1; b_hmax := HEAP_SIZE;
             b_node := sd_elems k |}
    = Some stf ->
  forall b, b < 1 \/ sd_max_length k < b ->
  ts_blcount (build_tree k s) b = 0.
Proof.
  intros k s t0 hp0 dep0 hlen0 maxc0 t1 hp1 dep1 hlen1 maxc1 ol1 sl1 stf
         Hel HM HK Hbl0 E0 E2 Eloop b Hb.
  destruct (build_tree_parked k s t0 hp0 dep0 hlen0 maxc0
              t1 hp1 dep1 hlen1 maxc1 ol1 sl1
              (bt_heapify (Z.to_nat HEAP_SIZE) t1 dep1 hp1 hlen1 (hlen1 / 2))
              stf Hel E0 E2 eq_refl Eloop)
    as [Hpk [Hout1 [Hsz [Hcen Hfr0]]]].
  set (hp3 := zset (b_heap stf) (b_hmax stf - 1) (b_heap stf 1)) in *.
  set (hmaxf := b_hmax stf - 1) in *.
  set (ndf := b_node stf) in *.
  set (M := sd_max_length k) in *.
  pose proof (bp_hmax _ _ _ _ _ _ _ Hpk) as Hhm.
  assert (Hmf0 : 0 <= hmaxf)
    by (unfold HEAP_SIZE in Hhm; unfold L_CODES in Hsz; lia).
  destruct (gen_bitlen_out k (s1_of k maxc1 stf ol1 sl1 s) (sd_elems k) maxc1
              M t1 (b_tree stf) hp3 hmaxf ndf hlen1
              Hpk HM Hmf0 eq_refl
              (s1_heap k maxc1 stf ol1 sl1 s)
              (s1_heapmax k maxc1 stf ol1 sl1 s)
              (s1_trees k maxc1 stf ol1 sl1 s)
              (s1_maxcode k maxc1 stf ol1 sl1 s)
              ltac:(intros b' Hb'; rewrite s1_blcount; apply Hbl0; exact Hb')
              Hcen ltac:(lia) HK)
    as [G1 [G2 [G3 [G4 [G5 G6]]]]].
  unfold build_tree. cbv zeta.
  rewrite E0. cbv beta match.
  rewrite E2. cbv beta match.
  rewrite Eloop. cbv beta match.
  fold (s1_of k maxc1 stf ol1 sl1 s).
  set (s2 := gen_bitlen k (s1_of k maxc1 stf ol1 sl1 s)) in *.
  rewrite blc_settree.
  apply G3. exact Hb.
Qed.


(** ** R2: [tr_dl] non-negativity survives a build

    [KraftDlNn] proves every per-write step; these are the loop walks it
    declined to claim, plus the [build_tree]-level composition. *)

Lemma DlNn_bt_init : forall fuel n elems t hp dep hlen maxc
                            t' hp' dep' hlen' maxc',
  bt_init fuel n elems t hp dep hlen maxc = (t', hp', dep', hlen', maxc') ->
  DlNn t -> DlNn t'.
Proof.
  induction fuel as [|f IH];
    intros n elems t hp dep hlen maxc t' hp' dep' hlen' maxc' H Ht;
    cbn [bt_init] in H.
  - injection H as <- _ _ _ _. exact Ht.
  - destruct (Z.leb elems n); [injection H as <- _ _ _ _; exact Ht|].
    destruct (Z.eqb (t_freq t n) 0).
    + exact (IH _ _ _ _ _ _ _ _ _ _ _ _ H (DlNn_setlen t n 0 Ht)).
    + exact (IH _ _ _ _ _ _ _ _ _ _ _ _ H Ht).
Qed.

Lemma DlNn_bt_force2 : forall fuel stree t hp dep hlen maxc ol sl
                              t' hp' dep' hlen' maxc' ol' sl',
  bt_force2 fuel stree t hp dep hlen maxc ol sl
    = (t', hp', dep', hlen', maxc', ol', sl') ->
  DlNn t -> DlNn t'.
Proof.
  induction fuel as [|f IH];
    intros stree t hp dep hlen maxc ol sl t' hp' dep' hlen' maxc' ol' sl'
           H Ht;
    cbn [bt_force2] in H.
  - injection H as <- _ _ _ _ _ _. exact Ht.
  - destruct (Z.leb 2 hlen); [injection H as <- _ _ _ _ _ _; exact Ht|].
    cbv zeta in H.
    refine (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H _).
    apply DlNn_setfreq. exact Ht.
Qed.

Lemma DlNn_bt_step : forall st r,
  bt_step st = r ->
  DlNn (b_tree st) ->
  match r with
  | BtCont st' => DlNn (b_tree st')
  | BtDone st' => DlNn (b_tree st')
  end.
Proof.
  intros st r H Ht.
  unfold bt_step in H. cbv zeta in H.
  destruct (Z.leb 2 (b_hlen st - 1)); subst r; cbn [b_tree];
    apply DlNn_setdad, DlNn_setdad, DlNn_setfreq; exact Ht.
Qed.

Lemma DlNn_bt_loop : forall fuel st stf,
  bt_loop fuel st = Some stf ->
  DlNn (b_tree st) -> DlNn (b_tree stf).
Proof.
  induction fuel as [|f IH]; intros st stf H Ht; cbn [bt_loop] in H;
    [discriminate H|].
  destruct (bt_step st) as [st'|st'] eqn:Hs.
  - apply (IH st' stf H).
    exact (DlNn_bt_step st (BtCont st') Hs Ht).
  - injection H as <-.
    exact (DlNn_bt_step st (BtDone st') Hs Ht).
Qed.

Lemma DlNn_gb_pass1 : forall fuel k hp maxc maxlen base extra stree h t blc
                             ol sl ov t' blc' ol' sl' ov',
  gb_pass1 fuel k hp maxc maxlen base extra stree h t blc ol sl ov
    = (t', blc', ol', sl', ov') ->
  DlNn t -> DlNn t'.
Proof.
  induction fuel as [|f IH];
    intros k hp maxc maxlen base extra stree h t blc ol sl ov
           t' blc' ol' sl' ov' H Ht;
    cbn [gb_pass1] in H.
  - injection H as <- _ _ _ _. exact Ht.
  - destruct (Z.leb HEAP_SIZE h); [injection H as <- _ _ _ _; exact Ht|].
    cbv zeta in H.
    destruct (Z.ltb maxc (hp h)).
    + refine (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H _).
      apply DlNn_setlen. exact Ht.
    + refine (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H _).
      apply DlNn_setlen. exact Ht.
Qed.

Lemma DlNn_gb_pass2 : forall fuel hp maxc t blc bits n h ol t' ol',
  gb_pass2 fuel hp maxc t blc bits n h ol = (t', ol') ->
  DlNn t -> DlNn t'.
Proof.
  induction fuel as [|f IH]; intros hp maxc t blc bits n h ol t' ol' H Ht;
    cbn [gb_pass2] in H.
  - injection H as <- _. exact Ht.
  - destruct (Z.eqb n 0).
    + destruct (Z.leb bits 1); [injection H as <- _; exact Ht|].
      exact (IH _ _ _ _ _ _ _ _ _ _ H Ht).
    + cbv zeta in H.
      destruct (Z.ltb maxc (hp (h - 1)));
        [exact (IH _ _ _ _ _ _ _ _ _ _ H Ht)|].
      destruct (Z.eqb (t_len t (hp (h - 1))) bits);
        [exact (IH _ _ _ _ _ _ _ _ _ _ H Ht)|].
      refine (IH _ _ _ _ _ _ _ _ _ _ H _).
      apply DlNn_setlen. exact Ht.
Qed.

Lemma DlNn_gc_assign : forall fuel n maxc t nc,
  DlNn t -> DlNn (gc_assign fuel n maxc t nc).
Proof.
  induction fuel as [|f IH]; intros n maxc t nc Ht; cbn [gc_assign];
    [exact Ht|].
  destruct (Z.ltb maxc n); [exact Ht|].
  cbv zeta.
  destruct (Z.eqb (t_len t n) 0); [exact (IH _ _ _ _ Ht)|].
  apply IH. apply DlNn_setcode. exact Ht.
Qed.

Lemma DlNn_gen_bitlen : forall k s,
  DlNn (ts_trees s k) -> DlNn (ts_trees (gen_bitlen k s) k).
Proof.
  intros k s Ht. unfold gen_bitlen.
  destruct (gb_pass1 (Z.to_nat HEAP_SIZE + 1) k (ts_heap s)
              (ts_maxcode s k) (sd_max_length k) (sd_extra_base k)
              (sd_extra k) (sd_stree k) (ts_heapmax s + 1)
              (t_setlen (ts_trees s k) (ts_heap s (ts_heapmax s)) 0)
              (arr_zero (Z.to_nat MAX_BITS + 1) 0 (ts_blcount s))
              (ts_optlen s) (ts_statlen s) 0)
    as [[[[t2 blc1] ol1] sl1] ov] eqn:HP1.
  assert (Ht2 : DlNn t2).
  { refine (DlNn_gb_pass1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HP1 _).
    apply DlNn_setlen. exact Ht. }
  destruct (Z.eqb ov 0).
  - cbn [ts_trees set_statlen set_optlen set_blcount].
    rewrite set_tree_same. exact Ht2.
  - destruct (gb_pass2 (2 * Z.to_nat HEAP_SIZE + Z.to_nat MAX_BITS + 4)
                (ts_heap s) (ts_maxcode s k) t2
                (gb_adjust (Z.to_nat ov + 1) (sd_max_length k) blc1 ov)
                (sd_max_length k)
                (gb_adjust (Z.to_nat ov + 1) (sd_max_length k) blc1 ov
                   (sd_max_length k))
                HEAP_SIZE ol1) as [t3 ol2] eqn:HP2.
    cbn [ts_trees set_statlen set_optlen set_blcount].
    rewrite set_tree_same.
    exact (DlNn_gb_pass2 _ _ _ _ _ _ _ _ _ _ _ HP2 Ht2).
Qed.

(** The R2 export, in the emitter side's spelling. *)
Theorem build_tree_len_nonneg : forall k s,
  (forall i, 0 <= t_len (ts_trees s k) i) ->
  forall i, 0 <= t_len (ts_trees (build_tree k s) k) i.
Proof.
  intros k s Ht.
  assert (Hd : DlNn (ts_trees s k)) by exact Ht.
  unfold build_tree. cbv zeta.
  destruct (bt_init (Z.to_nat L_CODES + 2) 0 (sd_elems k) (ts_trees s k)
              (ts_heap s) (ts_depth s) 0 (-1))
    as [[[[t0 hp0] dep0] hlen0] maxc0] eqn:E0.
  assert (H0 : DlNn t0)
    by exact (DlNn_bt_init _ _ _ _ _ _ _ _ _ _ _ _ _ E0 Hd).
  destruct (bt_force2 3%nat (sd_stree k) t0 hp0 dep0 hlen0 maxc0
              (ts_optlen s) (ts_statlen s))
    as [[[[[[t1 hp1] dep1] hlen1] maxc1] ol1] sl1] eqn:E2.
  assert (H1 : DlNn t1)
    by exact (DlNn_bt_force2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ E2 H0).
  destruct (bt_loop (Z.to_nat HEAP_SIZE)
              {| b_tree := t1;
                 b_heap := bt_heapify (Z.to_nat HEAP_SIZE) t1 dep1 hp1 hlen1
                             (hlen1 / 2);
                 b_dep := dep1; b_hlen := hlen1; b_hmax := HEAP_SIZE;
                 b_node := sd_elems k |}) as [stf|] eqn:Eloop; [|exact Ht].
  assert (Hf : DlNn (b_tree stf))
    by exact (DlNn_bt_loop _ _ _ Eloop H1).
  fold (s1_of k maxc1 stf ol1 sl1 s).
  rewrite set_tree_same.
  intro i. rewrite gen_codes_len.
  refine (DlNn_gen_bitlen k (s1_of k maxc1 stf ol1 sl1 s) _ i).
  rewrite s1_trees. exact Hf.
Qed.

Print Assumptions build_tree_blc0.
Print Assumptions build_tree_len_nonneg.
