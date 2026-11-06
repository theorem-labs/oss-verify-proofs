(* fuzz_preset, image-B walk of check_reject_clean_starved (slice BCrs): the MODEL half of its generic part.
   PURE: no machine state, no image, no allocator relation, no address, no SR conclusion. Every statement is over Z,
   lists, bool and the released pure models, so a walk of either image can cite it.
   WHAT IT HOLDS:
   - fuzz_pick (PRH_FnCheck.v:124-129 ck_djb2 / ck_pick): the hash's snoc rule, its range, and the pick's range and
     closed form (the walk's byte loop builds the hash one byte at a time and then takes a remainder).
   - the writer's text (WriterValue.wdpieces): it is never empty, so the writer always makes at least one
     fuzz_realloc call, and it makes at most wlen + 1 of them.
   - the writer run with allocation outcomes (PRH_FnWriter.v:101-130 prhWriter_put1 / prhWriter_putN / prhWriter_k):
     with every outcome accepting it is the plain WriterApp.putN; from a fresh w0 with an unreachable g_fail_at it
     makes 1..N calls and stops exactly at the first refused one; with g_fail_at set inside the run it stops at the
     first refusal or at the injected failure, whichever comes first.
   - the reader under refusal (PRH_Base.v:277-281 prh_oks with PjGrammar's G7 family): a run whose outcomes are cut
     at the j-th harness allocation returns None and makes 1..j+1 calls, exactly j+1 when nothing was refused.
   - the whole function's g_count arithmetic: cnt grows by at most ck_crcs_max and by exactly ck_crcs_growth when
     g_ran_out ends 0.
   DONORS REUSED (rule 24; file:lemma):
   - lib/Prog/WriterAppFacts.v:8 piece_lens_cons, :11 grow_calls_cons, :22 put1_fit, :179 grow_calls_nonempty.
   - lib/Prog/CrsRoom.v:38 wdpieces_nonempty, :127 crs_wcalls_le (the same bound EntSQ_Cnt.v:38 esq_wcalls states
     over wlen).
   - lib/Prog/RttModel.v:127 wcalls_pos (1 <= wcalls t p).
   - lib/Prog/WriterApp.v:37 putN_cons.
   - lib/Spec/PjGrammar.v:758 ok_upto_dec, :1346 G7_1_calls, :1350 G7_2.
   - the plain walk texts lib/Prog/CrsSegA.v:89 crs_djb2_range, CrsSegB.v:21 crsb_djb2_range, :27 crsb_pick and
     CrsRun.v:1037 crs_pk_lt prove the hash and pick facts for the plain (identical) djb2 / pick of
     check_reject_clean_starved_c.v:20-26; they are WALK files, which this file must not Require, so their two-line
     proofs are transcribed here at ck_djb2 / ck_pick and cited.
   NUMERALS: 33 and 5381 are WORD constants of fuzz_pick (fuzz.h:65-72, djb2's multiplier and seed); 2 ^ 64 and
   2 ^ 64 - 1 (PRH_Base.SIZE_MAXZ) are WORD (the 64-bit wrap and SIZE_MAX); the 1 in a put's need is LENGTH (the NUL
   byte the writer always keeps room for, preset_file.c:458); 2 ^ 62 is DERIVED (the text length under which a run's
   call count cannot exceed its length, CrsRoom.v:127).
   No address, no Admitted, no Axiom. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import
WriterSpec WriterApp WriterAppFacts.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require WriterValue PjWriteHyp CrsRoom RttModel.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import
PRH_Base PRH_Reader PRH_FnWriter PRH_FnCheck.
Import ListNotations.
Local Open Scope Z_scope.

(* the brief's N P: the fuzz_realloc calls a whole run of the pieces P makes (an abbreviation, so every statement
   below is literally the expanded term) *)
Local Notation crsN P := (length (grow_calls 0 0 (piece_lens P))).

(* ---- 1-2. fuzz_pick's hash (fuzz.h:65-72; plain check_reject_clean_starved_c.v:20-26 djb2) ---- *)

Lemma crs_djb2_snoc : forall h x c, ck_djb2 h (x ++ [c]) = (33 * ck_djb2 h x + c) mod 2 ^ 64.
Proof.
  intros h x. revert h. induction x as [|a r IH]; intros h c; [reflexivity|].
  cbn [app ck_djb2]. apply IH.
Qed.

(* transcribed from the walk text lib/Prog/CrsSegA.v:89 crs_djb2_range (= CrsSegB.v:21 crsb_djb2_range) *)
Lemma crs_djb2_range : forall x h, 0 <= h < 2 ^ 64 -> 0 <= ck_djb2 h x < 2 ^ 64.
Proof.
  intros x. induction x as [|c r IH]; intros h Hh; cbn [ck_djb2]; [exact Hh|].
  apply IH. apply Z.mod_pos_bound. lia.
Qed.

(* ---- 3-4. fuzz_pick itself (plain CrsSegB.v:27 crsb_pick, CrsRun.v:1037 crs_pk_lt) ---- *)

Lemma crs_pick_eq : forall x n, 0 < n -> ck_pick x n = ck_djb2 5381 x mod n.
Proof.
  intros x n Hn. unfold ck_pick. rewrite (proj2 (Z.eqb_neq n 0) ltac:(lia)). reflexivity.
Qed.

Lemma crs_pick_lt : forall x n, 0 < n -> 0 <= ck_pick x n < n.
Proof.
  intros x n Hn. rewrite (crs_pick_eq x n Hn). apply Z.mod_pos_bound. lia.
Qed.

(* ---- 5-6. the writer's text and its call count ---- *)

Lemma crs_wdpieces_ne : forall t p, WriterValue.wdpieces t p <> [].
Proof. intros t p. exact (CrsRoom.wdpieces_nonempty t p). Qed.

Lemma crs_wN_pos : forall t p, (1 <= crsN (WriterValue.wdpieces t p))%nat.
Proof.
  intros t p. pose proof (RttModel.wcalls_pos t p) as H. unfold PjWriteHyp.wcalls in H. lia.
Qed.

Lemma crs_wN_le : forall t p,
  PjWriteHyp.wlen t p + 1 <= 2 ^ 62 -> Z.of_nat (crsN (WriterValue.wdpieces t p)) <= PjWriteHyp.wlen t p + 1.
Proof.
  intros t p H. unfold PjWriteHyp.wlen, WriterValue.wdoc in H |- *.
  exact (CrsRoom.crs_wcalls_le (WriterValue.wdpieces t p) H).
Qed.

(* ---- the step shapes of prhWriter_put1 / prhWriter_putN (PRH_FnWriter.v:95-125) ---- *)

Lemma crs_pgrows_true : forall t c n fl cs b,
  c < Z.of_nat (length t) + Z.of_nat (length b) + 1 -> prhWriter_grows (mkW 0 t c n fl cs) b = true.
Proof.
  intros t c n fl cs b H. unfold prhWriter_grows, prhWriter_need.
  cbn [w_failed w_text w_cap]. rewrite Z.eqb_refl. cbn [andb].
  exact (proj2 (Z.ltb_lt _ _) H).
Qed.

Lemma crs_pgrows_false : forall t c n fl cs b,
  Z.of_nat (length t) + Z.of_nat (length b) + 1 <= c -> prhWriter_grows (mkW 0 t c n fl cs) b = false.
Proof.
  intros t c n fl cs b H. unfold prhWriter_grows, prhWriter_need.
  cbn [w_failed w_text w_cap]. rewrite Z.eqb_refl. cbn [andb].
  exact (proj2 (Z.ltb_ge _ _) H).
Qed.

Lemma crs_pwN_grow : forall P ok t c n fl cs b,
  c < Z.of_nat (length t) + Z.of_nat (length b) + 1 ->
  prhWriter_putN ok (mkW 0 t c n fl cs) (b :: P) =
  prhWriter_putN (tl ok) (prhWriter_put1 (hd true ok) (mkW 0 t c n fl cs) b) P.
Proof.
  intros P ok t c n fl cs b H. cbn [prhWriter_putN].
  rewrite (crs_pgrows_true t c n fl cs b H). reflexivity.
Qed.

Lemma crs_pwN_fit : forall P ok t c n fl cs b,
  Z.of_nat (length t) + Z.of_nat (length b) + 1 <= c ->
  prhWriter_putN ok (mkW 0 t c n fl cs) (b :: P) = prhWriter_putN ok (WriterApp.put1 (mkW 0 t c n fl cs) b) P.
Proof.
  intros P ok t c n fl cs b H. cbn [prhWriter_putN].
  rewrite (crs_pgrows_false t c n fl cs b H). reflexivity.
Qed.

Lemma crs_pput1_starve : forall okb t c n fl cs b,
  c < Z.of_nat (length t) + Z.of_nat (length b) + 1 -> n = fl ->
  prhWriter_put1 okb (mkW 0 t c n fl cs) b =
  mkW 1 t c ((n + 1) mod 2 ^ 64) (2 ^ 64 - 1)
    (cs ++ [newcap c (Z.of_nat (length t) + Z.of_nat (length b) + 1)]).
Proof.
  intros okb t c n fl cs b H Hn. unfold prhWriter_put1.
  rewrite (crs_pgrows_true t c n fl cs b H). unfold prhWriter_need.
  cbn [w_failed w_text w_cap w_cnt w_fail w_calls].
  rewrite (proj2 (Z.eqb_eq n fl) Hn). reflexivity.
Qed.

Lemma crs_pput1_grow : forall t c n fl cs b,
  c < Z.of_nat (length t) + Z.of_nat (length b) + 1 -> n <> fl ->
  prhWriter_put1 true (mkW 0 t c n fl cs) b =
  mkW 0 (t ++ b) (newcap c (Z.of_nat (length t) + Z.of_nat (length b) + 1)) ((n + 1) mod 2 ^ 64) fl
    (cs ++ [newcap c (Z.of_nat (length t) + Z.of_nat (length b) + 1)]).
Proof.
  intros t c n fl cs b H Hn. unfold prhWriter_put1.
  rewrite (crs_pgrows_true t c n fl cs b H). unfold prhWriter_need.
  cbn [w_failed w_text w_cap w_cnt w_fail w_calls].
  rewrite (proj2 (Z.eqb_neq n fl) Hn). reflexivity.
Qed.

Lemma crs_pput1_refuse : forall t c n fl cs b,
  c < Z.of_nat (length t) + Z.of_nat (length b) + 1 -> n <> fl ->
  prhWriter_put1 false (mkW 0 t c n fl cs) b =
  mkW 1 t c ((n + 1) mod 2 ^ 64) fl (cs ++ [newcap c (Z.of_nat (length t) + Z.of_nat (length b) + 1)]).
Proof.
  intros t c n fl cs b H Hn. unfold prhWriter_put1.
  rewrite (crs_pgrows_true t c n fl cs b H). unfold prhWriter_need.
  cbn [w_failed w_text w_cap w_cnt w_fail w_calls].
  rewrite (proj2 (Z.eqb_neq n fl) Hn). reflexivity.
Qed.

(* a failed writer makes no further call (the plain WriterApp.v:40 putN_failed, with outcomes) *)
Lemma crs_pw_failed : forall P ok st, w_failed st <> 0 -> prhWriter_putN ok st P = st.
Proof.
  induction P as [|b P IH]; intros ok st H; [reflexivity|].
  cbn [prhWriter_putN].
  assert (Hg : prhWriter_grows st b = false).
  { unfold prhWriter_grows. destruct (Z.eqb_spec (w_failed st) 0); [lia|reflexivity]. }
  rewrite Hg.
  assert (Hp : WriterApp.put1 st b = st).
  { unfold WriterApp.put1. destruct (Z.eqb_spec (w_failed st) 0); [lia|reflexivity]. }
  rewrite Hp. apply IH. exact H.
Qed.

(* ---- 7. with every outcome accepting the run is the plain one ---- *)

Lemma crs_put1_true : forall st b, prhWriter_put1 true st b = WriterApp.put1 st b.
Proof.
  intros st b. unfold prhWriter_put1, prhWriter_grows, prhWriter_need.
  destruct (Z.eqb_spec (w_failed st) 0) as [Hf|Hf]; cbn [andb]; [|reflexivity].
  destruct (Z.ltb_spec (w_cap st) (Z.of_nat (length (w_text st)) + Z.of_nat (length b) + 1)) as [Hc|Hc];
    [|reflexivity].
  unfold WriterApp.put1. cbv zeta. rewrite Hf, Z.eqb_refl. cbn [negb].
  destruct (Z.leb_spec (Z.of_nat (length (w_text st)) + Z.of_nat (length b) + 1) (w_cap st)); [lia|].
  reflexivity.
Qed.

Lemma crs_wputN_nil : forall st P, prhWriter_putN [] st P = WriterApp.putN st P.
Proof.
  intros st P. revert st. induction P as [|b P IH]; intros st; [reflexivity|].
  cbn [prhWriter_putN]. rewrite WriterApp.putN_cons.
  destruct (prhWriter_grows st b) eqn:Hg.
  - cbn [tl hd]. rewrite crs_put1_true. apply IH.
  - apply IH.
Qed.

(* ---- the workhorse: one run of puts with outcomes, from any unfailed state ---- *)

Lemma crs_hd_nth : forall (ok : list bool), hd true ok = nth 0 ok true.
Proof. intros [|b ok]; reflexivity. Qed.

Lemma crs_nth_tl : forall (ok : list bool) i, nth (S i) ok true = nth i (tl ok) true.
Proof. intros [|b ok] i; [destruct i; reflexivity|reflexivity]. Qed.

Lemma crs_pw_gen : forall P ok t c n fl cs,
  0 <= n ->
  n + Z.of_nat (length (grow_calls (Z.of_nat (length t)) c (piece_lens P))) + 1 < 2 ^ 64 ->
  exists k,
    (k <= length (grow_calls (Z.of_nat (length t)) c (piece_lens P)))%nat /\
    length (w_calls (prhWriter_putN ok (mkW 0 t c n fl cs) P)) = (length cs + k)%nat /\
    w_cnt (prhWriter_putN ok (mkW 0 t c n fl cs) P) = n + Z.of_nat k /\
    ((k = length (grow_calls (Z.of_nat (length t)) c (piece_lens P)) /\
      w_failed (prhWriter_putN ok (mkW 0 t c n fl cs) P) = 0 /\
      w_fail (prhWriter_putN ok (mkW 0 t c n fl cs) P) = fl /\
      (forall i, (i < k)%nat -> n + Z.of_nat i <> fl /\ nth i ok true = true)) \/
     (exists j, k = S j /\
       w_failed (prhWriter_putN ok (mkW 0 t c n fl cs) P) <> 0 /\
       (n + Z.of_nat j = fl \/ nth j ok true = false) /\
       (forall i, (i < j)%nat -> n + Z.of_nat i <> fl /\ nth i ok true = true) /\
       w_fail (prhWriter_putN ok (mkW 0 t c n fl cs) P) =
         (if n + Z.of_nat j =? fl then 2 ^ 64 - 1 else fl))).
Proof.
  induction P as [|b P IH]; intros ok t c n fl cs Hn Hb.
  - exists 0%nat. unfold piece_lens. cbn [map grow_calls length prhWriter_putN w_calls w_cnt w_failed w_fail].
    split; [lia|]. split; [lia|]. split; [lia|].
    left. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    intros i Hi. lia.
  - rewrite piece_lens_cons, grow_calls_cons in Hb |- *.
    destruct (Z.ltb_spec c (Z.of_nat (length t) + Z.of_nat (length b) + 1)) as [Hlt|Hge].
    + (* the put grows the buffer: one fuzz_realloc call, with its outcome *)
      rewrite (crs_pwN_grow P ok t c n fl cs b Hlt).
      cbn [length] in Hb |- *. rewrite Nat2Z.inj_succ in Hb.
      destruct (Z.eq_dec n fl) as [Hnf|Hnf].
      * (* the allocation set to fail: the plain starve *)
        rewrite (crs_pput1_starve (hd true ok) t c n fl cs b Hlt Hnf).
        set (c' := newcap c (Z.of_nat (length t) + Z.of_nat (length b) + 1)) in *.
        rewrite (crs_pw_failed P (tl ok)
          (mkW 1 t c ((n + 1) mod 2 ^ 64) (2 ^ 64 - 1) (cs ++ [c']))) by (cbn [w_failed]; lia).
        cbn [w_calls w_cnt w_failed w_fail]. rewrite length_app. cbn [length].
        rewrite (Z.mod_small (n + 1) (2 ^ 64)) by lia.
        exists 1%nat. split; [lia|]. split; [lia|]. split; [lia|].
        right. exists 0%nat. split; [reflexivity|]. split; [lia|].
        split; [left; lia|]. split; [intros i Hi; lia|].
        rewrite (proj2 (Z.eqb_eq (n + Z.of_nat 0) fl) ltac:(lia)). reflexivity.
      * destruct (hd true ok) eqn:Hh.
        -- (* the allocation is granted: the run goes on *)
           rewrite (crs_pput1_grow t c n fl cs b Hlt Hnf).
           rewrite (Z.mod_small (n + 1) (2 ^ 64)) by lia.
           set (c' := newcap c (Z.of_nat (length t) + Z.of_nat (length b) + 1)) in *.
           assert (Hlen : Z.of_nat (length (t ++ b)) = Z.of_nat (length t) + Z.of_nat (length b))
             by (rewrite length_app, Nat2Z.inj_add; reflexivity).
           destruct (IH (tl ok) (t ++ b) c' (n + 1) fl (cs ++ [c']) ltac:(lia)
             ltac:(rewrite Hlen; lia)) as (k & H1 & H2 & H3 & H4).
           rewrite Hlen in H1, H4.
           exists (S k). split; [lia|].
           split; [rewrite H2, length_app; cbn [length]; lia|].
           split; [rewrite H3, Nat2Z.inj_succ; lia|].
           destruct H4 as [(E1 & E2 & E3 & E4)|(j & E1 & E2 & E3 & E4 & E5)].
           ++ left. split; [lia|]. split; [exact E2|]. split; [exact E3|].
              intros i Hi. destruct i as [|i].
              ** split; [lia|]. rewrite <- crs_hd_nth. exact Hh.
              ** destruct (E4 i ltac:(lia)) as [F1 F2].
                 split; [rewrite Nat2Z.inj_succ; lia|]. rewrite crs_nth_tl. exact F2.
           ++ right. exists (S j). split; [lia|]. split; [exact E2|].
              split.
              { destruct E3 as [E3|E3];
                  [left; rewrite Nat2Z.inj_succ; lia | right; rewrite crs_nth_tl; exact E3]. }
              split.
              { intros i Hi. destruct i as [|i].
                - split; [lia|]. rewrite <- crs_hd_nth. exact Hh.
                - destruct (E4 i ltac:(lia)) as [F1 F2].
                  split; [rewrite Nat2Z.inj_succ; lia|]. rewrite crs_nth_tl. exact F2. }
              rewrite E5. replace (n + Z.of_nat (S j)) with (n + 1 + Z.of_nat j)
                by (rewrite Nat2Z.inj_succ; lia).
              reflexivity.
        -- (* the allocator refuses this grow: failed, the text kept, g_fail_at kept *)
           rewrite (crs_pput1_refuse t c n fl cs b Hlt Hnf).
           set (c' := newcap c (Z.of_nat (length t) + Z.of_nat (length b) + 1)) in *.
           rewrite (crs_pw_failed P (tl ok)
             (mkW 1 t c ((n + 1) mod 2 ^ 64) fl (cs ++ [c']))) by (cbn [w_failed]; lia).
           cbn [w_calls w_cnt w_failed w_fail]. rewrite length_app. cbn [length].
           rewrite (Z.mod_small (n + 1) (2 ^ 64)) by lia.
           exists 1%nat. split; [lia|]. split; [lia|]. split; [lia|].
           right. exists 0%nat. split; [reflexivity|]. split; [lia|].
           split; [right; rewrite <- crs_hd_nth; exact Hh|]. split; [intros i Hi; lia|].
           rewrite (proj2 (Z.eqb_neq (n + Z.of_nat 0) fl) ltac:(lia)). reflexivity.
    + (* the put fits: no call *)
      rewrite (crs_pwN_fit P ok t c n fl cs b ltac:(lia)).
      rewrite (put1_fit t c n fl cs b ltac:(lia)).
      assert (Hlen : Z.of_nat (length (t ++ b)) = Z.of_nat (length t) + Z.of_nat (length b))
        by (rewrite length_app, Nat2Z.inj_add; reflexivity).
      destruct (IH ok (t ++ b) c n fl cs Hn ltac:(rewrite Hlen; lia)) as (k & H1 & H2 & H3 & H4).
      rewrite Hlen in H1, H4.
      exists k. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. exact H4.
Qed.

(* ---- 8. a whole pretty write with an unreachable g_fail_at ---- *)

Lemma crs_wfull : forall P cnt ok, P <> [] -> 0 <= cnt -> cnt + Z.of_nat (crsN P) + 1 < 2 ^ 64 ->
  let st' := prhWriter_putN ok (WriterApp.w0 cnt SIZE_MAXZ) P in
  let k := prhWriter_k ok (WriterApp.w0 cnt SIZE_MAXZ) P in
  (1 <= k <= crsN P)%nat /\ WriterApp.w_cnt st' = cnt + Z.of_nat k /\ WriterApp.w_fail st' = SIZE_MAXZ /\
  (WriterApp.w_failed st' = 0 -> k = crsN P) /\
  ((forall i, (i < k)%nat -> nth i ok true = true) -> WriterApp.w_failed st' = 0) /\
  (WriterApp.w_failed st' <> 0 -> exists i, (i < k)%nat /\ nth i ok true = false).
Proof.
  intros P cnt ok HP Hcnt Hlt. cbv zeta. unfold WriterApp.w0.
  assert (E0 : Z.of_nat (length (@nil Z)) = 0) by reflexivity.
  destruct (crs_pw_gen P ok [] 0 cnt SIZE_MAXZ [] Hcnt ltac:(rewrite E0; exact Hlt))
    as (k & H1 & H2 & H3 & H4).
  rewrite E0 in H1, H4.
  assert (HNP : (1 <= length (grow_calls 0 0 (piece_lens P)))%nat).
  { pose proof (grow_calls_nonempty P HP) as Hne.
    destruct (grow_calls 0 0 (piece_lens P)) as [|z L]; [congruence|cbn [length]; lia]. }
  assert (Hk : prhWriter_k ok (mkW 0 [] 0 cnt SIZE_MAXZ []) P = k).
  { unfold prhWriter_k. rewrite H2. cbn [w_calls length]. lia. }
  rewrite Hk.
  destruct H4 as [(E1 & E2 & E3 & E4)|(j & E1 & E2 & E3 & E4 & E5)].
  - split; [lia|]. split; [exact H3|]. split; [exact E3|].
    split; [intros _; lia|]. split; [intros _; exact E2|].
    intros Hfl. exfalso. apply Hfl. exact E2.
  - assert (Hnf : cnt + Z.of_nat j <> SIZE_MAXZ).
    { unfold SIZE_MAXZ.
      assert (Hjl : (j < length (grow_calls 0 0 (piece_lens P)))%nat) by lia. lia. }
    split; [lia|]. split; [exact H3|].
    split; [rewrite E5; destruct (cnt + Z.of_nat j =? SIZE_MAXZ);
            [unfold SIZE_MAXZ; reflexivity|reflexivity]|].
    split; [intros Hz; exfalso; apply E2; exact Hz|].
    split.
    + intros Hall. exfalso. destruct E3 as [E3|E3]; [lia|].
      specialize (Hall j ltac:(lia)). congruence.
    + intros _. exists j. split; [lia|]. destruct E3 as [E3|E3]; [lia|exact E3].
Qed.

(* ---- 9. the injected write: g_fail_at inside the run ---- *)

Lemma crs_winj : forall P cnt j ok, 0 <= cnt -> (j < crsN P)%nat -> cnt + Z.of_nat (crsN P) + 1 < 2 ^ 64 ->
  let fail := cnt + Z.of_nat j in
  let st' := prhWriter_putN ok (WriterApp.w0 cnt fail) P in
  let k := prhWriter_k ok (WriterApp.w0 cnt fail) P in
  WriterApp.w_failed st' <> 0 /\ (1 <= k <= S j)%nat /\ WriterApp.w_cnt st' = cnt + Z.of_nat k /\
  ((forall i, (i < k)%nat -> nth i ok true = false -> cnt + Z.of_nat i = fail) -> k = S j).
Proof.
  intros P cnt j ok Hcnt Hj Hlt. cbv zeta. unfold WriterApp.w0.
  assert (E0 : Z.of_nat (length (@nil Z)) = 0) by reflexivity.
  destruct (crs_pw_gen P ok [] 0 cnt (cnt + Z.of_nat j) [] Hcnt ltac:(rewrite E0; exact Hlt))
    as (k & H1 & H2 & H3 & H4).
  rewrite E0 in H1, H4.
  assert (Hk : prhWriter_k ok (mkW 0 [] 0 cnt (cnt + Z.of_nat j) []) P = k).
  { unfold prhWriter_k. rewrite H2. cbn [w_calls length]. lia. }
  rewrite Hk.
  destruct H4 as [(E1 & E2 & E3 & E4)|(j' & E1 & E2 & E3 & E4 & E5)].
  - exfalso. destruct (E4 j ltac:(lia)) as [F1 _]. lia.
  - assert (Hjj : (j' <= j)%nat).
    { destruct (Nat.le_gt_cases j' j) as [H|H]; [exact H|].
      destruct (E4 j ltac:(lia)) as [F1 _]. lia. }
    split; [exact E2|]. split; [lia|]. split; [exact H3|].
    intros Hall. destruct E3 as [E3|E3]; [lia|].
    specialize (Hall j' ltac:(lia) E3). lia.
Qed.

(* ---- 10. the starved reading: the reader under a cut outcome list ---- *)

(* a failed outcome that is not the chosen failure is a refusal (PRH_Base.prh_refused) *)
Lemma crs_refused_of : forall ok cnt fail i,
  nth i ok true = false -> cnt + Z.of_nat i <> fail -> prh_refused ok cnt fail i = true.
Proof.
  intros ok cnt fail i H1 H2. unfold prh_refused. rewrite H1, (proj2 (Z.eqb_neq _ _) H2). reflexivity.
Qed.

(* ns: the run's requests (the caller binds PRH_Base.prh_ev_reqs tr), most: the ledger's g_most; every request of
   the run is within most, so a refusal sets g_ran_out (prh_oks's third conjunct) *)
Lemma crs_read_inj : forall tl ok res tr cnt j ns most ran ran',
  PjGrammar.jr_run prh_jr_strtod tl ok = (res, tr) ->
  prh_oks ok cnt (cnt + Z.of_nat j) (PjGrammar.calls tr) ns most ran ran' ->
  (forall i, (i < PjGrammar.calls tr)%nat -> nth i ns 0 <= most) ->
  (j < PjGrammar.ncalls prh_jr_strtod tl)%nat ->
  res = None /\ (1 <= PjGrammar.calls tr <= S j)%nat /\ (ran' = 0 -> PjGrammar.calls tr = S j).
Proof.
  intros tl ok res tr cnt j ns most ran ran' Hrun Hoks Hns Hj.
  destruct Hoks as (Ha & Hb & Hc).
  assert (Hfst : fst (PjGrammar.jr_run prh_jr_strtod tl ok) = res) by (rewrite Hrun; reflexivity).
  assert (Hsnd : snd (PjGrammar.jr_run prh_jr_strtod tl ok) = tr) by (rewrite Hrun; reflexivity).
  destruct (PjGrammar.ok_upto_dec ok (PjGrammar.ncalls prh_jr_strtod tl)) as [Hu|(j' & Hj' & Hf' & Hu')];
    unfold PjGrammar.ok_upto in *.
  - (* nothing refused: the reader would make all its calls, so the j-th is not refused - impossible *)
    exfalso.
    pose proof (PjGrammar.G7_1_calls prh_jr_strtod tl ok Hu) as Hcalls.
    rewrite Hsnd in Hcalls.
    specialize (Ha j ltac:(lia) ltac:(lia)).
    specialize (Hu j Hj). congruence.
  - (* the first refusal, at j': the reader stops there *)
    destruct (PjGrammar.G7_2 prh_jr_strtod tl ok j' Hj' Hf' Hu') as (Hnone & Hcalls).
    rewrite Hfst in Hnone. rewrite Hsnd in Hcalls.
    assert (Hjj : (j' <= j)%nat).
    { destruct (Nat.le_gt_cases j' j) as [H|H]; [exact H|].
      specialize (Hu' j ltac:(lia)). specialize (Ha j ltac:(lia) ltac:(lia)). congruence. }
    split; [exact Hnone|]. split; [lia|].
    intros Hran. destruct (Nat.eq_dec j' j) as [->|Hne]; [lia|].
    exfalso.
    specialize (Hc j' ltac:(lia) (crs_refused_of ok cnt (cnt + Z.of_nat j) j' Hf' ltac:(lia)) (Hns j' ltac:(lia))).
    lia.
Qed.

(* NO REFUSAL KEEPS g_ran_out (prh_oks's second conjunct): with every failure the chosen one (prh_granted), no call
   is refused, so ran' = ran - pj_write's post (DEAD-PJWRITE) and the starved reading's (DEAD-PJPARSE) *)
Lemma crs_ran_of_granted : forall ok cnt fail k ns most ran ran',
  prh_oks ok cnt fail k ns most ran ran' -> prh_granted ok cnt fail k -> ran' = ran.
Proof.
  intros ok cnt fail k ns most ran ran' (_ & [E | (_ & i & Hi & Hr & _)] & _) Hg; [exact E|].
  exfalso. unfold prh_refused in Hr. apply andb_true_iff in Hr as [H1 H2].
  apply negb_true_iff in H1. apply negb_true_iff in H2. apply Z.eqb_neq in H2.
  exact (H2 (Hg i Hi H1)).
Qed.

(* the starved reading with NO REFUSAL (prh_granted, DEAD-PJPARSE): refused at the injected failure, after exactly
   j + 1 calls, g_ran_out kept; no request bound needed *)
Lemma crs_read_inj_granted : forall tl ok res tr cnt j ns most ran ran',
  PjGrammar.jr_run prh_jr_strtod tl ok = (res, tr) ->
  prh_oks ok cnt (cnt + Z.of_nat j) (PjGrammar.calls tr) ns most ran ran' ->
  prh_granted ok cnt (cnt + Z.of_nat j) (PjGrammar.calls tr) ->
  (j < PjGrammar.ncalls prh_jr_strtod tl)%nat ->
  res = None /\ PjGrammar.calls tr = S j /\ ran' = ran.
Proof.
  intros tl ok res tr cnt j ns most ran ran' Hrun Hoks Hg Hj.
  pose proof (crs_ran_of_granted _ _ _ _ _ _ _ _ Hoks Hg) as Hran.
  destruct Hoks as (Ha & _ & _).
  assert (Hfst : fst (PjGrammar.jr_run prh_jr_strtod tl ok) = res) by (rewrite Hrun; reflexivity).
  assert (Hsnd : snd (PjGrammar.jr_run prh_jr_strtod tl ok) = tr) by (rewrite Hrun; reflexivity).
  destruct (PjGrammar.ok_upto_dec ok (PjGrammar.ncalls prh_jr_strtod tl)) as [Hu|(j' & Hj' & Hf' & Hu')];
    unfold PjGrammar.ok_upto in *.
  - exfalso.
    pose proof (PjGrammar.G7_1_calls prh_jr_strtod tl ok Hu) as Hcalls.
    rewrite Hsnd in Hcalls.
    specialize (Ha j ltac:(lia) ltac:(lia)).
    specialize (Hu j Hj). congruence.
  - destruct (PjGrammar.G7_2 prh_jr_strtod tl ok j' Hj' Hf' Hu') as (Hnone & Hcalls).
    rewrite Hfst in Hnone. rewrite Hsnd in Hcalls.
    specialize (Hg j' ltac:(lia) Hf').
    split; [exact Hnone|]. split; [lia | exact Hran].
Qed.

(* and no refusal raises g_peak: the writer's refusal peak (PRH_FnWriter.prhWriter_rpeak) is 0 under prh_granted *)
Lemma crs_rpeak_granted : forall ok Lam st P,
  prh_granted ok (WriterApp.w_cnt st) (WriterApp.w_fail st) (prhWriter_k ok st P) ->
  prhWriter_rpeak ok Lam st P = 0.
Proof.
  intros ok Lam st P Hg. unfold prhWriter_rpeak. exact (prh_refused_peak_granted _ _ _ _ _ Hg).
Qed.

(* ---- 11. the whole function's g_count arithmetic ---- *)

Lemma crs_count_total : forall (x : list Z) (took doc : Z) (t : PjTree.jv)
    (cnt c1 k1 k2 k3 k4 ran1 ran2 ran3 ran4 ran5 ran0 : Z),
  let N1 := PjWriteHyp.wcalls t true in
  let N0 := PjWriteHyp.wcalls t false in
  0 <= took -> 1 <= N1 -> 1 <= N0 ->
  (* the starved reading *)
  (took = 0 -> c1 = cnt) ->
  (took <> 0 -> cnt + 1 <= c1 <= cnt + ck_pick x took + 1 /\ (ran1 = 0 -> c1 = cnt + ck_pick x took + 1)) ->
  (* the two pretty writes *)
  (doc <> 0 -> 1 <= k1 <= N1 /\ (ran2 = 0 -> k1 = N1) /\
               1 <= k2 <= ck_pick x k1 + 1 /\ (ran3 = 0 -> k2 = ck_pick x k1 + 1) /\
               1 <= k3 <= N0 /\ (ran4 = 0 -> k3 = N0) /\
               1 <= k4 <= ck_pick x k3 + 1 /\ (ran5 = 0 -> k4 = ck_pick x k3 + 1)) ->
  (* g_ran_out only grows *)
  (ran5 = 0 -> ran4 = 0) -> (ran4 = 0 -> ran3 = 0) -> (ran3 = 0 -> ran2 = 0) -> (ran2 = 0 -> ran1 = 0) ->
  let cend := if doc =? 0 then c1 else c1 + k1 + k2 + k3 + k4 in
  let rend := if doc =? 0 then ran1 else ran5 in
  cnt <= cend <= cnt + ck_crcs_max x took doc t /\ (rend = 0 -> cend = cnt + ck_crcs_growth x took doc t).
Proof.
  intros x took doc t cnt c1 k1 k2 k3 k4 ran1 ran2 ran3 ran4 ran5 ran0. cbv zeta.
  intros Ht HN1 HN0 Hz Hnz Hd H54 H43 H32 H21.
  unfold ck_crcs_max, ck_crcs_growth.
  destruct (Z.eqb_spec doc 0) as [Hd0|Hd0]; cbv iota.
  - (* no document: only the starved reading counts *)
    destruct (Z.eqb_spec took 0) as [Ht0|Ht0]; cbv iota.
    + specialize (Hz Ht0). split; [lia|]. intros _. lia.
    + destruct (Hnz Ht0) as [Hb Hr]. split; [lia|]. intros Hran. specialize (Hr Hran). lia.
  - destruct (Hd Hd0) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
    pose proof (crs_pick_lt x k1 ltac:(lia)) as P1.
    pose proof (crs_pick_lt x k3 ltac:(lia)) as P3.
    destruct (Z.eqb_spec took 0) as [Ht0|Ht0]; cbv iota.
    + specialize (Hz Ht0). split; [lia|].
      intros Hran. assert (R4 : ran4 = 0) by (apply H54; exact Hran).
      assert (R3 : ran3 = 0) by (apply H43; exact R4).
      assert (R2 : ran2 = 0) by (apply H32; exact R3).
      specialize (A2 R2). specialize (A4 R3). specialize (A6 R4). specialize (A8 Hran).
      rewrite A2 in A4. rewrite A6 in A8. lia.
    + destruct (Hnz Ht0) as [Hb Hr]. split; [lia|].
      intros Hran. assert (R4 : ran4 = 0) by (apply H54; exact Hran).
      assert (R3 : ran3 = 0) by (apply H43; exact R4).
      assert (R2 : ran2 = 0) by (apply H32; exact R3).
      assert (R1 : ran1 = 0) by (apply H21; exact R2).
      specialize (Hr R1). specialize (A2 R2). specialize (A4 R3). specialize (A6 R4). specialize (A8 Hran).
      rewrite A2 in A4. rewrite A6 in A8. lia.
Qed.
