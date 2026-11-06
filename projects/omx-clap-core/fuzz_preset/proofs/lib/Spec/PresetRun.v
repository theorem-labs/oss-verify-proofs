(* omx-clap-core/fuzz_preset: P8 part B -- the harness's heap events, call by call, and the live count of a class
   at every position of the calls.

   THE HARNESS (fuzz/fuzz_preset.c and fuzz/alloc.c as merged by omx-clap-core #102). LLVMFuzzerTestOneInput
   (:800-836) first runs check_no_overread (:524-559). It makes three padded () copies of the input (:510-521, :527;
   malloc (n + FUZZ_PAD), the request of fuzz.h's fuzz_copy) and reads them with parse_noting (:499-507) while memory
   has not run out (out_of_memory (), :79-82; the readings at :531-536). Each of these three readings may meet a REAL
   refusal (the C library's malloc / realloc returns NULL) at any of its allocations. The reader then refuses (pj_parse
   frees its partial tree, src/preset_file.c:296-309) and memory has run out (alloc.c refused (), :70-78, for a request
   at most fuzz_alloc_most's bound, PJ_ALLOC_BOUND (size) set at :810), so the LATER READINGS ARE NOT MADE. The trees
   are compared only when none ran out (same (): no allocation). Then pj_free (&a1), pj_free (&a2), pj_free (&a0)
   (:552-554; a refused or unmade tree is empty: no frees), and free (one), free (two), free (nul) (:555-557). A
   reading that ran out ENDS THE CALL (:558, :811-812). Otherwise everything after check_no_overread is as in
   PresetReqAt.hrun. A refusal at any OTHER allocation also ends the call, with no abort; P8 proves that those do not
   happen, so the model grants every allocation outside the three readings. A reading's grants are okof o: all
   (None), or all but its j-th allocation (Some j, PresetReqAt.okk j). It RUNS OUT (ranout) when j is below the
   all-granted reading's call count: it meets the refusal (PjGrammar.G7_2); at a larger j it is the all-granted
   reading (G7_1).

   THE MODEL. call_evs sm x o1 o2 o0 is one LLVMFuzzerTestOneInput on the bytes x, the three readings' grants o1 o2 o0
   (call_evs_none: the all-granted call is PresetReqAt.hrun). When a reading runs out, the later readings and
   everything after check_no_overread are left out (call_evs_blocks: one form per case). call_cons flags its events:
   false exactly on the events of the readings' parse_evs. target_run calls the harness k <= 4 times on the same
   bytes: hruns / hcons.

   WHAT IS PROVED.
   - call_okf, call_closed, hruns_okf: every removal of a call finds its block live, and a call leaves nothing live,
     so the calls compose.
   - hruns_live: at every position of the calls, for a class f (a predicate on requests),
       cnt f live <= KH + max (3 A) (A + 2 B + KB)  =  max (3 A + 3) (A + 2 B + 5),   KH = 3, KB = 2,
     where A bounds the f-requests of ONE reading of x under ANY grants, and B those of the trace of the file's tree
     and of its rewritten copy (copy_set). The two terms bound the two peaks:
       3 A + 3:    check_no_overread after its third reading: three trees and the three padded () copies;
       A + 2 B + 5: the rewrite's read-back: the doc tree (A), the copy after pj_set (B, plus at most 4 requests pj_set
                    makes), the read-back tree (B) and the writer's buffer (1). The pretty round trip's read-back is
                    bounded by A + 2 B + 2 (doc, copy, read-back, writer text, rendered text).
     The other segments have smaller bounds: the main parse and expected ()'s scratch A + 1; the starved parse 2 A; the
     starved writes A + 1. A call that a reading cuts holds at most the copies and the readings made: 3 + 2 A.
   - hfrees: the requests an event list frees, in order (a pj_free, HBulk L, frees L in pj_free's post-order:
     PresetReqAt.pj_frees / fo); the writer's and rendered ()'s chains free their capacities but the last, and both
     come before the round trip's parse (rt_text_frees).

   The peak framework (pkR, nprodR and their lemmas) is PresetReqAtClass.v's (pk, nprod, ...), copied under new names:
   PresetReqAtClass.v imports lib/A/ClassConsDef, which this file does not.

   Nothing here is a function's proof (rule 24). *)
From Stdlib Require Import ZArith List Lia Bool Arith Permutation.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import WriterSpec WriterValue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import
  PjTree PjGrammar PjRoundTrip PresetReqAt PresetReqAtNoMiss.
Import ListNotations.
Local Open Scope Z_scope.

(* ================================================================ peaks and productions
   (copied from PresetReqAtClass.v, names suffixed R; the source name is given with each) *)

(* PresetReqAtClass.pk: the largest count of f over the states s, hstep s e1, ... *)
Fixpoint pkR (f : Z -> bool) (s : list Z) (es : list hev) : nat :=
  match es with
  | [] => cnt f s
  | e :: r => Nat.max (cnt f s) (pkR f (hstep s e) r)
  end.

(* PresetReqAtClass.prod_ev *)
Definition prod_evR (f : Z -> bool) (e : hev) : nat :=
  match e with
  | HMal n => if f n then 1%nat else 0%nat
  | HRe _ n => if f n then 1%nat else 0%nat
  | _ => 0%nat
  end.

(* PresetReqAtClass.nprod: the f-requests an event list makes *)
Fixpoint nprodR (f : Z -> bool) (es : list hev) : nat :=
  match es with [] => 0%nat | e :: r => (prod_evR f e + nprodR f r)%nat end.

(* PresetReqAtClass.nprod_app *)
Lemma nprodR_app : forall f a b, nprodR f (a ++ b) = (nprodR f a + nprodR f b)%nat.
Proof. intros f a b. induction a as [|e a IH]; [reflexivity|]. cbn [app nprodR]. rewrite IH. lia. Qed.

(* PresetReqAtClass.prod_ev_le *)
Lemma prod_evR_le : forall f e, (prod_evR f e <= 1)%nat.
Proof. intros f [n | m n | n | L]; cbn [prod_evR]; try lia; destruct (f n); lia. Qed.

(* PresetReqAtClass.nprod_len *)
Lemma nprodR_len : forall f es, (nprodR f es <= length es)%nat.
Proof.
  intros f es. induction es as [|e r IH]; [cbn; lia|].
  cbn [nprodR length]. pose proof (prod_evR_le f e). lia.
Qed.

(* PresetReqAtClass.cnt_cons_eq *)
Lemma cnt_cons_eqR : forall f z L, cnt f (z :: L) = ((if f z then 1 else 0) + cnt f L)%nat.
Proof. intros f z L. unfold cnt. simpl. destruct (f z); reflexivity. Qed.

(* PresetReqAtClass.cnt_hstep *)
Lemma cnt_hstepR : forall f s e, (cnt f (hstep s e) <= cnt f s + prod_evR f e)%nat.
Proof.
  intros f s [n | m n | n | L]; cbn [hstep prod_evR].
  - rewrite cnt_cons_eqR. destruct (f n); lia.
  - rewrite cnt_cons_eqR. pose proof (subm_cnt f _ _ (rm1_subm m s)). destruct (f n); lia.
  - pose proof (subm_cnt f _ _ (rm1_subm n s)). lia.
  - pose proof (subm_cnt f _ _ (rmall_subm L s)). lia.
Qed.

(* PresetReqAtClass.pk_le *)
Lemma pkR_le : forall f es s, (pkR f s es <= cnt f s + nprodR f es)%nat.
Proof.
  intros f es. induction es as [|e r IH]; intros s; cbn [pkR nprodR]; [lia|].
  pose proof (IH (hstep s e)). pose proof (cnt_hstepR f s e). lia.
Qed.

(* PresetReqAtClass.pk_prefix *)
Lemma pkR_prefix : forall f es s j, (cnt f (hlive_from s (firstn j es)) <= pkR f s es)%nat.
Proof.
  intros f es. induction es as [|e r IH]; intros s j.
  - rewrite firstn_nil, hlive_from_nil. cbn [pkR]. lia.
  - destruct j as [|j]; cbn [firstn pkR].
    + rewrite hlive_from_nil. lia.
    + rewrite hlive_from_cons. pose proof (IH (hstep s e) j). lia.
Qed.

(* PresetReqAtClass.pk_app *)
Lemma pkR_app : forall f a b s, pkR f s (a ++ b) = Nat.max (pkR f s a) (pkR f (hlive_from s a) b).
Proof.
  intros f a. induction a as [|e r IH]; intros b s.
  - cbn [app pkR]. rewrite hlive_from_nil. destruct b as [|e b]; cbn [pkR]; lia.
  - cbn [app pkR]. rewrite IH, hlive_from_cons. lia.
Qed.

(* PresetReqAtClass.cnt_hlive_nprod *)
Lemma cnt_hlive_nprodR : forall f es, (cnt f (hlive es) <= nprodR f es)%nat.
Proof.
  intros f es. pose proof (pkR_prefix f es [] (length es)) as H. rewrite firstn_all in H.
  pose proof (pkR_le f es []) as H2. unfold hlive. cbn [cnt List.filter length] in H2. lia.
Qed.

(* PresetReqAtClass.nprod_parse *)
Lemma nprodR_parse : forall f sm y ok, nprodR f (parse_evs sm y ok) = nprodR f (rd_hevs (rtr sm ok y)).
Proof.
  intros f sm y ok. unfold parse_evs. rewrite nprodR_app.
  destruct (fst (jr_run sm y ok)); cbn [nprodR prod_evR]; lia.
Qed.

(* PresetReqAtClass.rd_hev_len *)
Lemma rd_hev_lenR : forall e, (length (rd_hev e) <= 1)%nat.
Proof. intros [n | [|m] n | n | n]; cbn; lia. Qed.

(* PresetReqAtClass.rd_hevs_len *)
Lemma rd_hevs_lenR : forall l, (length (rd_hevs l) <= length l)%nat.
Proof.
  induction l as [|e l IH]; [cbn; lia|]. rewrite rd_hevs_cons, length_app. cbn [length].
  pose proof (rd_hev_lenR e). lia.
Qed.

(* PresetReqAtClass.set_evs_nprod: pj_string and pj_set make at most 4 requests *)
Lemma set_evs_nprodR : forall f ms, (nprodR f (set_evs ms) <= 4)%nat.
Proof.
  intros f ms. pose proof (nprodR_len f (set_evs ms)) as H. unfold set_evs in *. cbn [length] in H.
  destruct (mfind ms) as [u|].
  - cbn [length] in H. lia.
  - assert (Hg : (length (grow_ev true (length ms) (ncap (length ms))) <= 2)%nat).
    { unfold grow_ev. destruct (Nat.ltb _ _); cbn; lia. }
    pose proof (rd_hevs_lenR (grow_ev true (length ms) (ncap (length ms)) ++ [EAlloc (S (length MOD_KEY))])).
    rewrite length_app in *. cbn [length] in *. lia.
Qed.

(* PresetReqAtClass.pk_mono *)
Lemma pkR_mono : forall f es s s', subm s s' -> (pkR f s es <= pkR f s' es)%nat.
Proof.
  intros f es. induction es as [|e r IH]; intros s s' H; cbn [pkR].
  - apply subm_cnt. exact H.
  - pose proof (subm_cnt f _ _ H). pose proof (IH _ _ (hstep_mono e _ _ H)). lia.
Qed.

(* PresetReqAtClass.pk_base *)
Lemma pkR_base : forall f es a s, (pkR f (a ++ s) es <= pkR f a es + cnt f s)%nat.
Proof.
  intros f es. induction es as [|e r IH]; intros a s; cbn [pkR].
  - rewrite cnt_app. lia.
  - rewrite cnt_app. pose proof (pkR_mono f r _ _ (hstep_le e a s)). pose proof (IH (hstep a e) s). lia.
Qed.

(* PresetReqAtClass.pk_base0 *)
Lemma pkR_base0 : forall f es s, (pkR f s es <= pkR f [] es + cnt f s)%nat.
Proof. intros f es s. exact (pkR_base f es [] s). Qed.

(* PresetReqAtClass.cnt_live_le *)
Lemma cnt_live_leR : forall f s es, (cnt f (hlive_from s es) <= cnt f s + nprodR f es)%nat.
Proof.
  intros f s es. pose proof (pkR_prefix f es s (length es)) as H. rewrite firstn_all in H.
  pose proof (pkR_le f es s). lia.
Qed.

(* PresetReqAtClass.cnt_live_pk *)
Lemma cnt_live_pkR : forall f s es, (cnt f (hlive_from s es) <= pkR f s es)%nat.
Proof. intros f s es. pose proof (pkR_prefix f es s (length es)) as H. rewrite firstn_all in H. exact H. Qed.

(* ---------------------------------------------------------------- one buffer at a time *)

(* PresetReqAtClass.pk_chain_h *)
Lemma pkR_chain_h : forall f cs hd old, Forall (fun c => 0 < c) cs -> 0 < old ->
  (pkR f [(old + hd)%Z] (chain hd old cs) <= 1)%nat.
Proof.
  intros f cs. induction cs as [|c cs IH]; intros hd old Hall Hold.
  - cbn [chain pkR]. rewrite cnt_cons_eqR. cbn [cnt List.filter length]. destruct (f (old + hd)); lia.
  - apply Forall_cons_iff in Hall as [Hc Hall].
    cbn [chain]. rewrite (proj2 (Z.eqb_neq old 0)) by lia. cbn [pkR hstep]. rewrite rm1_cons_eq.
    pose proof (IH hd c Hall Hc). rewrite cnt_cons_eqR. cbn [cnt List.filter length].
    destruct (f (old + hd)); lia.
Qed.

(* PresetReqAtClass.pk_chain0 *)
Lemma pkR_chain0 : forall f cs hd, Forall (fun c => 0 < c) cs -> (pkR f [] (chain hd 0 cs) <= 1)%nat.
Proof.
  intros f [|c cs] hd Hall; [cbn; lia|].
  apply Forall_cons_iff in Hall as [Hc Hall].
  cbn [chain]. rewrite Z.eqb_refl. cbn [pkR hstep]. cbn [cnt List.filter length].
  pose proof (pkR_chain_h f cs hd c Hall Hc). lia.
Qed.

(* PresetReqAtClass.pk_w_evs *)
Lemma pkR_w_evs : forall f t p s, (pkR f s (w_evs t p) <= 1 + cnt f s)%nat.
Proof.
  intros f t p s. pose proof (pkR_base0 f (w_evs t p) s).
  pose proof (pkR_chain0 f (wcaps t p) HEAD (wcaps_pos t p)). unfold w_evs in *. lia.
Qed.

(* PresetReqAtClass.pk_r_evs *)
Lemma pkR_r_evs : forall f t p s, (pkR f s (r_evs t p) <= 1 + cnt f s)%nat.
Proof.
  intros f t p s. pose proof (pkR_base0 f (r_evs t p) s).
  pose proof (pkR_chain0 f (rcaps t p) 0 (rcaps_pos t p)). unfold r_evs in *. lia.
Qed.

(* PresetReqAtClass.pk_w_starved *)
Lemma pkR_w_starved : forall f t p k s, (pkR f s (w_starved t p k) <= 1 + cnt f s)%nat.
Proof.
  intros f t p k s. unfold w_starved. rewrite pkR_app.
  pose proof (pkR_base0 f (chain HEAD 0 (firstn k (wcaps t p))) s) as H1.
  pose proof (pkR_chain0 f (firstn k (wcaps t p)) HEAD (firstn_forall _ _ _ k (wcaps_pos t p))) as H2.
  pose proof (cnt_live_pkR f s (chain HEAD 0 (firstn k (wcaps t p)))) as H3.
  pose proof (pkR_le f (match k with O => [] | S _ => [HFr (last (firstn k (wcaps t p)) 0 + HEAD)] end)
                (hlive_from s (chain HEAD 0 (firstn k (wcaps t p))))) as H4.
  assert (Ht : nprodR f (match k with O => [] | S _ => [HFr (last (firstn k (wcaps t p)) 0 + HEAD)] end) = 0%nat)
    by (destruct k; reflexivity).
  lia.
Qed.

(* PresetReqAtClass.cnt_tblk *)
Lemma cnt_tblkR : forall f t, (cnt f (tblk t) <= nprodR f (rd_hevs (ttrace t)))%nat.
Proof. intros f t. rewrite <- (cnt_perm f _ _ (ttrace_blocks t)). apply cnt_hlive_nprodR. Qed.

(* ---------------------------------------------------------------- the harness's segments *)

(* PresetReqAtClass.pk_rt_text *)
Lemma pkR_rt_text : forall f sm t p s, pj_wf sm t ->
  (pkR f s (rt_text sm t p) <= 2 + nprodR f (rd_hevs (ttrace t)) + cnt f s)%nat.
Proof.
  intros f sm t p s Hw. unfold rt_text. rewrite (parse_wf sm t p Hw).
  destruct (w_evs_ok t p s) as [_ W2].
  set (W := last (wcaps t p) 0 + HEAD) in *.
  destruct (r_evs_ok t p (W :: s)) as [_ R2].
  set (R := last (rcaps t p) 0 + 0) in *.
  rewrite pkR_app, W2, pkR_app, R2.
  pose proof (pkR_w_evs f t p s). pose proof (pkR_r_evs f t p (W :: s)).
  pose proof (pkR_le f (rd_hevs (ttrace t) ++ r_free t p ++ w_free t p) (R :: W :: s)) as P.
  assert (F1 : nprodR f (r_free t p) = 0%nat) by reflexivity.
  assert (F2 : nprodR f (w_free t p) = 0%nat) by reflexivity.
  rewrite !nprodR_app, F1, F2 in P.
  rewrite !cnt_cons_eqR in *. destruct (f W); destruct (f R); lia.
Qed.

(* PresetReqAtClass.pk_rw *)
Lemma pkR_rw : forall f sm ms Lc, pj_wf sm (JObj ms) ->
  (pkR f Lc (rw_evs sm ms) <= cnt f Lc + 5 + nprodR f (rd_hevs (ttrace (copy_set ms))))%nat.
Proof.
  intros f sm ms Lc Hw. pose proof (wf_copy sm ms Hw) as Hc.
  unfold rw_evs. rewrite (parse_wf sm (copy_set ms) true Hc).
  rewrite pkR_app.
  pose proof (pkR_le f (set_evs ms) Lc). pose proof (set_evs_nprodR f ms).
  pose proof (cnt_live_leR f Lc (set_evs ms)).
  set (C := hlive_from Lc (set_evs ms)) in *.
  destruct (w_evs_ok (copy_set ms) true C) as [_ W2].
  set (W := last (wcaps (copy_set ms) true) 0 + HEAD) in *.
  rewrite pkR_app, W2.
  pose proof (pkR_w_evs f (copy_set ms) true C).
  pose proof (pkR_le f (rd_hevs (ttrace (copy_set ms)) ++ w_free (copy_set ms) true ++
                        [HBulk (fo (copy_set ms))]) (W :: C)) as P.
  assert (F2 : nprodR f (w_free (copy_set ms) true) = 0%nat) by reflexivity.
  assert (F3 : nprodR f [HBulk (fo (copy_set ms))] = 0%nat) by reflexivity.
  rewrite !nprodR_app, F2, F3 in P.
  rewrite !cnt_cons_eqR in *. destruct (f W); lia.
Qed.

(* PresetReqAtClass.pk_starved_write *)
Lemma pkR_starved_write : forall f x t p rest s,
  (pkR f s rest <= 1 + cnt f s)%nat -> hlive_from s rest = s ->
  (pkR f s (starved_write x t p rest) <= 1 + cnt f s)%nat.
Proof.
  intros f x t p rest s Hr Hl. unfold starved_write.
  destruct (w_pair_ok t p s) as [_ P2].
  rewrite app_assoc, pkR_app, P2.
  assert (Hp : (pkR f s (w_evs t p ++ w_free t p) <= 1 + cnt f s)%nat).
  { rewrite pkR_app. destruct (w_evs_ok t p s) as [_ W2]. rewrite W2.
    pose proof (pkR_w_evs f t p s).
    pose proof (pkR_le f (w_free t p) (last (wcaps t p) 0 + HEAD :: s)) as P.
    assert (F2 : nprodR f (w_free t p) = 0%nat) by reflexivity. rewrite F2 in P.
    rewrite cnt_cons_eqR in P. destruct (f (last (wcaps t p) 0 + HEAD)); lia. }
  destruct (wcalls t p) as [|n].
  - cbn [pkR]. lia.
  - rewrite (pkR_app f (w_starved t p (pick x (S n))) rest s), w_starved_live.
    pose proof (pkR_w_starved f t p (pick x (S n)) s). lia.
Qed.

(* PresetReqAtClass.pk_starved_writes *)
Lemma pkR_starved_writes : forall f x t s, (pkR f s (starved_writes x t) <= 1 + cnt f s)%nat.
Proof.
  intros f x t s. unfold starved_writes.
  destruct (starved_write_ok x t false [] s I eq_refl) as [_ A2].
  apply pkR_starved_write; [|exact A2].
  apply pkR_starved_write; [cbn [pkR]; lia | reflexivity].
Qed.

(* ================================================================ the constants of hruns_live *)

(* the three padded () copies live at check_no_overread's peak *)
Definition KH : nat := 3%nat.
(* KH + KB = 5: at the rewrite's read-back, the writer's buffer and the at most 4 requests of pj_string / pj_set *)
Definition KB : nat := 2%nat.

(* ================================================================ the harness's calls (#102) *)

Section Run2.

Variable sm : list Z -> Z * Z.

(* a P1 reading's grants: all granted, or the j-th allocation refused (PresetReqAt.okk j) *)
Definition okof (o : option nat) : list bool := match o with None => [] | Some j => okk j end.

(* a P1 reading RUNS OUT (memory runs out during it): its j-th allocation is refused and the all-granted reading makes
   more than j allocations, so the reading meets the refusal (PjGrammar.G7_2; at j >= calls, G7_1: the reading is the
   all-granted one) *)
Definition ranout (x : list Z) (o : option nat) : bool :=
  match o with None => false | Some j => Nat.ltb j (calls (rtr sm [] x)) end.

(* pj_free (&a) of a P1 reading (:552-554): its tree's blocks, in pj_free's order; a refused tree is empty *)
Definition p1_tfree (x : list Z) (o : option nat) : list hev :=
  match fst (jr_run sm x (okof o)) with Some _ => [HBulk (pj_frees sm (okof o) x)] | None => [] end.

(* after expected (): the refused path (check_reject_clean_starved's parse), or the accepted path
   (check_round_trip, check_reject_clean_starved, pj_free (&doc)), as in PresetReqAt.hrun *)
Definition call_tail (x : list Z) : list hev :=
  match fst (jr_run sm x []) with
  | None => starved_parse sm x (calls (rtr sm [] x))
  | Some t => round_trip sm t ++ starved_parse sm x (calls (rtr sm [] x)) ++ starved_writes x t ++
              [HBulk (pj_frees sm [] x)]
  end.

(* LLVMFuzzerTestOneInput after check_no_overread (:814-836): parse_noting's pj_parse (:817), expected ()'s scratch
   (:362, :373), the tail *)
Definition call_rest (x : list Z) : list hev :=
  let n := Z.of_nat (length x) in
  parse_evs sm x [] ++ [HMal (n + 1); HFr (n + 1)] ++ call_tail x.

(* one LLVMFuzzerTestOneInput (:800-836) on x, the P1 readings' grants o1 o2 o0. check_no_overread (:524-559): the
   three padded () copies (:527), the readings made while memory has not run out (:531-536), the trees' pj_free
   (:552-554), the copies' free (:555-557). A reading that runs out stops the later readings and ends the call
   (:558, :811-812); its own tree is empty (G7_2), so its pj_free frees nothing and is left out. When none runs out,
   the rest as hrun sm x. *)
Definition call_evs (x : list Z) (o1 o2 o0 : option nat) : list hev :=
  let n := Z.of_nat (length x) in
  if MAXB <? n then []
  else if ranout x o1 then
    [HMal (n + FUZZ_PAD); HMal (n + FUZZ_PAD); HMal (n + FUZZ_PAD)] ++
    parse_evs sm x (okof o1) ++
    [HFr (n + FUZZ_PAD); HFr (n + FUZZ_PAD); HFr (n + FUZZ_PAD)]
  else if ranout x o2 then
    [HMal (n + FUZZ_PAD); HMal (n + FUZZ_PAD); HMal (n + FUZZ_PAD)] ++
    parse_evs sm x (okof o1) ++ parse_evs sm x (okof o2) ++
    p1_tfree x o1 ++
    [HFr (n + FUZZ_PAD); HFr (n + FUZZ_PAD); HFr (n + FUZZ_PAD)]
  else
    [HMal (n + FUZZ_PAD); HMal (n + FUZZ_PAD); HMal (n + FUZZ_PAD)] ++
    parse_evs sm x (okof o1) ++ parse_evs sm x (okof o2) ++ parse_evs sm x (okof o0) ++
    p1_tfree x o1 ++ p1_tfree x o2 ++ p1_tfree x o0 ++
    [HFr (n + FUZZ_PAD); HFr (n + FUZZ_PAD); HFr (n + FUZZ_PAD)] ++
    (if ranout x o0 then [] else call_rest x).

Definition flags (b : bool) (es : list hev) : list bool := map (fun _ => b) es.

(* consumer flag of each event of call_evs: false exactly for the events of the P1 parse_evs segments made *)
Definition call_cons (x : list Z) (o1 o2 o0 : option nat) : list bool :=
  let n := Z.of_nat (length x) in
  if MAXB <? n then []
  else if ranout x o1 then
    flags true [HMal (n + FUZZ_PAD); HMal (n + FUZZ_PAD); HMal (n + FUZZ_PAD)] ++
    flags false (parse_evs sm x (okof o1)) ++
    flags true [HFr (n + FUZZ_PAD); HFr (n + FUZZ_PAD); HFr (n + FUZZ_PAD)]
  else if ranout x o2 then
    flags true [HMal (n + FUZZ_PAD); HMal (n + FUZZ_PAD); HMal (n + FUZZ_PAD)] ++
    flags false (parse_evs sm x (okof o1)) ++ flags false (parse_evs sm x (okof o2)) ++
    flags true (p1_tfree x o1 ++ [HFr (n + FUZZ_PAD); HFr (n + FUZZ_PAD); HFr (n + FUZZ_PAD)])
  else
    flags true [HMal (n + FUZZ_PAD); HMal (n + FUZZ_PAD); HMal (n + FUZZ_PAD)] ++
    flags false (parse_evs sm x (okof o1)) ++ flags false (parse_evs sm x (okof o2)) ++
    flags false (parse_evs sm x (okof o0)) ++
    flags true (p1_tfree x o1 ++ p1_tfree x o2 ++ p1_tfree x o0 ++
                [HFr (n + FUZZ_PAD); HFr (n + FUZZ_PAD); HFr (n + FUZZ_PAD)] ++
                (if ranout x o0 then [] else call_rest x)).

Lemma call_cons_len : forall x o1 o2 o0, length (call_cons x o1 o2 o0) = length (call_evs x o1 o2 o0).
Proof.
  intros x o1 o2 o0. unfold call_cons, call_evs. cbv zeta.
  destruct (MAXB <? Z.of_nat (length x)); [reflexivity|].
  destruct (ranout x o1); [|destruct (ranout x o2)]; cbv iota;
    unfold flags; rewrite ?length_app, ?length_map, ?length_app; lia.
Qed.

(* the old model is the all-granted call *)
Lemma call_evs_none : forall x, call_evs x None None None = hrun sm x.
Proof. intros x. reflexivity. Qed.

(* target_run's calls on the same bytes, the k-th with the readings' grants of the k-th triple *)
Definition hruns (x : list Z) (os : list (option nat * option nat * option nat)) : list hev :=
  concat (map (fun o => let '(o1, o2, o0) := o in call_evs x o1 o2 o0) os).

Definition hcons (x : list Z) (os : list (option nat * option nat * option nat)) : list bool :=
  concat (map (fun o => let '(o1, o2, o0) := o in call_cons x o1 o2 o0) os).

Lemma hruns_cons : forall x o1 o2 o0 os, hruns x ((o1, o2, o0) :: os) = call_evs x o1 o2 o0 ++ hruns x os.
Proof. intros x o1 o2 o0 os. reflexivity. Qed.

Lemma hcons_len : forall x os, length (hcons x os) = length (hruns x os).
Proof.
  intros x os. induction os as [|[[o1 o2] o0] os IH]; [reflexivity|].
  change (length (call_cons x o1 o2 o0 ++ hcons x os) = length (call_evs x o1 o2 o0 ++ hruns x os)).
  rewrite !length_app, call_cons_len, IH. reflexivity.
Qed.

(* call_evs in blocks, one form per case: the copies, the readings made, the frees of check_no_overread, the rest
   when no reading ran out *)
Lemma call_evs_blocks : forall x o1 o2 o0, call_evs x o1 o2 o0 =
  if MAXB <? Z.of_nat (length x) then []
  else if ranout x o1 then
    [HMal (Z.of_nat (length x) + FUZZ_PAD); HMal (Z.of_nat (length x) + FUZZ_PAD);
     HMal (Z.of_nat (length x) + FUZZ_PAD)] ++
    parse_evs sm x (okof o1) ++
    [HFr (Z.of_nat (length x) + FUZZ_PAD); HFr (Z.of_nat (length x) + FUZZ_PAD);
     HFr (Z.of_nat (length x) + FUZZ_PAD)]
  else if ranout x o2 then
    [HMal (Z.of_nat (length x) + FUZZ_PAD); HMal (Z.of_nat (length x) + FUZZ_PAD);
     HMal (Z.of_nat (length x) + FUZZ_PAD)] ++
    (parse_evs sm x (okof o1) ++ parse_evs sm x (okof o2)) ++
    (p1_tfree x o1 ++
     [HFr (Z.of_nat (length x) + FUZZ_PAD); HFr (Z.of_nat (length x) + FUZZ_PAD);
      HFr (Z.of_nat (length x) + FUZZ_PAD)])
  else
    [HMal (Z.of_nat (length x) + FUZZ_PAD); HMal (Z.of_nat (length x) + FUZZ_PAD);
     HMal (Z.of_nat (length x) + FUZZ_PAD)] ++
    (parse_evs sm x (okof o1) ++ parse_evs sm x (okof o2) ++ parse_evs sm x (okof o0)) ++
    (p1_tfree x o1 ++ p1_tfree x o2 ++ p1_tfree x o0 ++
     [HFr (Z.of_nat (length x) + FUZZ_PAD); HFr (Z.of_nat (length x) + FUZZ_PAD);
      HFr (Z.of_nat (length x) + FUZZ_PAD)]) ++
    (if ranout x o0 then [] else call_rest x).
Proof.
  intros x o1 o2 o0. unfold call_evs. cbv zeta.
  destruct (MAXB <? Z.of_nat (length x)); [reflexivity|].
  destruct (ranout x o1); [reflexivity|].
  destruct (ranout x o2); cbv iota; rewrite <- ?app_assoc; reflexivity.
Qed.

(* ================================================================ the starved parse is refused *)

Lemma pick_lt : forall x n, (0 < n)%nat -> (pick x n < n)%nat.
Proof.
  intros x [|n] H; [lia|]. unfold pick. cbv beta iota.
  pose proof (Z.mod_pos_bound (pick_h x) (Z.of_nat (S n)) ltac:(lia)) as Hm.
  set (r := pick_h x mod Z.of_nat (S n)) in *. lia.
Qed.

Lemma okk_false : forall j, nth j (okk j) true = false.
Proof. unfold okk. induction j as [|j IH]; cbn [repeat app nth]; [reflexivity | exact IH]. Qed.

Lemma okk_true : forall j i, (i < j)%nat -> nth i (okk j) true = true.
Proof.
  unfold okk. induction j as [|j IH]; intros i Hi; [lia|].
  destruct i as [|i]; cbn [repeat app nth]; [reflexivity|]. apply IH. lia.
Qed.

(* check_reject_clean_starved's parse: its pick-th allocation fails, and pick < took, so the reader refuses
   (PjGrammar.G7_2) *)
Lemma starved_refused : forall x k, calls (rtr sm [] x) = S k ->
  fst (jr_run sm x (okk (pick x (S k)))) = None.
Proof.
  intros x k Hc.
  assert (Hl : (pick x (S k) < ncalls sm x)%nat).
  { unfold ncalls. unfold rtr in Hc. rewrite Hc. apply pick_lt. lia. }
  exact (proj1 (G7_2 sm x (okk (pick x (S k))) (pick x (S k)) Hl (okk_false _) (fun i Hi => okk_true _ i Hi))).
Qed.

(* a P1 reading that runs out is refused (PjGrammar.G7_2) *)
Lemma ranout_refused : forall x o, ranout x o = true -> fst (jr_run sm x (okof o)) = None.
Proof.
  intros x [j|] H; [|discriminate]. unfold ranout in H. apply Nat.ltb_lt in H.
  assert (Hl : (j < ncalls sm x)%nat) by exact H.
  exact (proj1 (G7_2 sm x (okk j) j Hl (okk_false j) (fun i Hi => okk_true j i Hi))).
Qed.

(* so it leaves nothing live *)
Lemma ranout_pacc : forall x o, ranout x o = true -> pacc sm x (okof o) = [].
Proof. intros x o H. unfold pacc. rewrite (ranout_refused x o H). reflexivity. Qed.

Lemma starved_ok : forall x s,
  okf s (starved_parse sm x (calls (rtr sm [] x))) /\ hlive_from s (starved_parse sm x (calls (rtr sm [] x))) = s.
Proof.
  intros x s. unfold starved_parse. destruct (calls (rtr sm [] x)) as [|k] eqn:Ec.
  - split; [exact I | reflexivity].
  - destruct (parse_ok sm x (okk (pick x (S k))) s) as [Q1 Q2].
    split; [exact Q1|]. rewrite Q2. unfold pacc. rewrite (starved_refused x k Ec). reflexivity.
Qed.

(* ================================================================ every removal hits, and a call is closed *)

Lemma tfree_ok : forall x o S s, Permutation S (pacc sm x (okof o) ++ s) ->
  okf S (p1_tfree x o) /\ Permutation (hlive_from S (p1_tfree x o)) s.
Proof.
  intros x o S s. unfold p1_tfree, pacc.
  destruct (fst (jr_run sm x (okof o))) as [t|]; intros H.
  - assert (H' : Permutation S (pj_frees sm (okof o) x ++ s)).
    { apply (Permutation_trans H). apply Permutation_app_tail. apply Permutation_sym. apply pj_frees_blocks. }
    destruct (bulk_ok _ S s H') as [B1 B2]. split.
    + cbn [okf]. split; [exact B1 | exact I].
    + rewrite hlive_from_cons, hlive_from_nil. exact B2.
  - split; [exact I|]. rewrite hlive_from_nil. exact H.
Qed.

(* the three readings leave their trees on top of the copies *)
Lemma p1_ok : forall x o1 o2 o0 C,
  okf C (parse_evs sm x (okof o1) ++ parse_evs sm x (okof o2) ++ parse_evs sm x (okof o0)) /\
  hlive_from C (parse_evs sm x (okof o1) ++ parse_evs sm x (okof o2) ++ parse_evs sm x (okof o0)) =
    pacc sm x (okof o0) ++ pacc sm x (okof o2) ++ pacc sm x (okof o1) ++ C.
Proof.
  intros x o1 o2 o0 C.
  destruct (parse_ok sm x (okof o1) C) as [P1 Q1].
  destruct (parse_ok sm x (okof o2) (pacc sm x (okof o1) ++ C)) as [P2 Q2].
  destruct (parse_ok sm x (okof o0) (pacc sm x (okof o2) ++ pacc sm x (okof o1) ++ C)) as [P0 Q0].
  split.
  - apply okf_app. split; [exact P1|]. rewrite Q1.
    apply okf_app. split; [exact P2|]. rewrite Q2. exact P0.
  - rewrite !hlive_from_app, Q1, Q2, Q0. reflexivity.
Qed.

(* pj_free (&a1), (&a2), (&a0), then free (one / two / nul): nothing is left *)
Lemma tfrees_ok : forall x o1 o2 o0 CP,
  okf (pacc sm x (okof o0) ++ pacc sm x (okof o2) ++ pacc sm x (okof o1) ++ [CP; CP; CP])
      (p1_tfree x o1 ++ p1_tfree x o2 ++ p1_tfree x o0 ++ [HFr CP; HFr CP; HFr CP]) /\
  hlive_from (pacc sm x (okof o0) ++ pacc sm x (okof o2) ++ pacc sm x (okof o1) ++ [CP; CP; CP])
      (p1_tfree x o1 ++ p1_tfree x o2 ++ p1_tfree x o0 ++ [HFr CP; HFr CP; HFr CP]) = [].
Proof.
  intros x o1 o2 o0 CP.
  set (A1 := pacc sm x (okof o1)). set (A2 := pacc sm x (okof o2)). set (A0 := pacc sm x (okof o0)).
  set (C := [CP; CP; CP]).
  set (S0 := A0 ++ A2 ++ A1 ++ C).
  assert (E1 : Permutation S0 (A1 ++ (A0 ++ A2 ++ C))).
  { unfold S0. rewrite (app_assoc A0 A2 (A1 ++ C)), (app_assoc A0 A2 C).
    apply (Permutation_app_swap_app (A0 ++ A2) A1 C). }
  destruct (tfree_ok x o1 S0 _ E1) as [T1 U1].
  set (S1 := hlive_from S0 (p1_tfree x o1)) in *.
  assert (E2 : Permutation S1 (A2 ++ (A0 ++ C))).
  { apply (Permutation_trans U1). apply Permutation_app_swap_app. }
  destruct (tfree_ok x o2 S1 _ E2) as [T2 U2].
  set (S2 := hlive_from S1 (p1_tfree x o2)) in *.
  destruct (tfree_ok x o0 S2 _ U2) as [T0 U0].
  set (S3 := hlive_from S2 (p1_tfree x o0)) in *.
  assert (HC : okf C [HFr CP; HFr CP; HFr CP] /\ hlive_from C [HFr CP; HFr CP; HFr CP] = []).
  { unfold C. cbn [okf hits hstep hlive_from fold_left]. rewrite !rm1_cons_eq. split.
    - split; [left; reflexivity|]. split; [left; reflexivity|]. split; [left; reflexivity | exact I].
    - reflexivity. }
  destruct HC as [HC1 HC2].
  assert (HF2 : hlive_from S3 [HFr CP; HFr CP; HFr CP] = []).
  { pose proof (hlive_from_perm [HFr CP; HFr CP; HFr CP] S3 C U0) as Hp. rewrite HC2 in Hp.
    exact (Permutation_nil (Permutation_sym Hp)). }
  split.
  - apply okf_app. split; [exact T1|]. fold S1.
    apply okf_app. split; [exact T2|]. fold S2.
    apply okf_app. split; [exact T0|]. fold S3.
    exact (okf_perm _ C S3 (Permutation_sym U0) HC1).
  - rewrite !hlive_from_app. fold S1. fold S2. fold S3. exact HF2.
Qed.

(* the accepted or refused path after expected (): nothing is left *)
Lemma tail_ok : forall x, okf (pacc sm x []) (call_tail x) /\ hlive_from (pacc sm x []) (call_tail x) = [].
Proof.
  intros x. unfold call_tail, pacc.
  destruct (fst (jr_run sm x [])) as [t|] eqn:Ej.
  - set (Lr := rd_blocks (rtr sm [] x)).
    assert (Hw : pj_wf sm t) by (apply (wf_read sm x t); unfold json_read; exact Ej).
    destruct (round_trip_ok sm t Hw) as [R1 R2].
    destruct (seg_step [] (round_trip sm t) Lr Lr R1 (Permutation_refl _)) as [R3 R4].
    fold (hlive (round_trip sm t)) in R4.
    assert (HR : Permutation (hlive_from Lr (round_trip sm t)) Lr).
    { apply (Permutation_trans R4). apply (Permutation_trans (Permutation_app_tail Lr R2)).
      apply Permutation_refl. }
    set (S1 := hlive_from Lr (round_trip sm t)) in *.
    destruct (starved_ok x S1) as [Q1 Q2].
    destruct (starved_writes_ok x t S1) as [W1 W2].
    assert (HB : Permutation S1 (pj_frees sm [] x ++ [])).
    { rewrite app_nil_r. apply (Permutation_trans HR). apply Permutation_sym. apply pj_frees_blocks. }
    destruct (bulk_ok (pj_frees sm [] x) S1 [] HB) as [B1 B2].
    split.
    + apply okf_app. split; [exact R3|]. fold S1.
      apply okf_app. split; [exact Q1|]. rewrite Q2.
      apply okf_app. split; [exact W1|]. rewrite W2.
      cbn [okf]. split; [exact B1 | exact I].
    + rewrite (hlive_from_app Lr (round_trip sm t)). fold S1.
      rewrite (hlive_from_app S1 (starved_parse sm x (calls (rtr sm [] x)))), Q2.
      rewrite (hlive_from_app S1 (starved_writes x t)), W2.
      rewrite hlive_from_cons, hlive_from_nil. exact (Permutation_nil (Permutation_sym B2)).
  - exact (starved_ok x []).
Qed.

Lemma rest_ok : forall x, okf [] (call_rest x) /\ hlive (call_rest x) = [].
Proof.
  intros x. unfold call_rest, hlive. cbv zeta.
  set (SC := Z.of_nat (length x) + 1).
  destruct (parse_ok sm x [] []) as [P1 P2]. rewrite app_nil_r in P2.
  assert (HS : forall s, okf s [HMal SC; HFr SC] /\ hlive_from s [HMal SC; HFr SC] = s).
  { intros s. cbn [okf hits hstep hlive_from fold_left]. rewrite rm1_cons_eq.
    split; [split; [exact I|]; split; [left; reflexivity | exact I] | reflexivity]. }
  destruct (tail_ok x) as [T1 T2].
  split.
  - apply okf_app. split; [exact P1|]. rewrite P2.
    apply okf_app. split; [exact (proj1 (HS (pacc sm x [])))|]. rewrite (proj2 (HS (pacc sm x []))). exact T1.
  - rewrite (hlive_from_app [] (parse_evs sm x [])), P2.
    rewrite (hlive_from_app (pacc sm x [])), (proj2 (HS (pacc sm x []))). exact T2.
Qed.

(* free (one), free (two), free (nul) when only the three copies are live: nothing is left *)
Lemma cfrees_ok : forall CP S, Permutation S [CP; CP; CP] ->
  okf S [HFr CP; HFr CP; HFr CP] /\ hlive_from S [HFr CP; HFr CP; HFr CP] = [].
Proof.
  intros CP S Hp.
  assert (HC : okf [CP; CP; CP] [HFr CP; HFr CP; HFr CP] /\ hlive_from [CP; CP; CP] [HFr CP; HFr CP; HFr CP] = []).
  { cbn [okf hits hstep hlive_from fold_left]. rewrite !rm1_cons_eq. split.
    - split; [left; reflexivity|]. split; [left; reflexivity|]. split; [left; reflexivity | exact I].
    - reflexivity. }
  destruct HC as [HC1 HC2]. split.
  - exact (okf_perm _ _ S (Permutation_sym Hp) HC1).
  - pose proof (hlive_from_perm [HFr CP; HFr CP; HFr CP] S [CP; CP; CP] Hp) as H. rewrite HC2 in H.
    exact (Permutation_nil (Permutation_sym H)).
Qed.

Lemma call_ok : forall x o1 o2 o0, okf [] (call_evs x o1 o2 o0) /\ hlive (call_evs x o1 o2 o0) = [].
Proof.
  intros x o1 o2 o0. rewrite call_evs_blocks. unfold hlive.
  destruct (MAXB <? Z.of_nat (length x)); [split; [exact I | reflexivity]|].
  set (CP := Z.of_nat (length x) + FUZZ_PAD).
  assert (HC : hlive_from [] [HMal CP; HMal CP; HMal CP] = [CP; CP; CP]) by reflexivity.
  assert (H3 : okf [] [HMal CP; HMal CP; HMal CP]) by (cbn [okf hits]; repeat split).
  destruct (ranout x o1) eqn:E1; cbv iota.
  { (* reading 1 runs out: its tree is empty, the copies are freed *)
    destruct (parse_ok sm x (okof o1) [CP; CP; CP]) as [P1 Q1].
    rewrite (ranout_pacc x o1 E1), app_nil_l in Q1.
    destruct (cfrees_ok CP [CP; CP; CP] (Permutation_refl _)) as [F1 F2].
    split.
    - apply okf_app. split; [exact H3|]. rewrite HC.
      apply okf_app. split; [exact P1|]. rewrite Q1. exact F1.
    - rewrite hlive_from_app, HC, hlive_from_app, Q1. exact F2. }
  destruct (ranout x o2) eqn:E2; cbv iota.
  { (* reading 2 runs out: its tree is empty; reading 1's tree, then the copies, are freed *)
    destruct (parse_ok sm x (okof o1) [CP; CP; CP]) as [P1 Q1].
    destruct (parse_ok sm x (okof o2) (pacc sm x (okof o1) ++ [CP; CP; CP])) as [P2 Q2].
    rewrite (ranout_pacc x o2 E2), app_nil_l in Q2.
    destruct (tfree_ok x o1 (pacc sm x (okof o1) ++ [CP; CP; CP]) [CP; CP; CP] (Permutation_refl _)) as [T1 U1].
    destruct (cfrees_ok CP _ U1) as [F1 F2].
    split.
    - apply okf_app. split; [exact H3|]. rewrite HC.
      apply okf_app. split.
      + apply okf_app. split; [exact P1|]. rewrite Q1. exact P2.
      + rewrite hlive_from_app, Q1, Q2. apply okf_app. split; [exact T1 | exact F1].
    - rewrite !hlive_from_app, HC, Q1, Q2. exact F2. }
  (* readings 1 and 2 did not run out: the three trees, then the copies, are freed; the rest unless reading 3 ran
     out *)
  destruct (p1_ok x o1 o2 o0 [CP; CP; CP]) as [Q1 Q2].
  destruct (tfrees_ok x o1 o2 o0 CP) as [T1 T2].
  assert (R : okf [] (if ranout x o0 then [] else call_rest x) /\
              hlive_from [] (if ranout x o0 then [] else call_rest x) = []).
  { destruct (ranout x o0); [split; [exact I | reflexivity]|]. exact (rest_ok x). }
  destruct R as [R1 R2].
  split.
  - apply okf_app. split; [exact H3|]. rewrite HC.
    apply okf_app. split; [exact Q1|]. rewrite Q2.
    apply okf_app. split; [exact T1|]. rewrite T2. exact R1.
  - rewrite hlive_from_app, HC, hlive_from_app, Q2, hlive_from_app, T2. exact R2.
Qed.

(* Every removal of a call (an HRe, an HFr, a pj_free) finds its block live. *)
Theorem call_okf : forall x o1 o2 o0, okf [] (call_evs x o1 o2 o0).
Proof. intros x o1 o2 o0. exact (proj1 (call_ok x o1 o2 o0)). Qed.

(* A call gives back all it took, whatever the three readings' grants. *)
Theorem call_closed : forall x o1 o2 o0, Permutation (hlive (call_evs x o1 o2 o0)) [].
Proof. intros x o1 o2 o0. rewrite (proj2 (call_ok x o1 o2 o0)). apply Permutation_refl. Qed.

(* So the calls compose: every removal of the k calls finds its block live. *)
Theorem hruns_okf : forall x os, okf [] (hruns x os).
Proof.
  intros x os. induction os as [|[[o1 o2] o0] os IH]; [exact I|].
  rewrite hruns_cons. destruct (call_ok x o1 o2 o0) as [H1 H2].
  apply okf_app. split; [exact H1|]. unfold hlive in H2. rewrite H2. exact IH.
Qed.

(* ================================================================ the live count of a class *)

(* PresetReqAtClass.pk_round_trip, with the copy's trace bounded by T (there: T + 4) *)
Lemma pkR_round_trip : forall f t T A, pj_wf sm t ->
  (nprodR f (rd_hevs (ttrace t)) <= T)%nat ->
  (forall ms, t = JObj ms -> (nprodR f (rd_hevs (ttrace (copy_set ms))) <= T)%nat) ->
  (pkR f A (round_trip sm t) <= 2 * T + cnt f A + 5)%nat.
Proof.
  intros f t T A Hw HT HC.
  assert (Htb : (cnt f (tblk t) <= T)%nat) by (pose proof (cnt_tblkR f t); lia).
  unfold round_trip.
  rewrite app_assoc, pkR_app.
  destruct (rt_text_ok sm t false A Hw) as [_ A2].
  set (S1 := hlive_from A (rt_text sm t false)) in *.
  destruct (rt_text_ok sm t true S1 Hw) as [_ B2].
  assert (HS2 : Permutation (hlive_from A (rt_text sm t false ++ rt_text sm t true))
                            (fo t ++ tblk t ++ A)).
  { rewrite hlive_from_app. fold S1. apply (Permutation_trans B2).
    apply (Permutation_trans (Permutation_app_head (tblk t) A2)).
    apply Permutation_app_tail. apply Permutation_sym. apply fo_tblk. }
  set (S2 := hlive_from A (rt_text sm t false ++ rt_text sm t true)) in *.
  destruct (bulk_ok (fo t) S2 (tblk t ++ A) HS2) as [_ C2].
  assert (H1 : (pkR f A (rt_text sm t false ++ rt_text sm t true) <= 2 * T + cnt f A + 5)%nat).
  { rewrite pkR_app. fold S1.
    pose proof (pkR_rt_text f sm t false A Hw). pose proof (pkR_rt_text f sm t true S1 Hw).
    assert (Hs1 : cnt f S1 = (cnt f (tblk t) + cnt f A)%nat) by (rewrite (cnt_perm f _ _ A2), cnt_app; reflexivity).
    lia. }
  assert (HcS2 : (cnt f S2 <= T + T + cnt f A)%nat).
  { rewrite (cnt_perm f _ _ HS2), !cnt_app, (cnt_perm f _ _ (fo_tblk t)). lia. }
  set (S3 := hstep S2 (HBulk (fo t))) in *.
  assert (HcS3 : (cnt f S3 <= T + cnt f A)%nat) by (rewrite (cnt_perm f _ _ C2), cnt_app; lia).
  rewrite (pkR_app f [HBulk (fo t)] _ S2).
  rewrite hlive_from_cons, hlive_from_nil. fold S3.
  assert (H2 : (pkR f S2 [HBulk (fo t)] <= 2 * T + cnt f A + 5)%nat) by (cbn [pkR]; fold S3; lia).
  assert (H3 : (pkR f S3 (match t with
                          | JObj ms => rw_evs sm ms ++ [HBulk (fo (copy_set ms))]
                          | _ => [HBulk (fo t)]
                          end) <= 2 * T + cnt f A + 5)%nat).
  { destruct t as [| | | txt bits | z | items | ms]; cbv beta iota;
      try (match goal with |- (pkR f S3 ?L <= _)%nat => pose proof (pkR_le f L S3) as P end;
           cbn [nprodR prod_evR] in P; lia).
    rewrite pkR_app.
    pose proof (pkR_rw f sm ms S3 Hw). pose proof (HC ms eq_refl).
    pose proof (cnt_live_pkR f S3 (rw_evs sm ms)).
    pose proof (pkR_le f [HBulk (fo (copy_set ms))]
                  (hlive_from S3 (rw_evs sm ms))) as P. cbn [nprodR prod_evR] in P.
    lia. }
  lia.
Qed.

Lemma cnt_pacc : forall f x ok A, (forall ok, (nprodR f (rd_hevs (rtr sm ok x)) <= A)%nat) ->
  (cnt f (pacc sm x ok) <= A)%nat.
Proof.
  intros f x ok A HA. unfold pacc. destruct (fst (jr_run sm x ok)).
  - pose proof (cnt_hlive_nprodR f (rd_hevs (rtr sm ok x))). pose proof (HA ok). unfold rd_blocks. lia.
  - cbn. lia.
Qed.

Lemma nprodR_tfree : forall f x o, nprodR f (p1_tfree x o) = 0%nat.
Proof. intros f x o. unfold p1_tfree. destruct (fst (jr_run sm x (okof o))); reflexivity. Qed.

Lemma pkR_starved : forall f x s A, (forall ok, (nprodR f (rd_hevs (rtr sm ok x)) <= A)%nat) ->
  (pkR f s (starved_parse sm x (calls (rtr sm [] x))) <= cnt f s + A)%nat.
Proof.
  intros f x s A HA. unfold starved_parse. destruct (calls (rtr sm [] x)) as [|k].
  - cbn [pkR]. lia.
  - pose proof (pkR_le f (parse_evs sm x (okk (pick x (S k)))) s) as H.
    rewrite nprodR_parse in H. pose proof (HA (okk (pick x (S k)))). lia.
Qed.

(* the tail: the round trips (A + 2 B + 5), the starved parse (2 A), the starved writes (A + 1) *)
Lemma pkR_tail : forall f x A B,
  (forall ok, (nprodR f (rd_hevs (rtr sm ok x)) <= A)%nat) ->
  (forall t, fst (jr_run sm x []) = Some t -> (nprodR f (rd_hevs (ttrace t)) <= B)%nat) ->
  (forall ms, fst (jr_run sm x []) = Some (JObj ms) -> (nprodR f (rd_hevs (ttrace (copy_set ms))) <= B)%nat) ->
  (pkR f (pacc sm x []) (call_tail x) <= Nat.max (2 * A) (A + 2 * B + 5))%nat.
Proof.
  intros f x A B HA HB HB'. unfold call_tail, pacc.
  destruct (fst (jr_run sm x [])) as [t|] eqn:Ej.
  - set (Lr := rd_blocks (rtr sm [] x)).
    assert (HcL : (cnt f Lr <= A)%nat).
    { unfold Lr, rd_blocks. pose proof (cnt_hlive_nprodR f (rd_hevs (rtr sm [] x))). pose proof (HA []). lia. }
    assert (Hw : pj_wf sm t) by (apply (wf_read sm x t); unfold json_read; exact Ej).
    pose proof (pkR_round_trip f t B Lr Hw (HB t ltac:(first [exact Ej | reflexivity]))
                  (fun ms E => HB' ms ltac:(subst t; first [exact Ej | reflexivity]))) as R.
    destruct (round_trip_ok sm t Hw) as [R1 R2].
    destruct (seg_step [] (round_trip sm t) Lr Lr R1 (Permutation_refl _)) as [_ R4].
    fold (hlive (round_trip sm t)) in R4.
    assert (HR : Permutation (hlive_from Lr (round_trip sm t)) Lr).
    { apply (Permutation_trans R4). apply (Permutation_trans (Permutation_app_tail Lr R2)).
      apply Permutation_refl. }
    rewrite (pkR_app f (round_trip sm t)).
    set (S1 := hlive_from Lr (round_trip sm t)) in *.
    assert (HcS : cnt f S1 = cnt f Lr) by exact (cnt_perm f _ _ HR).
    rewrite (pkR_app f (starved_parse sm x (calls (rtr sm [] x)))), (proj2 (starved_ok x S1)).
    rewrite (pkR_app f (starved_writes x t)), (proj2 (starved_writes_ok x t S1)).
    pose proof (pkR_starved f x S1 A HA).
    pose proof (pkR_starved_writes f x t S1).
    pose proof (pkR_le f [HBulk (pj_frees sm [] x)] S1) as P. cbn [nprodR prod_evR] in P.
    lia.
  - pose proof (pkR_starved f x [] A HA) as P.
    assert (C0 : cnt f [] = 0%nat) by reflexivity. lia.
Qed.

(* after check_no_overread: the main parse and expected ()'s scratch (A + 1), then the tail *)
Lemma pkR_rest : forall f x A B,
  (forall ok, (nprodR f (rd_hevs (rtr sm ok x)) <= A)%nat) ->
  (forall t, fst (jr_run sm x []) = Some t -> (nprodR f (rd_hevs (ttrace t)) <= B)%nat) ->
  (forall ms, fst (jr_run sm x []) = Some (JObj ms) -> (nprodR f (rd_hevs (ttrace (copy_set ms))) <= B)%nat) ->
  (pkR f [] (call_rest x) <= Nat.max (2 * A) (A + 2 * B + 5))%nat.
Proof.
  intros f x A B HA HB HB'. unfold call_rest. cbv zeta.
  set (SC := Z.of_nat (length x) + 1).
  destruct (parse_ok sm x [] []) as [_ P2]. rewrite app_nil_r in P2.
  rewrite (pkR_app f (parse_evs sm x [])), P2.
  rewrite (pkR_app f [HMal SC; HFr SC]).
  assert (HS : hlive_from (pacc sm x []) [HMal SC; HFr SC] = pacc sm x []).
  { cbn [hlive_from fold_left hstep]. apply rm1_cons_eq. }
  rewrite HS.
  pose proof (pkR_le f (parse_evs sm x []) []) as P. rewrite nprodR_parse in P.
  pose proof (HA []) as HA0.
  assert (C0 : cnt f [] = 0%nat) by reflexivity.
  pose proof (pkR_le f [HMal SC; HFr SC] (pacc sm x [])) as Q. cbn [nprodR prod_evR] in Q.
  pose proof (cnt_pacc f x [] A HA) as Hc.
  pose proof (pkR_tail f x A B HA HB HB') as T.
  destruct (f SC); lia.
Qed.

(* one call: check_no_overread's peak (3 A + 3; a call that a reading cuts holds less) or the rest's *)
Lemma pkR_call : forall f x o1 o2 o0 A B,
  (forall ok, (nprodR f (rd_hevs (rtr sm ok x)) <= A)%nat) ->
  (forall t, fst (jr_run sm x []) = Some t -> (nprodR f (rd_hevs (ttrace t)) <= B)%nat) ->
  (forall ms, fst (jr_run sm x []) = Some (JObj ms) -> (nprodR f (rd_hevs (ttrace (copy_set ms))) <= B)%nat) ->
  (pkR f [] (call_evs x o1 o2 o0) <= KH + Nat.max (3 * A) (A + 2 * B + KB))%nat.
Proof.
  intros f x o1 o2 o0 A B HA HB HB'. rewrite call_evs_blocks.
  destruct (MAXB <? Z.of_nat (length x)).
  { cbn [pkR]. assert (C0 : cnt f [] = 0%nat) by reflexivity. lia. }
  set (CP := Z.of_nat (length x) + FUZZ_PAD).
  set (H3 := [HMal CP; HMal CP; HMal CP]).
  assert (HC : hlive_from [] H3 = [CP; CP; CP]) by reflexivity.
  assert (C0 : cnt f [] = 0%nat) by reflexivity.
  pose proof (pkR_le f H3 []) as P1.
  assert (N3 : (nprodR f H3 <= 3)%nat) by (unfold H3; cbn [nprodR prod_evR]; destruct (f CP); lia).
  assert (CC : (cnt f [CP; CP; CP] <= 3)%nat) by (rewrite !cnt_cons_eqR; destruct (f CP); rewrite C0; lia).
  assert (NF : nprodR f [HFr CP; HFr CP; HFr CP] = 0%nat) by reflexivity.
  assert (HP : forall o, (nprodR f (parse_evs sm x (okof o)) <= A)%nat) by (intros o; rewrite nprodR_parse; apply HA).
  destruct (ranout x o1) eqn:E1; cbv iota.
  { (* reading 1 runs out: the copies and its reading *)
    destruct (parse_ok sm x (okof o1) [CP; CP; CP]) as [_ Q1].
    rewrite (ranout_pacc x o1 E1), app_nil_l in Q1.
    rewrite (pkR_app f H3), HC, (pkR_app f (parse_evs sm x (okof o1))), Q1.
    pose proof (pkR_le f (parse_evs sm x (okof o1)) [CP; CP; CP]) as P2. pose proof (HP o1).
    pose proof (pkR_le f [HFr CP; HFr CP; HFr CP] [CP; CP; CP]) as P3.
    unfold KH, KB. lia. }
  destruct (ranout x o2) eqn:E2; cbv iota.
  { (* reading 2 runs out: the copies, readings 1 and 2, reading 1's tree *)
    destruct (parse_ok sm x (okof o1) [CP; CP; CP]) as [_ Q1].
    destruct (parse_ok sm x (okof o2) (pacc sm x (okof o1) ++ [CP; CP; CP])) as [_ Q2].
    rewrite (ranout_pacc x o2 E2), app_nil_l in Q2.
    set (G := parse_evs sm x (okof o1) ++ parse_evs sm x (okof o2)).
    set (T := p1_tfree x o1 ++ [HFr CP; HFr CP; HFr CP]).
    assert (QG : hlive_from [CP; CP; CP] G = pacc sm x (okof o1) ++ [CP; CP; CP]).
    { unfold G. rewrite hlive_from_app, Q1, Q2. reflexivity. }
    rewrite (pkR_app f H3), HC, (pkR_app f G), QG.
    pose proof (pkR_le f G [CP; CP; CP]) as P2.
    assert (NG : (nprodR f G <= 2 * A)%nat).
    { unfold G. rewrite nprodR_app. pose proof (HP o1). pose proof (HP o2). lia. }
    pose proof (pkR_le f T (pacc sm x (okof o1) ++ [CP; CP; CP])) as P3.
    assert (NT : nprodR f T = 0%nat) by (unfold T; rewrite nprodR_app, nprodR_tfree; exact NF).
    rewrite cnt_app in P3. pose proof (cnt_pacc f x (okof o1) A HA).
    unfold KH, KB. lia. }
  (* readings 1 and 2 did not run out: the three readings, their trees, then the rest unless reading 3 ran out *)
  destruct (p1_ok x o1 o2 o0 [CP; CP; CP]) as [_ Q2].
  destruct (tfrees_ok x o1 o2 o0 CP) as [_ T2].
  set (G1 := parse_evs sm x (okof o1) ++ parse_evs sm x (okof o2) ++ parse_evs sm x (okof o0)) in *.
  set (G2 := p1_tfree x o1 ++ p1_tfree x o2 ++ p1_tfree x o0 ++ [HFr CP; HFr CP; HFr CP]) in *.
  rewrite (pkR_app f H3), HC, (pkR_app f G1), Q2, (pkR_app f G2), T2.
  pose proof (pkR_le f G1 [CP; CP; CP]) as P2.
  assert (N1 : (nprodR f G1 <= 3 * A)%nat).
  { unfold G1. rewrite !nprodR_app. pose proof (HP o1). pose proof (HP o2). pose proof (HP o0). lia. }
  pose proof (pkR_le f G2 (pacc sm x (okof o0) ++ pacc sm x (okof o2) ++ pacc sm x (okof o1) ++ [CP; CP; CP])) as P3.
  assert (N2 : nprodR f G2 = 0%nat).
  { unfold G2. rewrite !nprodR_app, !nprodR_tfree. reflexivity. }
  rewrite !cnt_app in P3.
  pose proof (cnt_pacc f x (okof o0) A HA). pose proof (cnt_pacc f x (okof o1) A HA).
  pose proof (cnt_pacc f x (okof o2) A HA).
  assert (P4 : (pkR f [] (if ranout x o0 then [] else call_rest x) <= Nat.max (2 * A) (A + 2 * B + 5))%nat).
  { destruct (ranout x o0); [cbn [pkR]; lia | exact (pkR_rest f x A B HA HB HB')]. }
  unfold KH, KB. lia.
Qed.

(* THE LIVE COUNT: at every position of the k calls, a class f holds at most KH + max (3 A) (A + 2 B + KB)
   = max (3 A + 3) (A + 2 B + 5) live requests, A bounding the f-requests of one reading of x under any grants and B
   those of the trace of the file's tree and of its rewritten copy. *)
Theorem hruns_live : forall x os f A B, (length os <= 4)%nat ->
  (forall ok, (nprodR f (rd_hevs (rtr sm ok x)) <= A)%nat) ->
  (forall t, fst (jr_run sm x []) = Some t -> (nprodR f (rd_hevs (ttrace t)) <= B)%nat) ->
  (forall ms, fst (jr_run sm x []) = Some (JObj ms) -> (nprodR f (rd_hevs (ttrace (copy_set ms))) <= B)%nat) ->
  forall i, (cnt f (hlive (firstn i (hruns x os))) <= KH + Nat.max (3 * A) (A + 2 * B + KB))%nat.
Proof.
  intros x os f A B _ HA HB HB' i.
  assert (Hpk : (pkR f [] (hruns x os) <= KH + Nat.max (3 * A) (A + 2 * B + KB))%nat).
  { induction os as [|[[o1 o2] o0] os IH].
    - cbn [hruns map concat pkR]. assert (C0 : cnt f [] = 0%nat) by reflexivity. lia.
    - rewrite hruns_cons, (pkR_app f (call_evs x o1 o2 o0)).
      destruct (call_ok x o1 o2 o0) as [_ E]. unfold hlive in E. rewrite E.
      pose proof (pkR_call f x o1 o2 o0 A B HA HB HB'). lia. }
  pose proof (pkR_prefix f (hruns x os) [] i). unfold hlive. lia.
Qed.

End Run2.

(* ================================================================ the freed requests, in order *)

Definition hfree1 (e : hev) : list Z :=
  match e with HMal _ => [] | HRe m _ => [m] | HFr n => [n] | HBulk L => L end.

(* HFr n -> [n]; HRe m n -> [m]; HBulk L -> L; HMal -> [] *)
Definition hfrees (es : list hev) : list Z := flat_map hfree1 es.

Lemma hfrees_app : forall a b, hfrees (a ++ b) = hfrees a ++ hfrees b.
Proof. intros a b. unfold hfrees. apply flat_map_app. Qed.

Lemma hfrees_chain_h : forall cs hd old, Forall (fun c => 0 < c) cs -> 0 < old ->
  hfrees (chain hd old cs) = map (fun c => c + hd) (removelast (old :: cs)).
Proof.
  induction cs as [|c cs IH]; intros hd old Hall Hold; [reflexivity|].
  apply Forall_cons_iff in Hall as [Hc Hall].
  cbn [chain]. rewrite (proj2 (Z.eqb_neq old 0)) by lia.
  change (hfrees (HRe (old + hd) (c + hd) :: chain hd c cs)) with ((old + hd) :: hfrees (chain hd c cs)).
  rewrite (IH hd c Hall Hc). reflexivity.
Qed.

(* a buffer grown through the capacities cs from none frees each capacity but the last, in order *)
Lemma hfrees_chain0 : forall cs hd, Forall (fun c => 0 < c) cs ->
  hfrees (chain hd 0 cs) = map (fun c => c + hd) (removelast cs).
Proof.
  intros [|c cs] hd Hall; [reflexivity|].
  apply Forall_cons_iff in Hall as [Hc Hall].
  cbn [chain]. rewrite Z.eqb_refl.
  change (hfrees (HMal (c + hd) :: chain hd c cs)) with (hfrees (chain hd c cs)).
  exact (hfrees_chain_h cs hd c Hall Hc).
Qed.

(* pj_write's buffer (fuzz_realloc: request cap + HEAD) *)
Theorem hfrees_w_evs : forall t p, hfrees (w_evs t p) = map (fun c => c + HEAD) (removelast (wcaps t p)).
Proof. intros t p. unfold w_evs. exact (hfrees_chain0 (wcaps t p) HEAD (wcaps_pos t p)). Qed.

(* rendered ()'s buffer (realloc: request cap) *)
Theorem hfrees_r_evs : forall t p, hfrees (r_evs t p) = removelast (rcaps t p).
Proof.
  intros t p. unfold r_evs. rewrite (hfrees_chain0 (rcaps t p) 0 (rcaps_pos t p)).
  rewrite (map_ext (fun c => c + 0) (fun c => c) Z.add_0_r). apply map_id.
Qed.

(* Each round trip's writer chain (and rendered ()'s) comes, with its frees, before the round trip's parse. *)
Theorem rt_text_frees : forall sm t p,
  rt_text sm t p = w_evs t p ++ r_evs t p ++ parse_evs sm (wdoc t p) [] ++ r_free t p ++ w_free t p /\
  hfrees (w_evs t p) = map (fun c => c + HEAD) (removelast (wcaps t p)) /\
  hfrees (r_evs t p) = removelast (rcaps t p).
Proof. intros sm t p. split; [reflexivity|]. split; [apply hfrees_w_evs | apply hfrees_r_evs]. Qed.

(* and the rewrite's: pj_string / pj_set, then the writer, then the parse of its text *)
Theorem rw_evs_frees : forall sm ms,
  rw_evs sm ms = set_evs ms ++ w_evs (copy_set ms) true ++ parse_evs sm (wdoc (copy_set ms) true) [] ++
                 w_free (copy_set ms) true ++ [HBulk (fo (copy_set ms))] /\
  hfrees (w_evs (copy_set ms) true) = map (fun c => c + HEAD) (removelast (wcaps (copy_set ms) true)).
Proof. intros sm ms. split; [reflexivity | apply hfrees_w_evs]. Qed.

(* ================================================================ sanity, by computation *)

(* "[[]]" with the first reading refused at its first allocation: the reading runs out, so the other readings are not
   made and the call ends after check_no_overread's frees. After 6 events (the 3 copies, the refused reading's
   pj_free (out) of an empty tree, 2 of the 3 frees) one copy is live; the call ends empty. *)
Example sanity_call_peak : forall sm,
  hlive (firstn 6 (call_evs sm [91; 91; 93; 93] (Some 0%nat) None None)) = [20].
Proof. intros sm. vm_compute. reflexivity. Qed.

Example sanity_call_end : forall sm,
  hlive (call_evs sm [91; 91; 93; 93] (Some 0%nat) (Some 1%nat) None) = [].
Proof. intros sm. vm_compute. reflexivity. Qed.
