(** * ItGTblT0 — leg (3b): the spec's table output is t0-GENERIC on the written set.

    GTBL-ARMS lane, 2026-08-17.  Claim: c5-progress.md §GTBL-B1 (22:06 UTC),
    under TL's RULING O3.  This is the leg that makes the [t0 = tnone] anchor
    (3a) legitimate: composed with it, the result is general in [t0], which is
    TL's acceptance condition ("the composite must quantify t0 spec-side with no
    residual pin").

    SPEC-INTERNAL BY CONSTRUCTION, and that is the point.  This file imports
    Base and Inftrees and NOTHING ELSE — no [ItModel], no coercion, no [ttbl].
    So the import-discipline hazard that governs [ItGTblBridge.v] (five
    doubly-bound names) DOES NOT EXIST HERE: only one model is in scope, so
    [Import] is safe and unqualified names are unambiguous.  That asymmetry
    between the two files is deliberate and worth stating, because a reader who
    has internalised the bridge's rules would otherwise wonder why this file
    breaks them.

    WHY THIS LEG IS THE CHEAP ONE (from §GTBL-B1 items 2-3): it relates the SAME
    function to ITSELF, differing only in one argument.  Both runs step in
    lockstep by construction, there is no cross-model representation gap, and the
    written-set notion — which is the only genuinely new content — is needed only
    here, in its easy form.

    Spec side is Inftrees.v @ / Base.v @ , consumed as
    published. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Base Inftrees.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Open Scope Z_scope.

(** ** 1.  The written-set relation, stated WITHOUT a written set

    The obvious formulation carries an explicit set of written indices and proves
    it grows correctly.  This one does not need it: at every index, either the two
    runs' tables AGREE (the index was written, and both runs wrote the same entry
    because the entry depends only on the non-table state) or each still holds its
    OWN initial value (the index was never written by either).

    That disjunction IS the written-set characterisation, and it is pointwise, so
    nothing has to track a set through the loop.  It also makes the [s_used] NAME
    TRAP a non-issue: the spec's own comment (Inftrees.v :227-238) warns that a
    claim over [[0, s_used)] is false at trip 0 because [s_used] is ALLOCATED and
    not WRITTEN capacity — this relation never mentions [s_used], so it cannot
    make that mistake. *)
Definition AgreeOrInit (t0 : ztbl) (a b : ztbl) : Prop :=
  forall i, a i = b i \/ (a i = t0 i /\ b i = tnone i).

Lemma agreeorinit_refl_init : forall t0, AgreeOrInit t0 t0 tnone.
Proof. intros t0 i. right. split; reflexivity. Qed.

(** A write that both runs perform, at the same index with the same entry, moves
    that index into the AGREE case and leaves every other index alone. *)
Lemma agreeorinit_tset : forall t0 a b j e,
  AgreeOrInit t0 a b ->
  AgreeOrInit t0 (tset a j e) (tset b j e).
Proof.
  intros t0 a b j e H i. unfold tset.
  destruct (Z.eqb i j); [left; reflexivity | exact (H i)].
Qed.

(** The same for the replication loop, through the spec's own pointwise
    characterisation rather than by induction on [it_fill]. *)
Lemma agreeorinit_fill : forall t0 a b n bi incr h,
  0 < incr ->
  AgreeOrInit t0 a b ->
  AgreeOrInit t0 (it_fill n a bi incr h) (it_fill n b bi incr h).
Proof.
  intros t0 a b n bi incr h Hi H i.
  rewrite (it_fill_get n a bi incr h i Hi), (it_fill_get n b bi incr h i Hi).
  destruct (andb (andb (Z.leb bi i) (Z.ltb i (bi + Z.of_nat n * incr)))
                 (Z.eqb (Z.modulo (i - bi) incr) 0));
    [left; reflexivity | exact (H i)].
Qed.

(** ** 2.  Everything except the table is equal, and stays equal

    [s_count] is compared POINTWISE (it is a function), which forces two
    congruence lemmas below: the two loops that READ a count array must give the
    same answer on pointwise-equal inputs. *)
Definition StSameButTbl (st st' : ItSt) : Prop :=
  s_huff st = s_huff st'
  /\ s_sym  st = s_sym  st'
  /\ s_len  st = s_len  st'
  /\ s_next st = s_next st'
  /\ s_curr st = s_curr st'
  /\ s_drop st = s_drop st'
  /\ s_low  st = s_low  st'
  /\ s_used st = s_used st'
  /\ s_min  st = s_min  st'
  /\ (forall i, s_count st i = s_count st' i).

(** The entry written by a trip depends only on the context and the non-table
    fields, so the two runs write the SAME entry — which is what collapses the
    fill and the pointer write into the [agreeorinit_*] lemmas above. *)
Lemma it_here_ext : forall c st st',
  StSameButTbl st st' ->
  it_here c st = it_here c st'.
Proof.
  intros c st st' (_ & Hsym & Hlen & _ & _ & Hdrop & _).
  unfold it_here. rewrite Hsym, Hlen, Hdrop. reflexivity.
Qed.

Lemma it_subsz_ext : forall n cnt cnt' drop mx curr left,
  (forall i, cnt i = cnt' i) ->
  it_subsz n cnt drop mx curr left = it_subsz n cnt' drop mx curr left.
Proof.
  induction n as [|k IH]; intros cnt cnt' drop mx curr left Hc; [reflexivity|].
  cbn [it_subsz]. rewrite (Hc (curr + drop)).
  destruct (Z.ltb (curr + drop) mx); [|reflexivity].
  destruct (Z.leb (left - cnt' (curr + drop)) 0); [reflexivity|].
  apply IH. exact Hc.
Qed.

Lemma zset_ext : forall (a a' : zarr) j v i,
  (forall k, a k = a' k) ->
  zset a j v i = zset a' j v i.
Proof.
  intros a a' j v i H. unfold zset.
  destruct (Z.eqb i j); [reflexivity | exact (H i)].
Qed.

(** ** 3.  ONE TRIP is t0-generic

    Both runs take the SAME branch, because every test reads only the fields
    [StSameButTbl] equates — nothing reads the table except the writes
    themselves.  So the outcome and every non-table field are identical, and the
    two tables move together through [agreeorinit_fill] / [agreeorinit_tset].

    The one wrinkle is [s_count]: a FUNCTION compared pointwise, not
    syntactically, so it cannot be substituted away.  It reaches exactly two
    places that matter — the exit test and the sub-table width — and both are
    Z-VALUED, which is why [zset_ext] and [it_subsz_ext] suffice and why no
    functional extensionality is needed anywhere in this file. *)
Theorem it_step_t0_generic : forall c t0 st st',
  StSameButTbl st st' ->
  AgreeOrInit t0 (s_tbl st) (s_tbl st') ->
  0 <= s_len st - s_drop st ->
  match it_step c st, it_step c st' with
  | ItCont st1, ItCont st1' =>
      StSameButTbl st1 st1' /\ AgreeOrInit t0 (s_tbl st1) (s_tbl st1')
  | ItBreak st1, ItBreak st1' =>
      StSameButTbl st1 st1' /\ AgreeOrInit t0 (s_tbl st1) (s_tbl st1')
  | ItOverflow ta, ItOverflow tb => AgreeOrInit t0 ta tb
  | _, _ => False
  end.
Proof.
  intros c t0 st st' HS HT Hd.
  assert (HSc := HS).
  (* expose the fields and substitute every SCALAR equality, so the two sides
     differ only in the count array (pointwise) and the table *)
  destruct st  as [h  sy  l  nx  cu  dr  lo  us  mn  cnt  tbl ].
  destruct st' as [h' sy' l' nx' cu' dr' lo' us' mn' cnt' tbl'].
  destruct HS as (Hh & Hs & Hl & Hn & Hc & Hdr & Hlo & Hu & Hm & Hcnt).
  cbn [s_huff s_sym s_len s_next s_curr s_drop s_low s_used s_min s_count s_tbl]
    in Hh, Hs, Hl, Hn, Hc, Hdr, Hlo, Hu, Hm, Hcnt, HT, Hd |- *.
  subst h' sy' l' nx' cu' dr' lo' us' mn'.
  assert (Hincr : 0 < Z.shiftl 1 (l - dr)).
  { rewrite Z.shiftl_mul_pow2 by lia.
    pose proof (Z.pow_pos_nonneg 2 (l - dr) ltac:(lia) Hd). lia. }
  assert (Hcnt1 : forall i, zset cnt l (cnt l - 1) i = zset cnt' l (cnt' l - 1) i).
  { intro i. rewrite <- (Hcnt l). exact (zset_ext cnt cnt' l (cnt l - 1) i Hcnt). }
  unfold it_step. cbv zeta.
  (* the projections reappear applied to the literal records after the unfold, so
     they must be reduced again before anything can match a field-level lemma *)
  cbn [s_huff s_sym s_len s_next s_curr s_drop s_low s_used s_min s_count s_tbl].
  (* the two Z-valued places the counts reach, turned into the [cnt] side *)
  rewrite <- (Hcnt1 l).
  rewrite <- (it_subsz_ext 16%nat (zset cnt l (cnt l - 1)) (zset cnt' l (cnt' l - 1))
                _ _ _ _ Hcnt1).
  destruct (andb (Z.eqb (zset cnt l (cnt l - 1) l) 0) (Z.eqb l (x_max c))).
  - split.
    + unfold StSameButTbl.
      cbn [s_huff s_sym s_len s_next s_curr s_drop s_low s_used s_min s_count].
      repeat apply conj; try reflexivity. exact Hcnt1.
    + cbn [s_tbl]. exact (agreeorinit_fill t0 tbl tbl' _ _ _ _ Hincr HT).
  - destruct (andb (Z.ltb (x_root c) _) (negb (Z.eqb (Z.land _ (x_mask c)) lo))).
    + destruct (it_enough (x_type c) _).
      * cbn. exact (agreeorinit_fill t0 tbl tbl' _ _ _ _ Hincr HT).
      * split.
        -- unfold StSameButTbl.
           cbn [s_huff s_sym s_len s_next s_curr s_drop s_low s_used s_min s_count].
           repeat apply conj; try reflexivity. exact Hcnt1.
        -- cbn [s_tbl].
           exact (agreeorinit_tset t0 _ _ _ _
                    (agreeorinit_fill t0 tbl tbl' _ _ _ _ Hincr HT)).
    + split.
      * unfold StSameButTbl.
        cbn [s_huff s_sym s_len s_next s_curr s_drop s_low s_used s_min s_count].
        repeat apply conj; try reflexivity. exact Hcnt1.
      * cbn [s_tbl]. exact (agreeorinit_fill t0 tbl tbl' _ _ _ _ Hincr HT).
Qed.

Print Assumptions it_step_t0_generic.

(** ** 4.  THE WHOLE LOOP is t0-generic

    Induction on the shared fuel.  Both runs are the SAME function, so they
    consume fuel in lockstep by construction and there is nothing to reconcile —
    the [it_loop]/[g_run] fuel argument from §GTBL-B1 item 2 applies here a
    fortiori.

    [P] is the caller's side-condition carrier, exactly as in the cross-model
    loop lemma: it must imply the fill's [0 <= s_len - s_drop] and survive a
    continue.  Only ONE copy is needed even though there are two runs, because
    [StSameButTbl] makes the two states agree on every field [P] could read. *)
Theorem it_loop_t0_generic :
  forall (P : ItSt -> Prop) n c t0 st st' r r',
  (forall u, P u -> 0 <= s_len u - s_drop u) ->
  (forall u u', P u -> it_step c u = ItCont u' -> P u') ->
  P st ->
  StSameButTbl st st' ->
  AgreeOrInit t0 (s_tbl st) (s_tbl st') ->
  it_loop n c st = Some r ->
  it_loop n c st' = Some r' ->
  match r, r' with
  | ItBreak a, ItBreak b => StSameButTbl a b /\ AgreeOrInit t0 (s_tbl a) (s_tbl b)
  | ItOverflow a, ItOverflow b => AgreeOrInit t0 a b
  | _, _ => False
  end.
Proof.
  intros P n. induction n as [|k IH]; intros c t0 st st' r r' Hside Hpres HP HS HT
    H1 H2.
  - cbn in H1. discriminate.
  - cbn in H1, H2.
    pose proof (it_step_t0_generic c t0 st st' HS HT (Hside st HP)) as HStep.
    destruct (it_step c st) as [st1|st1|ta] eqn:E1;
      destruct (it_step c st') as [st1'|st1'|tb] eqn:E2;
      cbn in HStep; try contradiction.
    + (* both continue *)
      destruct HStep as [HS1 HT1].
      exact (IH c t0 st1 st1' r r' Hside Hpres (Hpres st st1 HP E1) HS1 HT1 H1 H2).
    + (* both exit *)
      injection H1 as <-. injection H2 as <-. exact HStep.
    + (* both overflow *)
      injection H1 as <-. injection H2 as <-. exact HStep.
Qed.

(** ** 5.  Across the epilogue

    [it_finish]'s test, index and written entry all read only fields
    [StSameButTbl] equates, so the incomplete-code fixup is the same write on
    both runs. *)
Theorem it_finish_t0_generic : forall t0 st st',
  StSameButTbl st st' ->
  AgreeOrInit t0 (s_tbl st) (s_tbl st') ->
  AgreeOrInit t0 (it_finish st) (it_finish st').
Proof.
  intros t0 st st' HS HT.
  destruct HS as (Hh & _ & Hl & Hn & _ & Hdr & _).
  unfold it_finish. rewrite <- Hh, <- Hl, <- Hn, <- Hdr.
  destruct (Z.eqb (s_huff st) 0); [exact HT|].
  exact (agreeorinit_tset t0 _ _ _ _ HT).
Qed.

Print Assumptions it_loop_t0_generic.
Print Assumptions it_finish_t0_generic.

(** ** 6.  The PROLOGUE is t0-independent, and this is where the leg gets cheap

    [it_pre] has four decision points — [mx = 0], [it_kraft]'s option, the
    incompleteness test, and the ENOUGH test — and **[t0] appears in NONE of
    them.**  Checked, not assumed: in the whole of [it_pre] (Inftrees.v @
    :378-420) [t0] occurs exactly twice, as the [PreEmpty] table and as
    [PreGo]'s [s_tbl], and every computed quantity ([cnt0], [mx], [mn], [r],
    [lft], [offs], [wk], [used0]) is derived from [lens]/[codes]/[root0] alone.

    THAT IS WHY (3b) DOES NOT NEED THE CROSS-MODEL PRE-PHASE that (3a) does. The
    scope correction I posted about (3a) — that my §1 table never enumerated the
    prologue — does not touch this leg, because here the prologue only has to be
    shown t0-BLIND, which is a syntactic property of one function, not a
    correspondence between two. *)
Theorem it_pre_t0_generic : forall ty lens codes root0 t0,
  match it_pre ty lens codes root0 t0, it_pre ty lens codes root0 tnone with
  | PreErr, PreErr => True
  | PreOver, PreOver => True
  | PreEmpty a, PreEmpty b => AgreeOrInit t0 a b
  | PreGo c st, PreGo c' st' =>
      c = c' /\ StSameButTbl st st' /\ AgreeOrInit t0 (s_tbl st) (s_tbl st')
  | _, _ => False
  end.
Proof.
  intros ty lens codes root0 t0. unfold it_pre. cbv zeta.
  destruct (Z.eqb (it_findmax 15%nat MAXBITS (it_count (Z.to_nat codes) 0 lens zzero)) 0).
  - apply agreeorinit_tset. apply agreeorinit_tset. apply agreeorinit_refl_init.
  - destruct (it_kraft 15%nat 1 1 (it_count (Z.to_nat codes) 0 lens zzero))
      as [lft|]; [|exact I].
    destruct (it_incomplete ty lft
                (it_findmax 15%nat MAXBITS (it_count (Z.to_nat codes) 0 lens zzero)));
      [exact I|].
    destruct (it_enough ty (Z.shiftl 1 _)); [exact I|].
    split; [reflexivity|]. split.
    + unfold StSameButTbl.
      cbn [s_huff s_sym s_len s_next s_curr s_drop s_low s_used s_min s_count].
      (* robust either way: if [reflexivity] already closed the pointwise
         conjunct there is no goal left for the [intro] to act on *)
      repeat apply conj; try reflexivity; try (intro i; reflexivity).
    + cbn [s_tbl]. exact (agreeorinit_refl_init t0).
Qed.

(** ** 7.  (3b) COMPLETE: it_model's output is t0-generic

    The composite this leg exists for.  All three scalar outputs are EQUAL — the
    return code, [*bits] and the [*table] advance do not depend on [t0] at all —
    and the tables are related by [AgreeOrInit], i.e. they agree wherever either
    run wrote and each otherwise holds its own initial entry.

    The error returns are the degenerate case and they come out right for the
    right reason: both leave the caller's table untouched, so nothing was written
    and [AgreeOrInit] holds by its second disjunct everywhere.

    [P] carries the fill's side condition, and the caller supplies it about the
    ACTUAL prologue state rather than about a state I have to produce. *)
Theorem it_model_t0_generic :
  forall (P : ItSt -> Prop) ty lens codes root0 t0 o o',
  (forall u, P u -> 0 <= s_len u - s_drop u) ->
  (forall c u u', P u -> it_step c u = ItCont u' -> P u') ->
  (forall c st, it_pre ty lens codes root0 t0 = PreGo c st -> P st) ->
  it_model ty lens codes root0 t0 = Some o ->
  it_model ty lens codes root0 tnone = Some o' ->
  o_ret o = o_ret o' /\ o_bits o = o_bits o' /\ o_used o = o_used o'
  /\ AgreeOrInit t0 (o_tbl o) (o_tbl o').
Proof.
  intros P ty lens codes root0 t0 o o' Hside Hpres HP H1 H2.
  pose proof (it_pre_t0_generic ty lens codes root0 t0) as HPre.
  unfold it_model in H1, H2.
  (* ItPre is PreErr | PreEmpty t | PreOver | PreGo c st -- four constructors with
     arities 0,1,0,2, so the pattern has an EMPTY third slot *)
  destruct (it_pre ty lens codes root0 t0) as [ | a | | c st ] eqn:E1;
    destruct (it_pre ty lens codes root0 tnone) as [ | b | | c' st' ] eqn:E2;
    cbn in HPre; try contradiction.
  - (* PreErr / PreErr *)
    injection H1 as <-. injection H2 as <-. cbn.
    repeat split; try reflexivity. exact (agreeorinit_refl_init t0).
  - (* PreEmpty / PreEmpty *)
    injection H1 as <-. injection H2 as <-. cbn.
    repeat split; try reflexivity. exact HPre.
  - (* PreOver / PreOver *)
    injection H1 as <-. injection H2 as <-. cbn.
    repeat split; try reflexivity. exact (agreeorinit_refl_init t0).
  - (* PreGo / PreGo -- the loop *)
    destruct HPre as (Ec & HS & HT). subst c'.
    destruct (it_loop (S (Z.to_nat codes)) c st) as [r|] eqn:L1; [|discriminate].
    destruct (it_loop (S (Z.to_nat codes)) c st') as [r'|] eqn:L2; [|discriminate].
    pose proof (it_loop_t0_generic P (S (Z.to_nat codes)) c t0 st st' r r'
                  Hside (fun u u' => Hpres c u u') (HP c st eq_refl) HS HT L1 L2)
      as HL.
    destruct r as [u|u|t]; destruct r' as [u'|u'|t'];
      cbn in HL, H1, H2; try contradiction; try discriminate.
    + (* both ItBreak *)
      destruct HL as [HS1 HT1].
      injection H1 as <-. injection H2 as <-. cbn.
      (* extract without destroying: HS1 is still needed by it_finish_t0_generic *)
      assert (Hused : s_used u = s_used u')
        by (destruct HS1 as (_ & _ & _ & _ & _ & _ & _ & H & _); exact H).
      (* count-INDEPENDENT closer: every goal-count assumption I made today was
         wrong at least once, so dispatch per goal instead of positionally *)
      repeat split; try reflexivity; try exact Hused;
        try exact (it_finish_t0_generic t0 u u' HS1 HT1).
    + (* both ItOverflow *)
      injection H1 as <-. injection H2 as <-. cbn.
      repeat split; try reflexivity. exact HL.
Qed.

Print Assumptions it_pre_t0_generic.
Print Assumptions it_model_t0_generic.

Print Assumptions agreeorinit_refl_init.
Print Assumptions agreeorinit_tset.
Print Assumptions agreeorinit_fill.
Print Assumptions it_here_ext.
Print Assumptions it_subsz_ext.
Print Assumptions zset_ext.
