

(** * OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel.GtTblWidth — every entry of a built table has
      [c_bits <= 15], UNRELATIVISED in the index

    huffman-id's `inf_fetch_go` (`ZBitsIn.v:458`) pulls while `c_bits h > br_bits b`
    with `h` recomputed each trip, so its exit bound is governed by the TABLE's entry
    widths, and they named the premise rather than assuming it:

        TblBitsAtMost B t := forall i, c_bits (t i) <= B

    Delivered here at [B = 15], for every table type, **with no range restriction on
    the index** — which is the part that needed checking rather than assuming.

    ============================================================================
    WHY THIS ONE CAN BE UNRELATIVISED WHERE [lcode_len_bounded] CANNOT.

    zlib-lead warned that [TblBitsAtMost] is an unrelativised universal over a shared
    array index, structurally identical to [InflateFast.lcode_len_bounded], which is
    FALSE because the distance table lives in the same array above the length table's
    extent ([Gw.GtLcodeBound]).  The warning is exactly right about the SHAPE and the
    conclusion differs, for a reason worth stating:

      [lc_len_ok] asserts a LENGTH-specific bound (`c_val + 2^extra - 1 <= 258`, and
      258 is MAX_MATCH), so a distance entry violates it by up to 127x — a unit
      mismatch.  [c_bits] is a CODE WIDTH, and every entry of every table type carries
      a width, all of them bounded by MAXBITS.  There is no second unit.

    So the shared array is harmless here and fatal there.  **Same shape, opposite
    verdict, and the discriminator is whether the bound's units are table-type
    specific.**  Stated because the shape alone would have argued for relativising.
    ============================================================================

    AND THE TRAP THAT MAKES THIS A WALK RATHER THAN ARITHMETIC.  [mkCodeT] applies
    [u8], so a NEGATIVE width does not give a small number — measured:

        c_bits (mkCodeT 0 (-4) 0) = 252        c_bits (mkCodeT 0 (-1) 0) = 255

    The three widths the loop writes are [s_len st - s_drop st] ([it_here]'s three arms
    and [it_finish]), [x_root c] (the sub-table pointer) and [1] ([it_pre]'s markers).
    So the bound needs [0 <= s_len st - s_drop st] at every visited state, which is an
    ORDERING fact — not a consequence of [s_len <= 15] and [x_root <= 15] on their own.

    IT COMES FROM MY OWN LANDED [ItGTblCover.CovInv], whose phase disjunct is exactly
    the missing fact: phase 1 has [s_drop = 0] with [s_len <= x_root], phase 2 has
    [s_drop = x_root] with [x_root < s_len].  Both give [0 <= s_len - s_drop <= 15]
    against [1 <= x_root c <= 15] and [1 <= s_len st <= 15].  **So this walk is a
    mirror of one I have already done, and it cites rather than re-derives**:
    [cov_pre] discharges the invariant at entry, [cov_step_cont] preserves it, and
    [bits_here_val] converts the arm width.  That chain was landed-unbuilt an hour ago
    and is citable from the graded root only because rt-scout's sweep built it.

    GTBL-ARMS, 2026-08-19.  Read-only against the graded tree. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Base Inftrees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import ItGTblCover.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(** huffman-id's premise, verbatim. *)
Definition TblBitsAtMost (B : Z) (t : ztbl) : Prop := forall i, c_bits (t i) <= B.

(* ######################################################################### *)
(* 1.  THE WIDTH AT A VISITED STATE — from CovInv's phase disjunct            *)
(* ######################################################################### *)

Lemma cov_width_range : forall c cnt0 st,
  CovCtxOk c cnt0 -> CovInv c cnt0 st -> 0 <= s_len st - s_drop st <= 15.
Proof.
  intros c cnt0 st Hctx Hinv.
  destruct Hctx as (Hroot & _).
  destruct Hinv as (Hlen & _ & _ & _ & _ & _ & _ & Hphase).
  destruct Hphase as [(Hd & _ & _ & _ & Hle) | (Hd & Hlt & _)]; lia.
Qed.

Lemma bits_here_le : forall c cnt0 st,
  CovCtxOk c cnt0 -> CovInv c cnt0 st -> c_bits (it_here c st) <= 15.
Proof.
  intros c cnt0 st Hctx Hinv.
  pose proof (cov_width_range c cnt0 st Hctx Hinv) as Hr.
  rewrite (bits_here_val c st) by lia. lia.
Qed.

(** The pointer arm's width is [x_root c], which [CovCtxOk] bounds directly. *)
Lemma bits_ptr_le : forall c cnt0 b v,
  CovCtxOk c cnt0 -> c_bits (mkCodeT b (x_root c) v) <= 15.
Proof.
  intros c cnt0 b v Hctx. destruct Hctx as (Hroot & _).
  unfold mkCodeT, u8. cbn [c_bits]. rewrite Z.mod_small by lia. lia.
Qed.

(* ######################################################################### *)
(* 2.  CLOSURE UNDER THE WRITE CHANNEL                                        *)
(* ######################################################################### *)

Lemma bits_tset : forall B t i e,
  TblBitsAtMost B t -> c_bits e <= B -> TblBitsAtMost B (tset t i e).
Proof.
  intros B t i e Ht He j. unfold tset.
  destruct (Z.eqb j i); [exact He | apply Ht].
Qed.

Lemma bits_it_fill : forall n B t bi incr h,
  TblBitsAtMost B t -> c_bits h <= B -> TblBitsAtMost B (it_fill n t bi incr h).
Proof.
  induction n as [|n IH]; intros B t bi incr h Ht Hh; cbn [it_fill].
  - exact Ht.
  - apply IH; [apply bits_tset; assumption | exact Hh].
Qed.

(** The table a step result carries.  Defined locally for the third time in this lane,
    because the two files that already define it are landed-unbuilt or frozen — the
    same artifact condition rt-scout's sweep has just started retiring. *)
Definition step_table (r : ItStep) : ztbl :=
  match r with
  | ItCont st => s_tbl st
  | ItBreak st => s_tbl st
  | ItOverflow t => t
  end.

(* ######################################################################### *)
(* 3.  ONE TRIP                                                               *)
(* ######################################################################### *)

Lemma bits_step : forall c cnt0 st,
  CovCtxOk c cnt0 -> CovInv c cnt0 st ->
  TblBitsAtMost 15 (s_tbl st) ->
  TblBitsAtMost 15 (step_table (it_step c st)).
Proof.
  intros c cnt0 st Hctx Hinv Ht.
  assert (Hhere : c_bits (it_here c st) <= 15) by (apply (bits_here_le c cnt0 st); assumption).
  assert (Htbl1 : TblBitsAtMost 15
                    (it_fill (Z.to_nat (Z.shiftl 1 (s_curr st)
                                        / Z.shiftl 1 (s_len st - s_drop st)))
                       (s_tbl st)
                       (s_next st + Z.shiftr (s_huff st) (s_drop st))
                       (Z.shiftl 1 (s_len st - s_drop st))
                       (it_here c st)))
    by (apply bits_it_fill; assumption).
  unfold it_step. cbv zeta.
  destruct (Z.eqb (zset (s_count st) (s_len st) (s_count st (s_len st) - 1) (s_len st)) 0
            && Z.eqb (s_len st) (x_max c)) eqn:Ebrk;
    [cbn [step_table s_tbl]; exact Htbl1|].
  destruct ((Z.ltb (x_root c) _) && negb (Z.eqb _ (s_low st))) eqn:Esub.
  - destruct (it_enough (x_type c) _) eqn:Eover;
      [cbn [step_table]; exact Htbl1|].
    cbn [step_table s_tbl]. apply bits_tset; [exact Htbl1|].
    apply (bits_ptr_le c cnt0). exact Hctx.
  - cbn [step_table s_tbl]. exact Htbl1.
Qed.

(** [it_finish] writes one marker whose width is the SAME [s_len - s_drop] as the
    pre-state's, because the break state copies both fields unchanged
    ([Inftrees.v:319-321]).  So the pre-state's invariant bounds it. *)
Lemma bits_finish_at : forall c cnt0 st st1,
  CovCtxOk c cnt0 -> CovInv c cnt0 st ->
  s_len st1 = s_len st -> s_drop st1 = s_drop st ->
  TblBitsAtMost 15 (s_tbl st1) ->
  TblBitsAtMost 15 (it_finish st1).
Proof.
  intros c cnt0 st st1 Hctx Hinv Hl Hd Ht. unfold it_finish.
  destruct (Z.eqb (s_huff st1) 0); [exact Ht|].
  apply bits_tset; [exact Ht|].
  pose proof (cov_width_range c cnt0 st Hctx Hinv) as Hr.
  unfold mkCodeT, u8. cbn [c_bits]. rewrite Hl, Hd.
  rewrite Z.mod_small by lia. lia.
Qed.

(* ######################################################################### *)
(* 4.  THE LOOP — same shape as the landed [ItGTblCover.cov_loop]              *)
(* ######################################################################### *)

Lemma bits_loop : forall n c cnt0 st st1,
  CovCtxOk c cnt0 -> CovInv c cnt0 st ->
  TblBitsAtMost 15 (s_tbl st) ->
  it_loop n c st = Some (ItBreak st1) ->
  TblBitsAtMost 15 (it_finish st1).
Proof.
  induction n as [|n IH]; intros c cnt0 st st1 Hctx Hinv Ht Hl;
    cbn [it_loop] in Hl; [discriminate|].
  destruct (it_step c st) as [s|s|t] eqn:E.
  - assert (Hs : TblBitsAtMost 15 (s_tbl s)).
    { pose proof (bits_step c cnt0 st Hctx Hinv Ht) as H0.
      rewrite E in H0. cbn [step_table] in H0. exact H0. }
    exact (IH c cnt0 s st1 Hctx (cov_step_cont c cnt0 st s Hctx Hinv E) Hs Hl).
  - assert (Hs : TblBitsAtMost 15 (s_tbl s)).
    { pose proof (bits_step c cnt0 st Hctx Hinv Ht) as H0.
      rewrite E in H0. cbn [step_table] in H0. exact H0. }
    injection Hl as Hl. subst s.
    (* the break state copies s_len and s_drop from the pre-state *)
    apply (bits_finish_at c cnt0 st st1 Hctx Hinv);
      [ | | exact Hs].
    + unfold it_step in E. cbv zeta in E.
      destruct (Z.eqb (zset (s_count st) (s_len st) (s_count st (s_len st) - 1)
                         (s_len st)) 0 && Z.eqb (s_len st) (x_max c));
        [injection E as <-; reflexivity|].
      destruct ((Z.ltb (x_root c) _) && negb (Z.eqb _ (s_low st)));
        [destruct (it_enough (x_type c) _); discriminate E | discriminate E].
    + unfold it_step in E. cbv zeta in E.
      destruct (Z.eqb (zset (s_count st) (s_len st) (s_count st (s_len st) - 1)
                         (s_len st)) 0 && Z.eqb (s_len st) (x_max c));
        [injection E as <-; reflexivity|].
      destruct ((Z.ltb (x_root c) _) && negb (Z.eqb _ (s_low st)));
        [destruct (it_enough (x_type c) _); discriminate E | discriminate E].
  - discriminate Hl.
Qed.

(* ######################################################################### *)
(* 5.  THE PRE-LOOP, forward, ty-generic                                      *)
(* ######################################################################### *)

Definition PreTblOk (t0 : ztbl) (r : ItPre) : Prop :=
  match r with
  | PreGo _ st => s_tbl st = t0
  | _ => True
  end.

Lemma pre_tbl_ok : forall ty lens codes root0 t0,
  PreTblOk t0 (it_pre ty lens codes root0 t0).
Proof.
  intros ty lens codes root0 t0. unfold PreTblOk, it_pre. cbv zeta.
  destruct (Z.eqb (it_findmax 15%nat MAXBITS (it_count (Z.to_nat codes) 0 lens zzero)) 0);
    [exact I|].
  destruct (it_kraft 15%nat 1 1 (it_count (Z.to_nat codes) 0 lens zzero)) as [lft|];
    [|exact I].
  destruct (it_incomplete ty lft _); [exact I|].
  destruct (it_enough ty _); [exact I|].
  cbn [s_tbl]. reflexivity.
Qed.

Lemma pre_tbl_go : forall ty lens codes root0 t0 c st,
  it_pre ty lens codes root0 t0 = PreGo c st -> s_tbl st = t0.
Proof.
  intros ty lens codes root0 t0 c st H.
  pose proof (pre_tbl_ok ty lens codes root0 t0) as HP. rewrite H in HP. exact HP.
Qed.

(* ######################################################################### *)
(* 6.  THE THEOREM — huffman-id's premise, discharged                          *)
(* ######################################################################### *)

(** Premise set mirrors [ItGTblCover.it_covers_root_pos] exactly, plus the recurrence
    on the table [it_model] was handed — which is not a residue: [inf_table] passes the
    LIVE [state->codes] array ([Inflate.v:1241]), so a caller carries the property
    forward across builds rather than establishing it once. *)
Theorem built_table_bits_le_15 : forall ty lens codes root0 t0 out,
  0 <= codes ->
  (forall i, 0 <= i < codes -> 0 <= lens i <= 15) ->
  1 <= root0 <= 15 ->
  TblBitsAtMost 15 t0 ->
  it_model ty lens codes root0 t0 = Some out ->
  o_ret out = 0 ->
  TblBitsAtMost 15 (o_tbl out).
Proof.
  intros ty lens codes root0 t0 out Hcodes Hlens Hroot0 Ht0 Hm Hret.
  unfold it_model in Hm.
  destruct (it_pre ty lens codes root0 t0) as [|t| |c st] eqn:Hpre.
  - injection Hm as <-. cbn in Hret. lia.
  - injection Hm as <-. cbn [o_tbl].
    pose proof (it_pre_empty_shape ty lens codes root0 t0 t Hpre) as Hshape.
    rewrite Hshape. apply bits_tset; [apply bits_tset; [exact Ht0|]|];
      unfold mkCodeT, u8; cbn [c_bits]; rewrite Z.mod_small; lia.
  - injection Hm as <-. cbn in Hret. lia.
  - destruct (cov_pre ty lens codes root0 t0 c st Hcodes Hlens Hroot0 Hpre)
      as [Hctx Hinv].
    pose proof (pre_tbl_go ty lens codes root0 t0 c st Hpre) as Htbl.
    destruct (it_loop (S (Z.to_nat codes)) c st) as [r|] eqn:Hl; [|discriminate].
    destruct r as [s|s|tt].
    + discriminate Hm.
    + injection Hm as <-. cbn [o_tbl].
      (* cnt0 left to unification: it is fixed by Hctx/Hinv, and naming it would
         require ItGTblSortWin for sw_cnt, which nothing else here needs *)
      apply (bits_loop (S (Z.to_nat codes)) c _ st s
               Hctx Hinv); [rewrite Htbl; exact Ht0 | exact Hl].
    + injection Hm as <-. cbn in Hret. lia.
Qed.

(** And the shape huffman-id's fetch loop takes it in. *)
Corollary tblbitsatmost_of_built : forall ty lens codes root0 t0 out,
  0 <= codes ->
  (forall i, 0 <= i < codes -> 0 <= lens i <= 15) ->
  1 <= root0 <= 15 ->
  (forall i, c_bits (t0 i) <= 15) ->
  it_model ty lens codes root0 t0 = Some out ->
  o_ret out = 0 ->
  forall i, c_bits (o_tbl out i) <= 15.
Proof.
  intros ty lens codes root0 t0 out A B C D E F.
  exact (built_table_bits_le_15 ty lens codes root0 t0 out A B C D E F).
Qed.

Print Assumptions cov_width_range.
Print Assumptions bits_here_le.
Print Assumptions bits_ptr_le.
Print Assumptions bits_tset.
Print Assumptions bits_it_fill.
Print Assumptions bits_step.
Print Assumptions bits_finish_at.
Print Assumptions bits_loop.
Print Assumptions pre_tbl_ok.
Print Assumptions pre_tbl_go.
Print Assumptions built_table_bits_le_15.
Print Assumptions tblbitsatmost_of_built.
