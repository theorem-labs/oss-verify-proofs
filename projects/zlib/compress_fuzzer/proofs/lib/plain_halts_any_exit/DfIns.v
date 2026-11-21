(** * DfIns — the fast-path walk, part F2: [df_insert]'s chain walk.

    OWNER: q5-emitter (GAP7 D1).  TRUST BOUNDARY: pure Gallina.

    [df_insert] is [deflate_fast]'s match-covering insert loop
    ([deflate.c:1860-1870]): n unconditional hash inserts, each one
    strstart-advance + [insert_string] — exactly the INSERT arm of
    [SwArm1a.ds_insert_step], whose boundary test is TRUE under this
    lemma's in-bounds premise.  The walk re-establishes [ChainInv] and
    [InsSync] and frames every other field. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Chunk ZBitsOut BwStream Deflate Trees CresChain CbFold.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import
  SwWin SwFill SwTally SwChain SwLm SwInv SwArmPre SwArm1a.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

Lemma df_insert_walk : forall f g wbits hbits S Ins l n,
  GeomOk2 g wbits hbits ->
  ChainInv g (ls_window l) (ls_prev l) (ls_head l)
           (ls_strstart l) (S - ls_strstart l) Ins ->
  (forall p, Ins p -> p <= ls_strstart l) ->
  InsSync g S l ->
  0 <= ls_strstart l ->
  1 <= n ->
  n < Z.of_nat f ->
  ls_strstart l + n + MIN_MATCH <= S ->
  S <= 65538 ->
  let r := df_insert f g n l in
  exists Ins',
    ChainInv g (ls_window r) (ls_prev r) (ls_head r)
             (ls_strstart r) (S - ls_strstart r) Ins'
    /\ (forall p, Ins' p -> p <= ls_strstart r)
    /\ InsSync g S r
    /\ ls_window r = ls_window l
    /\ ls_blockstart r = ls_blockstart l
    /\ ls_matchavail r = ls_matchavail l
    /\ ls_matchlen r = ls_matchlen l
    /\ ls_matchstart r = ls_matchstart l
    /\ ls_lookahead r = ls_lookahead l
    /\ ls_windowsize r = ls_windowsize l
    /\ ls_insert r = ls_insert l
    /\ ls_prevlen r = ls_prevlen l
    /\ ls_prevmatch r = ls_prevmatch l
    /\ ls_strstart r = ls_strstart l + n.
Proof.
  induction f as [|f IH]; intros g wbits hbits S Ins l n
    Hg HC Hhi Hsync Hss0 Hn1 Hnf Hfit Hu16.
  - cbn [Z.of_nat] in Hnf. lia.
  - cbn [df_insert]. cbv zeta.
    destruct (ds_insert_step g wbits hbits S Ins l Hg HC Hhi Hsync Hss0
                ltac:(unfold MIN_MATCH in Hfit; lia) Hu16)
      as (Ins1 & HC1 & Hhi1 & Hsync1 & Ew1 & Ebs1 & Ema1 & Eml1 & Ems1
          & Ela1 & Ews1 & Eins1 & Epl1 & Epm1 & Ess1).
    cbv zeta in HC1, Hhi1, Hsync1, Ew1, Ebs1, Ema1, Eml1, Ems1, Ela1,
      Ews1, Eins1, Epl1, Epm1, Ess1.
    (* under the in-bounds premise the step's boundary test is TRUE, so
       its l2 IS the fast loop's insert *)
    replace (Z.leb (ls_strstart (setL_strstart (ls_strstart l + 1) l))
               (S - MIN_MATCH))
      with true in HC1, Hhi1, Hsync1, Ew1, Ebs1, Ema1, Eml1, Ems1, Ela1,
        Ews1, Eins1, Epl1, Epm1, Ess1
      by (cbn [ls_strstart setL_strstart]; symmetry; apply Z.leb_le; lia).
    cbv iota in HC1, Hhi1, Hsync1, Ew1, Ebs1, Ema1, Eml1, Ems1, Ela1,
      Ews1, Eins1, Epl1, Epm1, Ess1.
    set (l2 := snd (insert_string g
                      (ls_strstart (setL_strstart (ls_strstart l + 1) l))
                      (setL_strstart (ls_strstart l + 1) l))) in *.
    destruct (Z.eqb_spec (n - 1) 0) as [E0|Hne].
    + (* last insert *)
      exists Ins1.
      repeat apply conj; try assumption; try congruence.
      all: rewrite Ess1; lia.
    + (* recurse on n-1 over l2 *)
      destruct (IH g wbits hbits S Ins1 l2 (n - 1)
                  Hg HC1 Hhi1 Hsync1
                  ltac:(rewrite Ess1; lia)
                  ltac:(lia)
                  ltac:(lia)
                  ltac:(rewrite Ess1; lia)
                  Hu16)
        as (Ins' & HC' & Hhi' & Hsync' & Ew' & Ebs' & Ema' & Eml' & Ems'
            & Ela' & Ews' & Eins' & Epl' & Epm' & Ess').
      exists Ins'.
      repeat apply conj; try assumption; try congruence.
      all: rewrite Ess', Ess1; lia.
Qed.

Print Assumptions df_insert_walk.
