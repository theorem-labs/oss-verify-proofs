(** * KeyStep — the ownership S-instance's step/loop/model tier
    (pieces 3c-5).

    Imports the carrier and fill transport
    from KeyClass (own_fill_short/own_fill_long, PROVEN) and the three
    engines it runs alongside: CovInv (cov_step_cont, ItGTblCover),
    SubLedger (ledger_step_cont, ItGSubCover), and the break analysis
    derived here.

    own_step_cont dissects it_step's control flow: common fill via
    own_fill_short/long, then the no-creation exit or the creation
    exit, where the window arithmetic
      - phase-2 origin: P' <= top(low) from the position link's
        in-window split; P' in [start(low'), start(low') + u) from the
        st'-link split; low <> low' makes the aligned windows disjoint,
        so everything coincides: P' = top(low) = start(low') — the old
        window is complete (own_fill_long's boundary conclusion
        upgrades it) and the new window opens empty;
      - phase-1 origin: P' and start(low') are both multiples of
        u = 2^(15-root) and P' - start(low') in [0, u) => equal;
    the new pointer's geometry reads back through mkCodeT
    (op/val_mkCodeT_id) with bounds supplied by SubLedger(st')
    (ledger_step_cont) — engine consumed, not mirrored.

    *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Huff Inftrees ItGTblRev ItGTblGeom ItGTblSortWin
  InftreesBridge ItGTblCover ItGSubCover ItGTblLeafPos.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import ZReproQ6K.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import KeyTie KeyRank KeyBits KeyClass.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

(* ===== fast-shadow insert (fastshadow bed, KeyStep) =====
   Context-shed Zify pre-hook: revert every arithmetic hypothesis into the
   goal, then clear every remaining clearable hypothesis, so each [lia]/[nia]
   in this file pays zify preprocessing only for the arithmetic facts instead
   of the full context. The hook is restored to the Zify default at the
   END of this file, so importers see no net redefinition. *)
Ltac keystep_fs_shed :=
  repeat match goal with
  | H : (_ <= _)%Z |- _ => revert H
  | H : (_ < _)%Z |- _ => revert H
  | H : (_ >= _)%Z |- _ => revert H
  | H : (_ > _)%Z |- _ => revert H
  | H : @eq Z _ _ |- _ => revert H
  | H : not _ |- _ => revert H
  | H : @eq bool _ _ |- _ => revert H
  | H : @eq nat _ _ |- _ => revert H
  | H : (_ <= _)%nat |- _ => revert H
  | H : (_ < _)%nat |- _ => revert H
  | H : (_ >= _)%nat |- _ => revert H
  | H : (_ > _)%nat |- _ => revert H
  | H : @eq N _ _ |- _ => revert H
  | H : (_ <= _)%N |- _ => revert H
  | H : (_ < _)%N |- _ => revert H
  | H : _ /\ _ |- _ => revert H
  | H : _ \/ _ |- _ => revert H
  | H : _ <-> _ |- _ => revert H
  end;
  repeat match goal with H : _ |- _ => clear H end.
Ltac Zify.zify_pre_hook ::= keystep_fs_shed.
(* ===== end fast-shadow insert ===== *)
Local Open Scope Z_scope.

(** The terminal ledger shape: at the break state the just-closed
    window (if any) carries the WIDENED region bound next + 2^curr, so
    the loop's final conclusion classifies against that bound — which
    is all the model-level assembly reads (zr_fill_class has no region
    bounds; they are dropped at the weakening). *)
Definition OwnFin (c : ItCtx) (cnt0 : zarr) (lens : list nat)
           (ent : nat -> Code) (st1 : ItSt) : Prop :=
  OwnBelow (x_root c) lens ent (s_tbl st1)
           (s_next st1 + 2 ^ (s_curr st1))
           (Pos (it_mass 15%nat 1 cnt0) st1).

(** The classified payload is monotone in the region bound. *)
Lemma own_below_mono_nxt : forall root lens ent T nxt nxt' P,
  nxt <= nxt' ->
  OwnBelow root lens ent T nxt P ->
  OwnBelow root lens ent T nxt' P.
Proof.
  intros root lens ent T nxt nxt' P Hle Hb i Hi Hg.
  destruct (Hb i Hi Hg) as [HL|HP]; [left; exact HL|right].
  destruct HP as (H1 & H2 & H3 & H4 & H5).
  refine (conj H1 (conj H2 (conj H3 (conj _ H5)))). lia.
Qed.

(** A phase-2 position splits at the root boundary. *)
Lemma pos_split_phase2 : forall (root len huff : Z),
  1 <= root -> root < len -> len <= 15 -> 0 <= huff < 2 ^ len ->
  zrev (Z.to_nat len) huff * 2 ^ (15 - len)
  = zrev (Z.to_nat root) (huff mod 2 ^ root) * 2 ^ (15 - root)
    + zrev (Z.to_nat len - Z.to_nat root) (huff / 2 ^ root)
      * 2 ^ (15 - len).
Proof.
  intros root len huff Hr Hrl Hl Hh.
  assert (Hp2r : 2 ^ Z.of_nat (Z.to_nat root) = 2 ^ root)
    by (apply to_nat_pow; lia).
  assert (Hmod : 0 <= huff mod 2 ^ root < 2 ^ Z.of_nat (Z.to_nat root)).
  { rewrite Hp2r. apply Z.mod_pos_bound. apply pow2_pos_z. lia. }
  pose proof (zrev_split (Z.to_nat root) (Z.to_nat len - Z.to_nat root)
                (huff mod 2 ^ root) (huff / 2 ^ root) Hmod) as HS.
  replace (Z.to_nat root + (Z.to_nat len - Z.to_nat root))%nat
    with (Z.to_nat len) in HS by lia.
  rewrite Hp2r in HS.
  replace (huff mod 2 ^ root + huff / 2 ^ root * 2 ^ root) with huff in HS
    by (pose proof (Z.div_mod huff (2 ^ root)
          ltac:(pose proof (pow2_pos_z root ltac:(lia)); lia)); lia).
  rewrite HS.
  rewrite Z.mul_add_distr_r.
  f_equal.
  rewrite <- Z.mul_assoc. f_equal.
  rewrite <- Z.pow_add_r by lia.
  f_equal. lia.
Qed.

(** A phase-2 position lies inside its root window (fork helper). *)
Lemma pos_in_window : forall root len huff,
  1 <= root -> root < len -> len <= 15 -> 0 <= huff < 2 ^ len ->
  zrev (Z.to_nat root) (huff mod 2 ^ root) * 2 ^ (15 - root)
    <= zrev (Z.to_nat len) huff * 2 ^ (15 - len)
  /\ zrev (Z.to_nat len) huff * 2 ^ (15 - len) + 2 ^ (15 - len)
    <= zrev (Z.to_nat root) (huff mod 2 ^ root) * 2 ^ (15 - root)
       + 2 ^ (15 - root).
Proof.
  intros root len huff Hr Hrl Hl Hh.
  rewrite (pos_split_phase2 root len huff) by lia.
  set (tl := zrev (Z.to_nat len - Z.to_nat root) (huff / 2 ^ root)).
  assert (Htl0 : 0 <= tl) by apply zrev_nonneg.
  assert (Htl : tl < 2 ^ (len - root)).
  { pose proof (zrev_lt (Z.to_nat len - Z.to_nat root) (huff / 2 ^ root))
      as Hz.
    replace (Z.of_nat (Z.to_nat len - Z.to_nat root)) with (len - root)
      in Hz by lia.
    exact Hz. }
  assert (Hpp : 2 ^ (len - root) * 2 ^ (15 - len) = 2 ^ (15 - root))
    by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  assert (Hp15 : 0 < 2 ^ (15 - len)) by (apply pow2_pos_z; lia).
  split; [clear -Htl0 Hp15; nia|].
  clear -Htl0 Htl Hpp Hp15. nia.
Qed.

(** Writing a fresh pointer cell does not disturb classified cells
    (their indices differ) or their children (indices >= 2^root > the
    root-level write index) — fork helper. *)
Lemma own_below_tset_out : forall root lens ent T nxt P lo e,
  0 <= lo < 2 ^ root ->
  (forall i, 0 <= i < 2 ^ root ->
     (zrev (Z.to_nat root) i + 1) * 2 ^ (15 - root) <= P -> i <> lo) ->
  OwnBelow root lens ent T nxt P ->
  OwnBelow root lens ent (tset T lo e) nxt P.
Proof.
  intros root lens ent T nxt P lo e Hlo Hout Hb j Hj Hg.
  assert (Hne : j <> lo) by (apply Hout; assumption).
  destruct (Hb j Hj Hg) as [HL|HP].
  - left.
    destruct HL as (sym & cw & H1 & H2 & H3 & H4 & H5).
    exists sym, cw.
    rewrite (tset_other T lo e j) by exact Hne.
    exact (conj H1 (conj H2 (conj H3 (conj H4 H5)))).
  - right.
    destruct HP as (H1 & H2 & H3 & H4 & H5).
    unfold OwnPtr.
    rewrite (tset_other T lo e j) by exact Hne.
    refine (conj H1 (conj H2 (conj H3 (conj H4 _)))).
    intros k Hk.
    destruct (H5 k Hk) as (sym & cw & G1 & G2 & G3 & G4 & G5).
    exists sym, cw.
    rewrite (tset_other T lo e (c_val (T j) + k)) by lia.
    exact (conj G1 (conj G2 (conj G3 (conj G4 G5)))).
Qed.

(** Trip preservation.  The ty premise is ledger_step_cont's spelling:
    LENS/DISTS have the ENOUGH cap; x_max <= x_root kills creation.
    LeafShape rides along for ledger_step_cont. *)
Lemma own_step_cont : forall c cnt0 (l1 : list nat) st st',
  CovCtxOk c cnt0 ->
  CovInv c cnt0 st ->
  SubLedger (x_type c) c cnt0 st ->
  LeafShape (x_type c) (it_here c st) ->
  arr_eq_on (x_lens c) (zlens l1) 0 (Z.of_nat (length l1)) ->
  x_codes c = Z.of_nat (length l1) ->
  (x_type c = CT_LENS \/ x_type c = CT_DISTS \/ x_max c <= x_root c) ->
  Own c cnt0 l1 (ent_of c l1) st ->
  it_step c st = ItCont st' ->
  Own c cnt0 l1 (ent_of c l1) st'.
Proof.
  intros c cnt0 l1 st st' Hctx Hinv Hled Hlfs Hxl Hxc Hty Hown Hstep.
  pose proof (cov_step_cont c cnt0 st st' Hctx Hinv Hstep) as Hinv'.
  pose proof (ledger_step_cont (x_type c) c cnt0 st st' eq_refl Hty Hctx
                Hinv Hled Hlfs Hstep) as Hled'.
  pose proof (own_fill_short c cnt0 l1 st Hctx Hinv Hxl Hxc) as Hfs.
  pose proof (own_fill_long c cnt0 l1 st Hctx Hinv Hled Hxl Hxc) as Hfl.
  destruct Hown as [Hbelow Hopen].
  pose proof Hctx as Hctx0.
  destruct Hctx0 as (Hroot & Hmask & Hmx & Hmxnz & Hmxz & Hnn & Hcodes
                     & Hlens & Hcnt0 & Hwork & Hupper & Hcase & Hrootmx).
  pose proof Hinv as Hinv0.
  destruct Hinv0 as (Hlen & Hhuff & HwinL & HwinU & Hcnt & Hpos & Hcov
                     & Hphase).
  unfold it_step in Hstep. cbv zeta in Hstep.
  (* the drop' selector is the root either way *)
  assert (Hd' : (if s_drop st =? 0 then x_root c else s_drop st)
                = x_root c).
  { destruct (Z.eqb_spec (s_drop st) 0) as [E|E]; [reflexivity|].
    destruct Hphase as [(Hd & _)|(Hd & _)]; [congruence|exact Hd]. }
  rewrite Hd' in Hstep.
  set (cnt1 := zset (s_count st) (s_len st) (s_count st (s_len st) - 1))
    in *.
  set (huff1 := it_rev_incr (s_huff st) (s_len st)) in *.
  set (T1 := it_fill (Z.to_nat (Z.shiftl 1 (s_curr st)
                       / Z.shiftl 1 (s_len st - s_drop st)))
              (s_tbl st) (s_next st + Z.shiftr (s_huff st) (s_drop st))
              (Z.shiftl 1 (s_len st - s_drop st)) (it_here c st)) in *.
  set (len1 := if cnt1 (s_len st) =? 0
               then x_lens c (x_work c (s_sym st + 1)) else s_len st)
    in *.
  set (cu := it_subsz 16%nat cnt1 (x_root c) (x_max c) (len1 - x_root c)
               (Z.shiftl 1 (len1 - x_root c))) in *.
  set (lo' := Z.land huff1 (x_mask c)) in *.
  assert (HPadv : it_mass 15%nat 1 cnt0 - it_mass 15%nat 1 cnt1
                  = (it_mass 15%nat 1 cnt0 - it_mass 15%nat 1 (s_count st))
                    + 2 ^ (15 - s_len st)).
  { unfold cnt1. apply pos_advance. lia. }
  (* opaque from here on: lia/nia must treat these as atoms *)
  clearbody cnt1 huff1 T1 len1 cu lo'.
  assert (Hup : 0 < 2 ^ (15 - x_root c)) by (apply pow2_pos_z; lia).
  revert Hstep.
  destruct ((cnt1 (s_len st) =? 0) && (s_len st =? x_max c))%bool eqn:Hbrk;
    [intro Hstep; discriminate Hstep|].
  cbv iota.
  destruct ((x_root c <? len1) && negb (lo' =? s_low st))%bool eqn:Hcre;
    cbv iota.
  - (* CREATION exit *)
    destruct (it_enough (x_type c) (s_used st + Z.shiftl 1 cu)) eqn:Hen;
      cbv iota; intro Hstep; [discriminate Hstep|].
    injection Hstep as Heq. subst st'.
    (* post-state facts, projections reduced componentwise *)
    destruct Hinv' as (Hlen' & Hhuff' & _ & _ & _ & Hpos' & _ & Hphase').
    cbn [s_len s_huff s_low s_count s_drop] in Hlen', Hhuff', Hpos',
      Hphase'.
    destruct Hphase' as [(Hd0 & _)|(_ & Hrl' & _ & Hlow' & _)]; [lia|].
    cbn [s_len s_huff s_low] in Hrl', Hlow'.
    destruct Hled' as [_ Hled2'].
    destruct Hled2' as [(Hd0 & _)|Hled2'];
      [cbn [s_drop] in Hd0; lia|].
    destruct Hled2' as (_ & Hcurr'b & Hused'e & Hnext'b & Hused'u & _).
    cbn [s_curr s_used s_next] in Hcurr'b, Hused'e, Hnext'b, Hused'u.
    (* normalize the shifts *)
    assert (Hcu1 : 1 <= cu <= 15 - x_root c) by exact Hcurr'b.
    assert (Hshcu : Z.shiftl 1 cu = 2 ^ cu) by (apply shiftl1; lia).
    assert (Hcurnn : 0 <= s_curr st).
    { destruct Hphase as [(_ & Hc & _)|(Hd & _)]; [lia|].
      destruct Hled as [_ Hled2].
      destruct Hled2 as [(Hd0 & _)|(_ & Hcb & _)]; lia. }
    assert (Hshc : Z.shiftl 1 (s_curr st) = 2 ^ (s_curr st))
      by (apply shiftl1; lia).
    rewrite Hshcu in Hused'e, Hused'u, Hpos' |- *.
    rewrite Hshc in Hused'e, Hnext'b, Hpos' |- *.
    assert (Hcup : 0 < 2 ^ cu) by (apply pow2_pos_z; lia).
    assert (Hnx'u : s_next st + 2 ^ (s_curr st) < 65536) by lia.
    assert (Hnx'l : 2 ^ x_root c <= s_next st + 2 ^ (s_curr st))
      by exact Hnext'b.
    (* pointer readbacks *)
    assert (Hpb : c_bits (mkCodeT cu (x_root c)
                            (s_next st + 2 ^ (s_curr st))) = x_root c)
      by (apply bits_mkCodeT; lia).
    assert (Hpo : c_op (mkCodeT cu (x_root c)
                          (s_next st + 2 ^ (s_curr st))) = cu)
      by (apply op_mkCodeT_id; lia).
    assert (Hpv : c_val (mkCodeT cu (x_root c)
                           (s_next st + 2 ^ (s_curr st)))
                  = s_next st + 2 ^ (s_curr st))
      by (apply val_mkCodeT_id; lia).
    assert (Hlo'b : 0 <= lo' < 2 ^ x_root c).
    { rewrite Hlow'. apply Z.mod_pos_bound. apply pow2_pos_z. lia. }
    (* the st' position link, split at the root boundary *)
    unfold Pos in Hpos'. cbn [s_count] in Hpos'.
    rewrite HPadv in Hpos'.
    rewrite (pos_split_phase2 (x_root c) len1 huff1) in Hpos'
      by (try exact Hrl'; lia).
    rewrite <- Hlow' in Hpos'.
    set (tl' := zrev (Z.to_nat len1 - Z.to_nat (x_root c))
                  (huff1 / 2 ^ x_root c)) in *.
    assert (Htl'0 : 0 <= tl') by apply zrev_nonneg.
    assert (Htl' : tl' * 2 ^ (15 - len1) < 2 ^ (15 - x_root c)).
    { assert (Hz : tl' < 2 ^ (len1 - x_root c)).
      { pose proof (zrev_lt (Z.to_nat len1 - Z.to_nat (x_root c))
                      (huff1 / 2 ^ x_root c)) as Hz0.
        replace (Z.of_nat (Z.to_nat len1 - Z.to_nat (x_root c)))
          with (len1 - x_root c) in Hz0 by lia.
        exact Hz0. }
      assert (Hpp : 2 ^ (len1 - x_root c) * 2 ^ (15 - len1)
                    = 2 ^ (15 - x_root c))
        by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
      assert (Hp15 : 0 < 2 ^ (15 - len1)) by (apply pow2_pos_z; lia).
      clear -Hz Hpp Hp15 Htl'0. nia. }
    set (q := tl' * 2 ^ (15 - len1)) in *.
    assert (Hq0 : 0 <= q).
    { apply Z.mul_nonneg_nonneg; [exact Htl'0|].
      apply Z.pow_nonneg. lia. }
    clearbody q. clear Htl'0. clearbody tl'.
    assert (Hp15len : 0 < 2 ^ (15 - s_len st)) by (apply pow2_pos_z; lia).
    (* goal massage: expose P' and fold it as Pos st + step *)
    unfold Own, Pos. cbn [s_tbl s_next s_curr s_drop s_low s_count].
    rewrite HPadv.
    change (it_mass 15%nat 1 cnt0 - it_mass 15%nat 1 (s_count st))
      with (Pos (it_mass 15%nat 1 cnt0) st) in Hpos' |- *.
    (* the new window opens exactly at P' *)
    assert (Hstart' : Pos (it_mass 15%nat 1 cnt0) st + 2 ^ (15 - s_len st)
                      = zrev (Z.to_nat (x_root c)) lo'
                        * 2 ^ (15 - x_root c)).
    { destruct Hphase as [(Hd & Hc & Hnx & Hlow & Hlr)
                         |(Hd & Hrl & Hnx2 & Hlow2 & Hlb)].
      - (* phase-1 origin: both sides are multiples of u *)
        assert (Hpm : 2 ^ (15 - s_len st)
                      = 2 ^ (x_root c - s_len st) * 2 ^ (15 - x_root c))
          by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
        assert (HD : Pos (it_mass 15%nat 1 cnt0) st
                     = (zrev (Z.to_nat (s_len st)) (s_huff st)
                        * 2 ^ (x_root c - s_len st)) * 2 ^ (15 - x_root c)).
        { unfold Pos. unfold Pos in Hpos. rewrite Hpos, Hpm. ring. }
        set (D := zrev (Z.to_nat (s_len st)) (s_huff st)
                  * 2 ^ (x_root c - s_len st)) in *.
        set (E := 2 ^ (x_root c - s_len st)) in *.
        set (B := zrev (Z.to_nat (x_root c)) lo') in *.
        rewrite HD, Hpm in Hpos' |- *.
        fold E in Hpos' |- *.
        clearbody D E B.
        assert (Hcases : D + E <= B - 1 \/ D + E = B \/ B + 1 <= D + E)
          by lia.
        destruct Hcases as [Hlt|[Heq|Hgt]].
        + exfalso.
          assert (HA : D * 2 ^ (15 - x_root c) + E * 2 ^ (15 - x_root c)
                         + 2 ^ (15 - x_root c)
                       <= B * 2 ^ (15 - x_root c))
            by (clear -Hlt Hup; nia).
          clear -HA Hpos' Hq0 Hup. lia.
        + rewrite <- Heq. ring.
        + exfalso.
          assert (HA : B * 2 ^ (15 - x_root c) + 2 ^ (15 - x_root c)
                       <= D * 2 ^ (15 - x_root c)
                          + E * 2 ^ (15 - x_root c))
            by (clear -Hgt Hup; nia).
          clear -HA Hpos' Htl'. lia.
      - (* phase-2 origin: window trichotomy *)
        apply Bool.andb_true_iff in Hcre.
        destruct Hcre as [_ Hcre2].
        apply Bool.negb_true_iff, Z.eqb_neq in Hcre2.
        assert (Hlob : 0 <= s_low st < 2 ^ x_root c).
        { rewrite Hlow2. apply Z.mod_pos_bound. apply pow2_pos_z. lia. }
        assert (Hzne : zrev (Z.to_nat (x_root c)) lo'
                       <> zrev (Z.to_nat (x_root c)) (s_low st)).
        { intro Hzeq. apply Hcre2.
          apply (zrev_inj (Z.to_nat (x_root c)));
            [rewrite to_nat_pow by lia; exact Hlo'b
            |rewrite to_nat_pow by lia; exact Hlob
            |exact Hzeq]. }
        pose proof (pos_in_window (x_root c) (s_len st) (s_huff st)
                      ltac:(lia) Hrl ltac:(lia) Hhuff) as [Hwlo Hwhi].
        rewrite <- Hlow2 in Hwlo, Hwhi.
        rewrite <- Hpos in Hwlo, Hwhi.
        assert (Hcases : zrev (Z.to_nat (x_root c)) lo' + 1
                           <= zrev (Z.to_nat (x_root c)) (s_low st)
                         \/ zrev (Z.to_nat (x_root c)) (s_low st) + 1
                           <= zrev (Z.to_nat (x_root c)) lo') by lia.
        destruct Hcases as [Hlt|Hgt].
        + exfalso.
          assert (HA : zrev (Z.to_nat (x_root c)) lo' * 2 ^ (15 - x_root c)
                         + 2 ^ (15 - x_root c)
                       <= zrev (Z.to_nat (x_root c)) (s_low st)
                          * 2 ^ (15 - x_root c))
            by (clear -Hlt Hup; nia).
          clear -Hpos' Hwlo HA Htl' Hp15len Hq0. lia.
        + assert (HA : zrev (Z.to_nat (x_root c)) (s_low st)
                         * 2 ^ (15 - x_root c) + 2 ^ (15 - x_root c)
                       <= zrev (Z.to_nat (x_root c)) lo'
                          * 2 ^ (15 - x_root c))
            by (clear -Hgt Hup; nia).
          clear -Hpos' Hwhi HA Hq0. lia. }
    split.
    + (* OwnBelow at st' *)
      apply own_below_tset_out; [exact Hlo'b| |].
      { intros i Hi Hgi Hieq. subst i.
        pose proof (zrev_nonneg (Z.to_nat (x_root c)) lo') as Hz2.
        clear -Hgi Hstart' Hup Hz2. nia. }
      destruct Hphase as [(Hd & Hc & Hnx & Hlow & Hlr)
                         |(Hd & Hrl & Hnx2 & Hlow2 & Hlb)].
      * (* phase-1 origin: fresh cells from the short fill *)
        apply (own_below_mono_nxt _ _ _ _ (s_next st));
          [pose proof (Z.pow_nonneg 2 (s_curr st) ltac:(lia)); lia|].
        exact (Hfs Hd Hbelow).
      * (* phase-2 origin: P' = top(low), the old window closes *)
        specialize (Hopen Hd).
        destruct (Hfl Hd Hbelow Hopen) as (Hf1 & Hf2 & Hf3).
        pose proof (own_below_mono_nxt _ _ _ _ (s_next st)
                      (s_next st + 2 ^ (s_curr st)) _
                      ltac:(pose proof (Z.pow_nonneg 2 (s_curr st)
                                          ltac:(lia)); lia) Hf1)
          as Hf1w.
        pose proof (pos_in_window (x_root c) (s_len st) (s_huff st)
                      ltac:(lia) Hrl ltac:(lia) Hhuff) as [Hwlo Hwhi].
        rewrite <- Hlow2 in Hwlo, Hwhi.
        rewrite <- Hpos in Hwlo, Hwhi.
        intros j Hj Hg.
        destruct (Z.eq_dec j (s_low st)) as [->|Hnej].
        { assert (Hbound : Pos (it_mass 15%nat 1 cnt0) st
                             + 2 ^ (15 - s_len st)
                           = UnitStart (x_root c) (s_low st)
                             + 2 ^ (15 - x_root c)).
          { unfold UnitStart. clear -Hg Hwhi Hup. nia. }
          right. exact (Hf3 Hbound). }
        { assert (Hjb : 0 <= j < 2 ^ Z.of_nat (Z.to_nat (x_root c)))
            by (rewrite to_nat_pow by lia; exact Hj).
          assert (Hlob : 0 <= s_low st
                         < 2 ^ Z.of_nat (Z.to_nat (x_root c))).
          { rewrite to_nat_pow by lia. rewrite Hlow2.
            apply Z.mod_pos_bound. apply pow2_pos_z. lia. }
          assert (Hzne2 : zrev (Z.to_nat (x_root c)) j
                          <> zrev (Z.to_nat (x_root c)) (s_low st)).
          { intro Hzeq. apply Hnej.
            exact (zrev_inj (Z.to_nat (x_root c)) j (s_low st)
                     Hjb Hlob Hzeq). }
          assert (H2 : (zrev (Z.to_nat (x_root c)) j + 1)
                         * 2 ^ (15 - x_root c)
                       <= zrev (Z.to_nat (x_root c)) (s_low st)
                          * 2 ^ (15 - x_root c) + 2 ^ (15 - x_root c))
            by lia.
          assert (Hle1 : zrev (Z.to_nat (x_root c)) j + 1
                         <= zrev (Z.to_nat (x_root c)) (s_low st) + 1)
            by (clear -H2 Hup; nia).
          assert (Hle2 : zrev (Z.to_nat (x_root c)) j + 1
                         <= zrev (Z.to_nat (x_root c)) (s_low st))
            by lia.
          assert (Hgle : (zrev (Z.to_nat (x_root c)) j + 1)
                           * 2 ^ (15 - x_root c)
                         <= zrev (Z.to_nat (x_root c)) (s_low st)
                            * 2 ^ (15 - x_root c))
            by (clear -Hle2 Hup; nia).
          apply Hf1w; [exact Hj|]. lia. }
    + (* the fresh open window *)
      intros _.
      unfold OwnOpen.
      rewrite tset_same, Hpb, Hpo, Hpv.
      split; [reflexivity|].
      split; [reflexivity|].
      split; [reflexivity|].
      split; [exact Hcu1|].
      split; [exact Hnx'l|].
      intros k Hk Hgk. exfalso.
      assert (Hd0 : 0 < 2 ^ (15 - x_root c - cu))
        by (apply pow2_pos_z; lia).
      pose proof (zrev_nonneg (Z.to_nat cu) k) as Hz3.
      clear -Hgk Hstart' Hd0 Hz3. nia.
  - (* NO-CREATION exit *)
    intro Hstep. injection Hstep as Heq. subst st'.
    destruct Hinv' as (Hlen' & Hhuff' & _ & _ & _ & Hpos' & _ & Hphase').
    cbn [s_len s_huff s_low s_count s_drop] in Hlen', Hhuff', Hpos',
      Hphase'.
    unfold Own, Pos. cbn [s_tbl s_next s_curr s_drop s_low s_count].
    rewrite HPadv.
    change (it_mass 15%nat 1 cnt0 - it_mass 15%nat 1 (s_count st))
      with (Pos (it_mass 15%nat 1 cnt0) st).
    destruct Hphase as [(Hd & Hc & Hnx & Hlow & Hlr)
                       |(Hd & Hrl & Hnx2 & Hlow2 & Hlb)].
    + (* phase 1 stays phase 1 *)
      split.
      * exact (Hfs Hd Hbelow).
      * intro Habs. rewrite Hd in Habs. lia.
    + (* phase 2 continues in the same window *)
      specialize (Hopen Hd).
      destruct (Hfl Hd Hbelow Hopen) as (Hf1 & Hf2 & _).
      destruct Hphase' as [(Hd0 & _)|(_ & Hrl' & _ & Hlow' & _)];
        [lia|].
      cbn [s_len s_huff s_low] in Hrl', Hlow'.
      unfold Pos in Hpos'. cbn [s_count] in Hpos'.
      rewrite HPadv in Hpos'.
      change (it_mass 15%nat 1 cnt0 - it_mass 15%nat 1 (s_count st))
        with (Pos (it_mass 15%nat 1 cnt0) st) in Hpos'.
      rewrite (pos_split_phase2 (x_root c) len1 huff1) in Hpos'
        by (try exact Hrl'; lia).
      rewrite <- Hlow' in Hpos'.
      set (tl' := zrev (Z.to_nat len1 - Z.to_nat (x_root c))
                    (huff1 / 2 ^ x_root c)) in *.
      assert (Htl'0 : 0 <= tl') by apply zrev_nonneg.
      assert (Htl' : tl' * 2 ^ (15 - len1) < 2 ^ (15 - x_root c)).
      { assert (Hz : tl' < 2 ^ (len1 - x_root c)).
        { pose proof (zrev_lt (Z.to_nat len1 - Z.to_nat (x_root c))
                        (huff1 / 2 ^ x_root c)) as Hz0.
          replace (Z.of_nat (Z.to_nat len1 - Z.to_nat (x_root c)))
            with (len1 - x_root c) in Hz0 by lia.
          exact Hz0. }
        assert (Hpp : 2 ^ (len1 - x_root c) * 2 ^ (15 - len1)
                      = 2 ^ (15 - x_root c))
          by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
        assert (Hp15 : 0 < 2 ^ (15 - len1)) by (apply pow2_pos_z; lia).
        clear -Hz Hpp Hp15 Htl'0. nia. }
      set (q := tl' * 2 ^ (15 - len1)) in *.
      assert (Hq0 : 0 <= q).
      { apply Z.mul_nonneg_nonneg; [exact Htl'0|].
        apply Z.pow_nonneg. lia. }
      clearbody q. clear Htl'0. clearbody tl'.
      pose proof (pos_in_window (x_root c) (s_len st) (s_huff st)
                    ltac:(lia) Hrl ltac:(lia) Hhuff) as [Hwlo Hwhi].
      rewrite <- Hlow2 in Hwlo, Hwhi.
      rewrite <- Hpos in Hwlo, Hwhi.
      split.
      * intros j Hj Hg.
        destruct (Z.eq_dec j (s_low st)) as [->|Hnej].
        { exfalso.
          assert (HgD : zrev (Z.to_nat (x_root c)) (s_low st)
                          * 2 ^ (15 - x_root c) + 2 ^ (15 - x_root c)
                        <= Pos (it_mass 15%nat 1 cnt0) st
                           + 2 ^ (15 - s_len st))
            by (clear -Hg Hup; nia).
          clear -HgD Hpos' Htl' Hq0. lia. }
        { assert (Hjb : 0 <= j < 2 ^ Z.of_nat (Z.to_nat (x_root c)))
            by (rewrite to_nat_pow by lia; exact Hj).
          assert (Hlob : 0 <= s_low st
                         < 2 ^ Z.of_nat (Z.to_nat (x_root c))).
          { rewrite to_nat_pow by lia. rewrite Hlow2.
            apply Z.mod_pos_bound. apply pow2_pos_z. lia. }
          assert (Hzne2 : zrev (Z.to_nat (x_root c)) j
                          <> zrev (Z.to_nat (x_root c)) (s_low st)).
          { intro Hzeq. apply Hnej.
            exact (zrev_inj (Z.to_nat (x_root c)) j (s_low st)
                     Hjb Hlob Hzeq). }
          assert (H2 : (zrev (Z.to_nat (x_root c)) j + 1)
                         * 2 ^ (15 - x_root c)
                       <= zrev (Z.to_nat (x_root c)) (s_low st)
                          * 2 ^ (15 - x_root c) + 2 ^ (15 - x_root c)).
          { clear -Hg Hpos' Htl' Hq0. lia. }
          assert (Hle1 : zrev (Z.to_nat (x_root c)) j + 1
                         <= zrev (Z.to_nat (x_root c)) (s_low st) + 1)
            by (clear -H2 Hup; nia).
          assert (Hle2 : zrev (Z.to_nat (x_root c)) j + 1
                         <= zrev (Z.to_nat (x_root c)) (s_low st))
            by lia.
          assert (Hgle : (zrev (Z.to_nat (x_root c)) j + 1)
                           * 2 ^ (15 - x_root c)
                         <= zrev (Z.to_nat (x_root c)) (s_low st)
                            * 2 ^ (15 - x_root c))
            by (clear -Hle2 Hup; nia).
          apply Hf1; [exact Hj|]. lia. }
      * intro Hd2. exact Hf2.
Qed.

(** The break trip: the same fill, no creation, plus the endgame
    arithmetic. *)
Lemma own_step_break : forall c cnt0 (l1 : list nat) st st1,
  CovCtxOk c cnt0 ->
  CovInv c cnt0 st ->
  SubLedger (x_type c) c cnt0 st ->
  arr_eq_on (x_lens c) (zlens l1) 0 (Z.of_nat (length l1)) ->
  x_codes c = Z.of_nat (length l1) ->
  Own c cnt0 l1 (ent_of c l1) st ->
  it_step c st = ItBreak st1 ->
  OwnFin c cnt0 l1 (ent_of c l1) st1 /\ BreakShape c cnt0 st1.
Proof.
  intros c cnt0 l1 st st1 Hctx Hinv Hled Hxl Hxc Hown Hstep.
  pose proof (own_fill_short c cnt0 l1 st Hctx Hinv Hxl Hxc) as Hfs.
  pose proof (own_fill_long c cnt0 l1 st Hctx Hinv Hled Hxl Hxc) as Hfl.
  destruct Hown as [Hbelow Hopen].
  pose proof Hctx as Hctx0.
  destruct Hctx0 as (Hroot & Hmask & Hmx & Hmxnz & Hmxz & Hnn & Hcodes
                     & Hlens & Hcnt0 & Hwork & Hupper & Hcase & Hrootmx).
  pose proof Hinv as Hinv0.
  destruct Hinv0 as (Hlen & Hhuff & HwinL & HwinU & Hcnt & Hpos & Hcov
                     & Hphase).
  unfold it_step in Hstep. cbv zeta in Hstep.
  set (cnt1 := zset (s_count st) (s_len st) (s_count st (s_len st) - 1))
    in *.
  set (huff1 := it_rev_incr (s_huff st) (s_len st)) in *.
  set (T1 := it_fill (Z.to_nat (Z.shiftl 1 (s_curr st)
                       / Z.shiftl 1 (s_len st - s_drop st)))
              (s_tbl st) (s_next st + Z.shiftr (s_huff st) (s_drop st))
              (Z.shiftl 1 (s_len st - s_drop st)) (it_here c st)) in *.
  revert Hstep.
  destruct ((cnt1 (s_len st) =? 0) && (s_len st =? x_max c))%bool eqn:Hbrk;
    intro Hstep.
  2:{ exfalso. revert Hstep.
      repeat match goal with
             | |- (if ?b then _ else _) = _ -> _ => destruct b
             end; intro Hstep; discriminate Hstep. }
  apply Bool.andb_true_iff in Hbrk. destruct Hbrk as [Hhit0 Hmxeq].
  apply Z.eqb_eq in Hhit0. apply Z.eqb_eq in Hmxeq.
  injection Hstep as Heq. subst st1.
  (* the trip's position advance *)
  assert (HPadv : it_mass 15%nat 1 cnt0 - it_mass 15%nat 1 cnt1
                  = (it_mass 15%nat 1 cnt0 - it_mass 15%nat 1 (s_count st))
                    + 2 ^ (15 - s_len st)).
  { unfold cnt1. apply pos_advance. lia. }
  (* the counts are exhausted *)
  assert (Hmass1 : it_mass 15%nat 1 cnt1 = 0).
  { apply it_mass_zero_on. intros l Hl.
    unfold cnt1.
    destruct (Z.eq_dec l (s_len st)) as [->|Hne].
    - pose proof Hhit0 as Hh0. unfold cnt1 in Hh0.
      rewrite zset_same in Hh0 |- *. exact Hh0.
    - rewrite zset_other by exact Hne.
      rewrite (Hcnt l) by lia.
      destruct (Z.ltb_spec l (s_len st)); [reflexivity|].
      destruct (Z.eqb_spec l (s_len st)); [congruence|].
      apply Hmxz. lia. }
  split.
  { (* OwnFin *)
    unfold OwnFin, Pos.
    cbn [s_tbl s_next s_curr s_count].
    rewrite HPadv.
    change (it_mass 15%nat 1 cnt0 - it_mass 15%nat 1 (s_count st))
      with (Pos (it_mass 15%nat 1 cnt0) st).
    assert (Hc2nn : 0 <= 2 ^ (s_curr st)) by (apply Z.pow_nonneg; lia).
    destruct Hphase as [(Hd & Hc & Hnx & Hlow & Hlr)
                       |(Hd & Hrl & Hnx2 & Hlow2 & Hlb)].
    - (* phase 1: the fill's conclusion, region bound widened *)
      apply (own_below_mono_nxt _ _ _ _ (s_next st)); [lia|].
      exact (Hfs Hd Hbelow).
    - (* phase 2 *)
      specialize (Hopen Hd).
      destruct (Hfl Hd Hbelow Hopen) as (Hf1 & Hf2 & Hf3).
      pose proof (own_below_mono_nxt _ _ _ _ (s_next st)
                    (s_next st + 2 ^ (s_curr st)) _ ltac:(lia) Hf1) as Hf1w.
      pose proof (pos_in_window (x_root c) (s_len st) (s_huff st)
                    ltac:(lia) Hrl ltac:(lia) Hhuff) as [Hwlo Hwhi].
      rewrite <- Hlow2 in Hwlo, Hwhi.
      rewrite <- Hpos in Hwlo, Hwhi.
      intros j Hj Hg.
      assert (Hup : 0 < 2 ^ (15 - x_root c)) by (apply pow2_pos_z; lia).
      destruct (Z.eq_dec j (s_low st)) as [->|Hnej].
      + (* the open window completes exactly here *)
        assert (Hbound : Pos (it_mass 15%nat 1 cnt0) st
                           + 2 ^ (15 - s_len st)
                         = UnitStart (x_root c) (s_low st)
                           + 2 ^ (15 - x_root c)).
        { unfold UnitStart. clear -Hg Hwhi Hup. nia. }
        right. exact (Hf3 Hbound).
      + (* any other classified cell was already below P *)
        assert (Hjb : 0 <= j < 2 ^ Z.of_nat (Z.to_nat (x_root c)))
          by (rewrite to_nat_pow by lia; exact Hj).
        assert (Hlb2 : 0 <= s_low st < 2 ^ Z.of_nat (Z.to_nat (x_root c))).
        { rewrite to_nat_pow by lia. rewrite Hlow2.
          apply Z.mod_pos_bound. apply pow2_pos_z. lia. }
        assert (Hzne : zrev (Z.to_nat (x_root c)) j
                       <> zrev (Z.to_nat (x_root c)) (s_low st)).
        { intro Hzeq. apply Hnej.
          exact (zrev_inj (Z.to_nat (x_root c)) j (s_low st) Hjb Hlb2 Hzeq). }
        assert (Hgle : (zrev (Z.to_nat (x_root c)) j + 1)
                         * 2 ^ (15 - x_root c)
                       <= zrev (Z.to_nat (x_root c)) (s_low st)
                          * 2 ^ (15 - x_root c)).
        { assert (H2 : (zrev (Z.to_nat (x_root c)) j + 1)
                         * 2 ^ (15 - x_root c)
                       <= zrev (Z.to_nat (x_root c)) (s_low st)
                          * 2 ^ (15 - x_root c) + 2 ^ (15 - x_root c))
            by lia.
          assert (Hle1 : zrev (Z.to_nat (x_root c)) j + 1
                         <= zrev (Z.to_nat (x_root c)) (s_low st) + 1)
            by (clear -H2 Hup; nia).
          assert (Hle2 : zrev (Z.to_nat (x_root c)) j + 1
                         <= zrev (Z.to_nat (x_root c)) (s_low st))
            by lia.
          clear -Hle2 Hup. nia. }
        apply Hf1w; [exact Hj|]. lia. }
  { (* BreakShape *)
    unfold BreakShape.
    cbn [s_huff s_next s_drop s_len s_count].
    split; [exact Hmass1|].
    split.
    - (* complete: huff wraps to 0 *)
      intro HM0.
      assert (HE : (zrev (Z.to_nat (s_len st)) (s_huff st) + 1)
                     * 2 ^ (15 - s_len st) = 2 ^ 15).
      { unfold Pos in Hpos.
        clear -HPadv Hmass1 HM0 Hpos. nia. }
      assert (Hpw : 2 ^ (s_len st) * 2 ^ (15 - s_len st) = 2 ^ 15)
        by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
      assert (Hpl : 0 < 2 ^ (15 - s_len st)) by (apply pow2_pos_z; lia).
      assert (Hzr : zrev (Z.to_nat (s_len st)) (s_huff st)
                    = 2 ^ (s_len st) - 1).
      { clear -HE Hpw Hpl. nia. }
      assert (Hhf : s_huff st = 2 ^ (s_len st) - 1).
      { apply (zrev_inj (Z.to_nat (s_len st))).
        - rewrite to_nat_pow by lia. exact Hhuff.
        - rewrite to_nat_pow by lia.
          pose proof (pow2_pos_z (s_len st) ltac:(lia)). lia.
        - rewrite Hzr.
          rewrite <- (to_nat_pow (s_len st)) by lia.
          rewrite zrev_ones.
          rewrite to_nat_pow by lia. reflexivity. }
      unfold huff1. rewrite Hhf.
      apply it_rev_incr_ones. lia.
    - (* incomplete: the single one-bit trip *)
      intros Hmx1 HM14.
      assert (Hlen1 : s_len st = 1) by lia.
      destruct Hphase as [(Hd & Hc & Hnx & Hlow & Hlr)
                         |(Hd & Hrl & Hnx2 & Hlow2 & Hlb)];
        [|exfalso; lia].
      assert (HP0 : Pos (it_mass 15%nat 1 cnt0) st = 0).
      { unfold Pos. rewrite Hlen1 in HPadv. lia. }
      assert (Hzr0 : zrev (Z.to_nat (s_len st)) (s_huff st) = 0).
      { unfold Pos in Hpos.
        assert (Hpl : 0 < 2 ^ (15 - s_len st)) by (apply pow2_pos_z; lia).
        unfold Pos in HP0.
        clear -Hpos HP0 Hpl. nia. }
      assert (Hh0 : s_huff st = 0).
      { apply (zrev_inj (Z.to_nat (s_len st))).
        - rewrite to_nat_pow by lia. exact Hhuff.
        - rewrite to_nat_pow by lia.
          pose proof (pow2_pos_z (s_len st) ltac:(lia)). lia.
        - rewrite Hzr0, zrev_zero. reflexivity. }
      split.
      { unfold huff1. rewrite Hh0, Hlen1.
        rewrite it_rev_incr_zero by lia. reflexivity. }
      split; [exact Hnx|].
      split; [exact Hd|].
      exact Hlen1. }
Qed.

(** Loop transport, nom_loop pattern: CovInv via cov_step_cont,
    SubLedger via ledger_step_cont. *)
Lemma own_loop : forall n c cnt0 (l1 : list nat) st st1,
  CovCtxOk c cnt0 ->
  CovInv c cnt0 st ->
  SubLedger (x_type c) c cnt0 st ->
  arr_eq_on (x_lens c) (zlens l1) 0 (Z.of_nat (length l1)) ->
  x_codes c = Z.of_nat (length l1) ->
  (x_type c = CT_LENS \/ x_type c = CT_DISTS \/ x_max c <= x_root c) ->
  (forall st0, LeafShape (x_type c) (it_here c st0)) ->
  Own c cnt0 l1 (ent_of c l1) st ->
  it_loop n c st = Some (ItBreak st1) ->
  OwnFin c cnt0 l1 (ent_of c l1) st1 /\ BreakShape c cnt0 st1.
Proof.
  induction n as [|n IH]; intros c cnt0 l1 st st1 Hctx Hinv Hled Hxl Hxc
                                 Hty Hlfs Hown Hl;
    cbn [it_loop] in Hl; [discriminate Hl|].
  destruct (it_step c st) as [stm|stm|t'] eqn:Hs.
  - exact (IH c cnt0 l1 stm st1 Hctx
             (cov_step_cont c cnt0 st stm Hctx Hinv Hs)
             (ledger_step_cont (x_type c) c cnt0 st stm eq_refl Hty Hctx
                Hinv Hled (Hlfs st) Hs)
             Hxl Hxc Hty Hlfs
             (own_step_cont c cnt0 l1 st stm Hctx Hinv Hled (Hlfs st)
                Hxl Hxc Hty Hown Hs)
             Hl).
  - (* which name survives [injection ... as <-] is not ours to predict;
       let unification take the state from [Hs] (cov_loop's own note) *)
    injection Hl as <-.
    exact (own_step_break c cnt0 l1 st _ Hctx Hinv Hled Hxl Hxc
             Hown Hs).
  - discriminate Hl.
Qed.

(* ------------------------------------------------------------------ *)
(** ** it_pre projections the model tier needs (fork helpers; the
    guard-chain dissection mirrors ItGSubCover's it_pre_go_* lemmas). *)

Lemma it_pre_go_argsc : forall ty lens codes root0 t0 c st,
  it_pre ty lens codes root0 t0 = PreGo c st ->
  x_lens c = lens /\ x_codes c = codes.
Proof.
  intros ty lens codes root0 t0 c st H.
  unfold it_pre in H. cbv zeta in H.
  destruct (Z.eqb (it_findmax 15%nat MAXBITS
                     (it_count (Z.to_nat codes) 0 lens zzero)) 0);
    [discriminate H|].
  destruct (it_kraft 15%nat 1 1 (it_count (Z.to_nat codes) 0 lens zzero))
    as [lft|]; [|discriminate H].
  destruct (it_incomplete ty lft _); [discriminate H|].
  destruct (it_enough ty _); [discriminate H|].
  pose proof (f_equal (fun r => match r with PreGo a _ => a | _ => c end) H) as Hc;
    clear H; cbv beta iota in Hc. (* fast-shadow: base = [injection H as Hc _.], 36-49s each: injection's
    normalization unfolds the it_findmax/it_findmin fuel towers inside the
    record; this projection keeps Hc's RHS folded (definitionally equal,
    Qed-sealed within this lemma). *) rewrite <- Hc. cbn [x_lens x_codes].
  split; reflexivity.
Qed.

Lemma it_pre_go_codes_match : forall lens codes root0 t0 c st,
  it_pre CT_CODES lens codes root0 t0 = PreGo c st ->
  x_match c = 20.
Proof.
  intros lens codes root0 t0 c st H.
  unfold it_pre in H. cbv zeta in H.
  destruct (Z.eqb (it_findmax 15%nat MAXBITS
                     (it_count (Z.to_nat codes) 0 lens zzero)) 0);
    [discriminate H|].
  destruct (it_kraft 15%nat 1 1 (it_count (Z.to_nat codes) 0 lens zzero))
    as [lft|]; [|discriminate H].
  destruct (it_incomplete CT_CODES lft _); [discriminate H|].
  destruct (it_enough CT_CODES _); [discriminate H|].
  pose proof (f_equal (fun r => match r with PreGo a _ => a | _ => c end) H) as Hc;
    clear H; cbv beta iota in Hc. (* fast-shadow: base = [injection H as Hc _.], 36-49s each: injection's
    normalization unfolds the it_findmax/it_findmin fuel towers inside the
    record; this projection keeps Hc's RHS folded (definitionally equal,
    Qed-sealed within this lemma). *) rewrite <- Hc. cbn [x_match].
  vm_compute (Z.eqb CT_CODES CT_LENS).
  vm_compute (Z.eqb CT_CODES CT_DISTS).
  reflexivity.
Qed.

Lemma it_pre_go_max_le_root : forall ty lens codes root0 t0 c st,
  it_pre ty lens codes root0 t0 = PreGo c st ->
  x_max c <= root0 ->
  x_max c <= x_root c.
Proof.
  intros ty lens codes root0 t0 c st H.
  unfold it_pre in H. cbv zeta in H.
  destruct (Z.eqb (it_findmax 15%nat MAXBITS
                     (it_count (Z.to_nat codes) 0 lens zzero)) 0);
    [discriminate H|].
  destruct (it_kraft 15%nat 1 1 (it_count (Z.to_nat codes) 0 lens zzero))
    as [lft|]; [|discriminate H].
  destruct (it_incomplete ty lft _); [discriminate H|].
  destruct (it_enough ty _); [discriminate H|].
  pose proof (f_equal (fun r => match r with PreGo a _ => a | _ => c end) H) as Hc;
    clear H; cbv beta iota in Hc. (* fast-shadow: base = [injection H as Hc _.], 36-49s each: injection's
    normalization unfolds the it_findmax/it_findmin fuel towers inside the
    record; this projection keeps Hc's RHS folded (definitionally equal,
    Qed-sealed within this lemma). *)
  assert (Hmax : x_max c
                 = it_findmax 15%nat MAXBITS
                     (it_count (Z.to_nat codes) 0 lens zzero))
    by (rewrite <- Hc; reflexivity).
  assert (Hroot : x_root c
      = if (if it_findmax 15%nat MAXBITS
                (it_count (Z.to_nat codes) 0 lens zzero) <? root0
            then it_findmax 15%nat MAXBITS
                   (it_count (Z.to_nat codes) 0 lens zzero)
            else root0)
           <? it_findmin 16%nat 1
                (it_findmax 15%nat MAXBITS
                   (it_count (Z.to_nat codes) 0 lens zzero))
                (it_count (Z.to_nat codes) 0 lens zzero)
        then it_findmin 16%nat 1
               (it_findmax 15%nat MAXBITS
                  (it_count (Z.to_nat codes) 0 lens zzero))
               (it_count (Z.to_nat codes) 0 lens zzero)
        else if it_findmax 15%nat MAXBITS
                  (it_count (Z.to_nat codes) 0 lens zzero) <? root0
             then it_findmax 15%nat MAXBITS
                    (it_count (Z.to_nat codes) 0 lens zzero)
             else root0)
    by (rewrite <- Hc; reflexivity).
  intro Hle.
  rewrite Hmax in Hle |- *. rewrite Hroot.
  set (MX := it_findmax 15%nat MAXBITS
               (it_count (Z.to_nat codes) 0 lens zzero)) in *.
  set (MN := it_findmin 16%nat 1 MX
               (it_count (Z.to_nat codes) 0 lens zzero)) in *.
  clearbody MX MN.
  destruct (MX <? root0) eqn:E1.
  - apply Z.ltb_lt in E1. cbv beta match.
    destruct (MX <? MN) eqn:E2; cbv beta match.
    + apply Z.ltb_lt in E2. lia.
    + lia.
  - apply Z.ltb_ge in E1. cbv beta match.
    destruct (root0 <? MN) eqn:E2; cbv beta match.
    + apply Z.ltb_lt in E2. lia.
    + lia.
Qed.

Lemma it_pre_go_codes_pos : forall ty lens codes root0 t0 c st,
  0 <= codes ->
  it_pre ty lens codes root0 t0 = PreGo c st ->
  0 < codes.
Proof.
  intros ty lens codes root0 t0 c st Hnn H.
  destruct (Z.eqb_spec codes 0) as [E|E]; [|lia].
  subst codes. exfalso.
  unfold it_pre in H. cbv zeta in H.
  change (Z.to_nat 0) with 0%nat in H.
  cbn [it_count] in H.
  revert H.
  destruct (Z.eqb_spec (it_findmax 15%nat MAXBITS zzero) 0) as [E2|E2];
    intro H; [discriminate H|].
  apply E2. vm_compute. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The model-level theorem (piece 5)

    STATEMENT DELTA (fork, flagged loudly): TWO added length premises,
    [ty = CT_CODES -> |l1| <= 19] and [ty = CT_LENS -> |l1| <= 286].
    They are REQUIRED: own_loop's LeafShape-family premise is discharged
    by here_leafshape_codes/lens (ItGSubCover), whose work-range
    premises (<= 18 / <= 287) are sort outputs bounded only by the code
    count.  Both consumers instantiate at the real calls (CODES = 19
    codes; LENS <= 286), so the premises are free there.  The DISTS
    case is covered by the existing <= 30 premise. *)
Theorem fill_class_holds : forall ty (l1 : list nat) (lens : zarr)
                                  root0 t0 c st out,
  (ty = CT_CODES \/ ty = CT_LENS \/ ty = CT_DISTS) ->
  (ty = CT_DISTS -> Z.of_nat (length l1) <= 30) ->
  (ty = CT_CODES -> Z.of_nat (length l1) <= 19) ->
  (ty = CT_LENS -> Z.of_nat (length l1) <= 286) ->
  (ty = CT_CODES -> forall len, In len l1 -> Z.of_nat len <= root0) ->
  (forall len, In len l1 -> (len <= 15)%nat) ->
  1 <= root0 <= 15 ->
  arr_eq_on lens (zlens l1) 0 (Z.of_nat (length l1)) ->
  it_pre ty lens (Z.of_nat (length l1)) root0 t0
    = PreGo c st ->
  it_model ty lens (Z.of_nat (length l1)) root0 t0
    = Some out ->
  o_ret out = 0 ->
  zr_fill_class (o_tbl out) (o_bits out) l1 (ent_of c l1).
Proof.
  intros ty l1 lens root0 t0 c st out Hty3 Hd30 Hc19 Hl286 Hcap Hlen15
         Hroot0 Hagree Hpre Hmodel Hret.
  pose proof Hagree as HagU. unfold arr_eq_on in HagU.
  set (codes := Z.of_nat (length l1)) in *.
  assert (Hcodes0 : 0 <= codes) by (unfold codes; lia).
  assert (Hlensb : forall i, 0 <= i < codes -> 0 <= lens i <= 15).
  { intros i Hi.
    rewrite (HagU i) by (unfold codes in Hi; lia).
    unfold zlens.
    assert (Hlt : (Z.to_nat i < length l1)%nat)
      by (unfold codes in Hi; lia).
    pose proof (Hlen15 (nth (Z.to_nat i) l1 0%nat)
                  (nth_In l1 0%nat Hlt)).
    lia. }
  destruct (cov_pre ty lens codes root0 t0 c st Hcodes0 Hlensb Hroot0 Hpre)
    as [Hctx Hinv0].
  pose proof (ledger_pre ty lens codes root0 t0 c st Hcodes0 Hlensb Hroot0
                Hpre) as Hled0.
  set (cnt0 := sw_cnt lens codes) in *.
  pose proof (it_pre_go_type ty lens codes root0 t0 c st Hpre) as Hcty.
  rewrite <- Hcty in Hled0.
  destruct (it_pre_go_argsc ty lens codes root0 t0 c st Hpre) as [Hxl Hxc].
  pose proof (it_pre_go_codes_pos ty lens codes root0 t0 c st Hcodes0 Hpre)
    as Hcpos.
  pose proof (it_pre_go_work ty lens codes root0 t0 c st Hpre) as Hwk.
  assert (Hwr : forall s, 0 <= x_work c s < codes)
    by (intro s; rewrite Hwk; apply sort_work_range; exact Hcpos).
  assert (Hbr : forall b : nat,
             cnt0 (Z.of_nat b) = Z.of_nat (count_len l1 b)).
  { intro b. unfold cnt0, codes.
    apply sw_cnt_agree_count_len. exact Hagree. }
  pose proof Hctx as HctxC.
  destruct HctxC as (HrootB & _ & HmxB & Hmxnz & _ & _ & _ & _ & _ & _
                     & _ & Hcase & Hrootmx).
  assert (Htyd : x_type c = CT_LENS \/ x_type c = CT_DISTS
                 \/ x_max c <= x_root c).
  { rewrite Hcty.
    destruct Hty3 as [HtyC|[HtyL|HtyD]]; [right; right| |].
    - assert (Hmxr0 : x_max c <= root0).
      { destruct (Z_le_gt_dec (x_max c) root0) as [Hle|Hgt]; [exact Hle|].
        exfalso.
        assert (Hni : ~ In (Z.to_nat (x_max c)) l1).
        { intro Hin.
          pose proof (Hcap HtyC _ Hin) as Hb.
          lia. }
        pose proof (Hbr (Z.to_nat (x_max c))) as Hb2.
        rewrite Z2Nat.id in Hb2 by lia.
        apply Hmxnz. rewrite Hb2.
        unfold count_len.
        rewrite (count_occ_not_In Nat.eq_dec) in Hni.
        lia. }
      exact (it_pre_go_max_le_root ty lens codes root0 t0 c st Hpre Hmxr0).
    - left. exact HtyL.
    - right. left. exact HtyD. }
  assert (Hlfs : forall st0, LeafShape (x_type c) (it_here c st0)).
  { intro st0.
    destruct Hty3 as [HtyC|[HtyL|HtyD]].
    - subst ty. rewrite Hcty.
      apply here_leafshape_codes.
      + exact (it_pre_go_codes_match lens codes root0 t0 c st Hpre).
      + intro s. specialize (Hwr s). specialize (Hc19 eq_refl).
        unfold codes in Hwr. lia.
    - subst ty. rewrite Hcty.
      destruct (it_pre_go_lens_arrays lens codes root0 t0 c st Hpre)
        as (Hm & Hb & He).
      apply here_leafshape_lens; try assumption.
      intro s. specialize (Hwr s). specialize (Hl286 eq_refl).
      unfold codes in Hwr. lia.
    - subst ty. rewrite Hcty.
      destruct (it_pre_go_dists lens codes root0 t0 c st Hpre)
        as (Hm & Hb & He).
      apply here_leafshape_dists; try assumption.
      intro s. specialize (Hwr s). specialize (Hd30 eq_refl).
      unfold codes in Hwr. lia. }
  pose proof (it_pre_go_count ty lens codes root0 t0 c st Hpre) as Hcnt_st.
  destruct (it_pre_go_shape ty lens codes root0 t0 c st Hpre) as [Hdrop0 _].
  assert (Hown0 : Own c cnt0 l1 (ent_of c l1) st)
    by (apply (own_seed c cnt0 l1 (ent_of c l1) st Hcnt_st Hdrop0);
        exact HrootB).
  unfold it_model in Hmodel.
  rewrite Hpre in Hmodel. cbv beta match in Hmodel.
  revert Hmodel.
  destruct (it_loop (S (Z.to_nat codes)) c st) as [[st1|st1|tt]|] eqn:Hloop;
    intro Hmodel; try discriminate Hmodel.
  - (* ItBreak *)
    injection Hmodel as <-.
    cbn [o_tbl o_bits].
    assert (HagX : arr_eq_on (x_lens c) (zlens l1) 0
                     (Z.of_nat (length l1)))
      by (rewrite Hxl; exact Hagree).
    destruct (own_loop (S (Z.to_nat codes)) c cnt0 l1 st st1 Hctx Hinv0
                Hled0 HagX Hxc Htyd Hlfs Hown0 Hloop) as [HFin HBrk].
    destruct HBrk as (Hm0 & Hcompl & Hincompl).
    assert (HposM : Pos (it_mass 15%nat 1 cnt0) st1
                    = it_mass 15%nat 1 cnt0)
      by (unfold Pos; rewrite Hm0; lia).
    destruct Hcase as [HM15|[Hmx1 HM14]].
    + (* COMPLETE *)
      specialize (Hcompl HM15).
      assert (Hfin_id : it_finish st1 = s_tbl st1).
      { unfold it_finish. rewrite Hcompl. reflexivity. }
      rewrite Hfin_id.
      intros i Hi.
      assert (Hupos : 0 < 2 ^ (15 - x_root c)) by (apply pow2_pos_z; lia).
      assert (Hgi : (zrev (Z.to_nat (x_root c)) i + 1)
                      * 2 ^ (15 - x_root c)
                    <= Pos (it_mass 15%nat 1 cnt0) st1).
      { rewrite HposM, HM15.
        pose proof (zrev_lt (Z.to_nat (x_root c)) i) as Hzl.
        rewrite to_nat_pow in Hzl by lia.
        assert (Hpw : 2 ^ (x_root c) * 2 ^ (15 - x_root c) = 2 ^ 15)
          by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
        clear -Hzl Hpw Hupos. nia. }
      destruct (HFin i Hi Hgi) as [HL|HP].
      * left. exact HL.
      * right. left.
        destruct HP as (P1 & P2 & P3 & P4 & P5).
        exact (conj P1 (conj P2 (conj P3 P5))).
    + (* INCOMPLETE: the max==1 world *)
      destruct (Hincompl Hmx1 HM14) as (Hh1 & Hn0 & Hd0 & Hl1e).
      assert (Hroot1 : x_root c = 1) by lia.
      assert (Hfin : it_finish st1 = tset (s_tbl st1) 1 (mkCodeT 64 1 0)).
      { unfold it_finish. rewrite Hh1, Hn0, Hd0, Hl1e. reflexivity. }
      rewrite Hfin, Hroot1.
      unfold OwnFin in HFin.
      rewrite Hroot1 in HFin.
      intros i Hi.
      change (2 ^ 1) with 2 in Hi.
      destruct (Z.eq_dec i 1) as [->|Hne1].
      * right. right.
        rewrite tset_same.
        exact (conj eq_refl (conj eq_refl eq_refl)).
      * assert (Hi0 : i = 0) by lia. subst i.
        assert (H01 : 0 <= 0 < 2 ^ 1) by (change (2 ^ 1) with 2; lia).
        assert (Hg0 : (zrev (Z.to_nat 1) 0 + 1) * 2 ^ (15 - 1)
                      <= Pos (it_mass 15%nat 1 cnt0) st1).
        { rewrite HposM, HM14, zrev_zero.
          change (15 - 1) with 14. lia. }
        destruct (HFin 0 H01 Hg0) as [HL|HP].
        { left. destruct HL as (sym & cw & L1 & L2 & L3 & L4 & L5).
          exists sym, cw.
          rewrite (tset_other (s_tbl st1) 1 (mkCodeT 64 1 0) 0) by lia.
          exact (conj L1 (conj L2 (conj L3 (conj L4 L5)))). }
        { right. left.
          destruct HP as (P1 & P2 & P3 & P4 & P5).
          change (2 ^ 1) with 2 in P3.
          rewrite (tset_other (s_tbl st1) 1 (mkCodeT 64 1 0) 0) by lia.
          refine (conj P1 (conj P2 (conj P3 _))).
          intros j Hj.
          destruct (P5 j Hj) as (sym & cw & G1 & G2 & G3 & G4 & G5).
          exists sym, cw.
          rewrite (tset_other (s_tbl st1) 1 (mkCodeT 64 1 0)
                     (c_val (s_tbl st1 0) + j)) by lia.
          exact (conj G1 (conj G2 (conj G3 (conj G4 G5)))). }
  - (* ItOverflow: killed by o_ret *)
    injection Hmodel as <-.
    cbn [o_ret] in Hret. discriminate Hret.
Qed.

(* fast-shadow restore: importers of this file see the Zify default hook. *)
Ltac Zify.zify_pre_hook ::= idtac.
