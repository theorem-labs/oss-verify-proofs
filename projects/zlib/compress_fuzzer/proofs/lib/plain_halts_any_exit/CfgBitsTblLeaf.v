(* K-PARAMETRIC RE-CUT (BITSROW8-BUILD; TL ; q7 SHAPE ; a5-2 12670) of CfgBitsTblLeaf.v base md5 — owner an earlier development run (the dest's line 1) — under an earlier development run consent 12677/12851; cut 2026-09-05 by an earlier development run fork an earlier development run: every bound-bearing lemma cut ONCE at KB (Section, Variable KB, Hypothesis HK : 8 <= KB /\ KB <= 39), the landed names re-stated VERBATIM as the 14-instances (no carrier renamed); the 8-instances live in CfgBits8Inst.v. *)
(** * CfgBitsTblLeaf — the BITS8 TABLE THEORY as a header-light LEAF (by date -u; bits8-v1 r4).
    an earlier development run STOP #4 / an earlier development run's cure (A) (their prep CfgBitsTblLeaf.v 29291912, a build machine rc 0): the table-interface Definitions of record
    (SubPD, TblPD, FETCH_LT8_STMT, FIX_TBLPD_STMT — moved VERBATIM from CfgBits8Defs.v ) and the whole theory of CfgBitsTbl.v 
    (moved VERBATIM) under a MINIMAL Require header (Inftrees, ZBitsIn, Inflate, InflateThy, the ROOT ItGTbl* copies), so the ReachMode home
    (StepReach / StepPres: a5 665m (2) rm_tblpd, 665p rm_tblpdCL) can Require it without a cycle.  STATEMENT-IDENTICAL split: no Definition or
    Theorem text changes; CfgBitsTbl.v becomes a re-export shim and CfgBits8Defs.v Requires (Export) this leaf.
    NOTE (q4 side finding): two ItGTbl* copies exist (tree root vs Spec/PngModel); TblPD's RootPrefixDet is the ROOT copy's — never equate by name.
    Original CfgBitsTbl.v header (fork T1's provenance) follows verbatim: *)
(** * CfgBitsTbl — the TABLE side of the BITS8 discharge (an earlier development run fork T1, 2026-09-02).
    Consumes the interface leaf CfgBits8Defs (TblPD / SubPD and the *_STMT shapes) and proves:
      fetch_lt8      : FETCH_LT8_STMT                         (closed, exactly the STMT)
      fetch2_lt8_gen : the level-2 fetch bound + two premises          (0 <= c_op lst; the op = 0 fixed entry has 0 <= c_bits)
      fetch2_lt8_ptr : the level-2 fetch bound + premise 0 < c_op lst  (the pointer case, the only one the run reaches)
      decode_lt8_gen / decode_lt8_ptr : the two-level decode bound + a premise on [sub] (SubGuardGen / SubGuardPtr)
      fix_tblpd      : FIX_TBLPD_STMT                          (closed; decidable checker + vm_compute)
      it_tblpd_root  : the root half of the it_model table facts           (closed)
      it_subpd_wf    : the SUB half (SubPD) under the it_wf type/codes premise ITWF  (closed, NEW theory, sections S1-S8)
      it_tblpd_wf    : TblPD of an it_model output + the it_wf type/codes premise ITWF          (closed)
    INTERFACE NOTE: the level-2 fetch / decode / it_model facts carry the premises named above (op sign, the pointer guard,
    the it_wf type/codes bound); the development run's first drafts without them were refuted at concrete tables (kept in the fork's ride dir, not here).

    The sub half (S1-S8) mirrors ItGTblReplLoop's root argument on the sub phase of it_step: in phase 2 the
    current sub-table [next, next + 2^curr) is a root-shaped table of width curr whose position, scaled by 2^root,
    runs the same ClassDone/CovBelow clauses (classdone_fill_short / cov_step_short reused verbatim on the shifted
    VIEW); a pointer's unit completes exactly when the sub position reaches 2^15, which is repl_at_full; the
    sizing clause [ustart + 2^(15-root) - P <= pmass (curr+root) count] is what it_subsz's "left" loop establishes
    (subsz_spec) and what every later trip preserves, and it is what forces len - root <= curr (the fill really
    writes).  Completed sub-tables live below next and are never touched again (DonePtrs/PtrOk).

    Argument for the fetch loops (root and sub-table alike): the loop pulls a byte while the entry selected by the
    current low bits is wider than [bits]; a pull appends the byte ABOVE the [bits] valid bits, so the index selected
    after the pull agrees with the one before it modulo 2^bits (Z.land x (2^n-1) = x mod 2^n for EVERY x, so no
    sign premise on hold is needed); RootPrefixDet at k := bits then says the new entry cannot be <= bits wide
    without the old one being equally wide — contradicting the pull.  So after the LAST pull the entry is wider than
    bits - 8, i.e. bits < c_bits h + 8.  Invariant: [bits < 8 \/ bits - 8 < c_bits (entry at bits)]. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base ZBitsIn Inftrees InflateFast Inflate InflateThy.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import ItGTblRev ItGTblGeom ItGTblSortWin ItGTblCover ItGTblReplInv ItGTblReplLoop ItGTblRepl.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Open Scope Z_scope.

(* ===== the table-interface Definitions, from CfgBits8Defs.v (verbatim) ===== *)
(** ** The table interface (T1 proves; T3/T4 consume as Section Hypotheses of EXACTLY these types).
    TblPD t root = the canonical-table facts the fetch loops need: root-level prefix-determinism (ItGTblRepl.RootPrefixDet),
    positive root widths within root, and the SUB-TABLE half: every level-2 pointer entry (op & 0xf0 = 0, op <> 0 — the
    shape inf_decode's sub_len/sub_dist dispatch on) owns a sub-table at [c_val, c_val + 2^op) that is itself
    prefix-deterministic within its width with positive widths.  (An op = 0 "pointer" — sub_dist's degenerate case — has a
    one-entry sub-table and needs no property: the fetch2 loop's entry is then fixed.) *)
Definition SubPD (t : ztbl) (root : Z) : Prop :=
  forall i, 0 <= i < 2 ^ root -> Z.land (c_op (t i)) 240 = 0 -> c_op (t i) <> 0 ->
    RootPrefixDet (fun j => t (c_val (t i) + j)) (c_op (t i))
    /\ (forall j, 0 <= j < 2 ^ (c_op (t i)) -> 1 <= c_bits (t (c_val (t i) + j))).

Definition TblPD (t : ztbl) (root : Z) : Prop :=
  0 <= root
  /\ RootPrefixDet t root
  /\ (forall i, 0 <= i < 2 ^ root -> 1 <= c_bits (t i) <= root)
  /\ SubPD t root.

(** the root fetch leaves [c_bits h <= bits' < c_bits h + 8] from bits < 8 (so DROPBITS (c_bits h) leaves < 8) *)
Definition FETCH_LT_STMT_K (KB : Z) : Prop :=
  forall t rb b h b', TblPD t rb -> br_bits b < KB -> 0 <= br_hold b ->
    inf_fetch t rb b = FetchOk h b' -> c_bits h <= br_bits b' /\ br_bits b' < Z.max KB (c_bits h + 8).
(* BITSROW8-BUILD: the landed STMT, convertible to FETCH_LT_STMT_K 14 *)
Definition FETCH_LT8_STMT : Prop :=
  forall t rb b h b', TblPD t rb -> br_bits b < 14 -> 0 <= br_hold b ->
    inf_fetch t rb b = FetchOk h b' -> c_bits h <= br_bits b' /\ br_bits b' < Z.max 14 (c_bits h + 8).

(** TblPD at the tables the run decodes with (T1 proves; T3/T4 consume):
    - it_model outputs: root half = ItGTblReplLoop.it_prefixdet_root + ItGTblCover.it_covers_root_pos; sub half = NEW theory
      (the sub phase of it_step mirrors the root replication argument);
    - the fixed tables lenfix (root 9) / distfix (root 5): finite, decidable. *)
Definition FIX_TBLPD_STMT : Prop := TblPD lenfix 9 /\ TblPD distfix 5.


(* ===== the theory, from CfgBitsTbl.v (verbatim) ===== *)

(* ######################################################################### *)
(* 1.  Arithmetic: BITS(n) is a residue, pulls preserve residues               *)
(* ######################################################################### *)

Lemma cbt_bits_of_mod : forall n b, 0 <= n -> br_bits_of n b = br_hold b mod 2 ^ n.
Proof.
  intros n b Hn. unfold br_bits_of. rewrite Z.shiftl_1_l. apply land_ones_mod. exact Hn.
Qed.

Lemma cbt_pullbyte_fields : forall b b', br_pullbyte b = Some b' ->
  br_bits b' = br_bits b + 8
  /\ br_hold b' = br_hold b + Z.shiftl (br_in b (br_next b)) (br_bits b).
Proof.
  intros b b' H. unfold br_pullbyte in H.
  destruct (Z.eqb (br_have b) 0); [discriminate|].
  injection H as <-. cbn [br_bits br_hold]. split; reflexivity.
Qed.

(** (x mod 2^a) mod 2^k = x mod 2^(min a k) *)
Lemma cbt_mod2_mod2 : forall x a k, 0 <= a -> 0 <= k ->
  (x mod 2 ^ a) mod 2 ^ k = x mod 2 ^ (Z.min a k).
Proof.
  intros x a k Ha Hk.
  destruct (Z.le_ge_cases k a) as [Hle|Hge].
  - rewrite Z.min_r by lia. apply mod_pow2_tower. lia.
  - rewrite Z.min_l by lia. apply Z.mod_small.
    pose proof (Z.mod_pos_bound x (2 ^ a) (pow2_pos_z a Ha)).
    pose proof (Z.pow_le_mono_r 2 a k ltac:(lia) ltac:(lia)). lia.
Qed.

(** adding a multiple of 2^k does not change residues mod 2^m for m <= k *)
Lemma cbt_mod_add_pow2 : forall x y k m, 0 <= m <= k ->
  (x + y * 2 ^ k) mod 2 ^ m = x mod 2 ^ m.
Proof.
  intros x y k m Hm.
  replace (y * 2 ^ k) with ((y * 2 ^ (k - m)) * 2 ^ m).
  - apply Z_mod_plus_full.
  - rewrite <- Z.mul_assoc, <- Z.pow_add_r by lia. f_equal. f_equal. lia.
Qed.

(** dividing out the low cb bits of a pull: the byte lands k = bits - cb above the sub-index *)
Lemma cbt_div_shift : forall x y cb k, 0 <= cb -> 0 <= k ->
  (x + y * 2 ^ (cb + k)) / 2 ^ cb = x / 2 ^ cb + y * 2 ^ k.
Proof.
  intros x y cb k Hcb Hk.
  rewrite Z.pow_add_r by lia.
  replace (y * (2 ^ cb * 2 ^ k)) with ((y * 2 ^ k) * 2 ^ cb) by ring.
  pose proof (pow2_pos_z cb Hcb).
  apply Z.div_add. lia.
Qed.

(* ######################################################################### *)
(* 2.  The root fetch loop                                                    *)
(* ######################################################################### *)

(* bits14 v3 (an earlier development run F7B finding, row 7788 3(c')): the tree's ORIGINAL precise fetch-loop section, VERBATIM ( :130-:188) — FInv /
   finv_pull / fetch_go_lt8 keep their names and the PRECISE pulled-branch bound `br_bits b' < c_bits h + 8`, which W8's StepReach
   (cand11 fetch_root_le :2524) consumes.  The bits14 family's `< 14` world uses the widened twins in Section FetchLoop14 below. *)
Section FetchLoop.
  Variable t : ztbl.
  Variable rb : Z.
  Hypothesis Hpd : TblPD t rb.

  Lemma cbt_idx_range : forall b, 0 <= br_bits_of rb b < 2 ^ rb.
  Proof.
    intros b. pose proof Hpd as (Hrb & _).
    rewrite (cbt_bits_of_mod rb b Hrb). apply Z.mod_pos_bound, pow2_pos_z. exact Hrb.
  Qed.

  (** the loop invariant: either nothing was pulled yet, or the entry now selected is wider than bits - 8 *)
  Definition FInv (b : BR) : Prop :=
    br_bits b < 8 \/ br_bits b - 8 < c_bits (t (br_bits_of rb b)).

  Lemma finv_pull : forall b b',
    br_bits b < c_bits (t (br_bits_of rb b)) -> br_pullbyte b = Some b' -> FInv b'.
  Proof.
    intros b b' Hlt Hp.
    destruct (cbt_pullbyte_fields b b' Hp) as [Hbits Hhold].
    destruct (Z.lt_ge_cases (br_bits b) 0) as [Hneg|Hnn].
    - left. lia.
    - right. rewrite Hbits.
      destruct (Z.lt_ge_cases (br_bits b) (c_bits (t (br_bits_of rb b')))) as [Hok|Hbad]; [lia|exfalso].
      pose proof Hpd as (Hrb & Hpd1 & _ & _).
      pose proof (cbt_idx_range b') as Hi'.
      pose proof (cbt_idx_range b) as Hi.
      assert (Hagree : br_bits_of rb b' mod 2 ^ br_bits b = br_bits_of rb b mod 2 ^ br_bits b).
      { rewrite (cbt_bits_of_mod rb b' Hrb), (cbt_bits_of_mod rb b Hrb).
        rewrite (cbt_mod2_mod2 (br_hold b') rb (br_bits b) Hrb Hnn).
        rewrite (cbt_mod2_mod2 (br_hold b) rb (br_bits b) Hrb Hnn).
        rewrite Hhold, Z.shiftl_mul_pow2 by exact Hnn.
        apply cbt_mod_add_pow2. lia. }
      pose proof (Hpd1 _ _ (br_bits b) Hi' Hi Hnn Hbad Hagree) as Heq.
      lia.
  Qed.

  Lemma fetch_go_lt8 : forall f b h b',
    FInv b -> inf_fetch_go f t rb b = FetchOk h b' ->
    (exists i, 0 <= i < 2 ^ rb /\ t i = h)
    /\ c_bits h <= br_bits b' /\ br_bits b' < c_bits h + 8.
  Proof.
    induction f as [|f IH]; intros b h b' Hinv Hgo;
      cbn [inf_fetch_go] in Hgo; [discriminate|].
    cbv zeta in Hgo. revert Hgo.
    match goal with
    | |- (if ?c then _ else _) = _ -> _ => destruct c eqn:Hle
    end; intros Hgo.
    - apply Z.leb_le in Hle. injection Hgo as Hh Hb. subst h b'.
      pose proof Hpd as (Hrb & _ & Hw & _).
      pose proof (cbt_idx_range b) as Hi.
      pose proof (Hw _ Hi).
      split; [exists (br_bits_of rb b); split; [exact Hi | reflexivity] |].
      destruct Hinv; split; lia.
    - apply Z.leb_gt in Hle. revert Hgo.
      destruct (br_pullbyte b) as [b1|] eqn:Hp; intros Hgo; [|discriminate].
      exact (IH b1 h b' (finv_pull b b1 Hle Hp) Hgo).
  Qed.
End FetchLoop.

Section FetchLoop14.
  Variable t : ztbl.
  Variable rb : Z.
  Hypothesis Hpd : TblPD t rb.

  Lemma cbt_idx_range14 : forall b, 0 <= br_bits_of rb b < 2 ^ rb.
  Proof.
    intros b. pose proof Hpd as (Hrb & _).
    rewrite (cbt_bits_of_mod rb b Hrb). apply Z.mod_pos_bound, pow2_pos_z. exact Hrb.
  Qed.

  (** the loop invariant: either nothing was pulled yet, or the entry now selected is wider than bits - 8 *)
  Definition FInv14 (b : BR) : Prop :=
    br_bits b < 14 \/ br_bits b - 8 < c_bits (t (br_bits_of rb b)).  (* F7B: the entry bound is < 14 *)

  Lemma finv14_pull : forall b b',
    br_bits b < c_bits (t (br_bits_of rb b)) -> br_pullbyte b = Some b' -> FInv14 b'.
  Proof.
    intros b b' Hlt Hp.
    destruct (cbt_pullbyte_fields b b' Hp) as [Hbits Hhold].
    destruct (Z.lt_ge_cases (br_bits b) 0) as [Hneg|Hnn].
    - left. lia.
    - right. rewrite Hbits.
      destruct (Z.lt_ge_cases (br_bits b) (c_bits (t (br_bits_of rb b')))) as [Hok|Hbad]; [lia|exfalso].
      pose proof Hpd as (Hrb & Hpd1 & _ & _).
      pose proof (cbt_idx_range14 b') as Hi'.
      pose proof (cbt_idx_range14 b) as Hi.
      assert (Hagree : br_bits_of rb b' mod 2 ^ br_bits b = br_bits_of rb b mod 2 ^ br_bits b).
      { rewrite (cbt_bits_of_mod rb b' Hrb), (cbt_bits_of_mod rb b Hrb).
        rewrite (cbt_mod2_mod2 (br_hold b') rb (br_bits b) Hrb Hnn).
        rewrite (cbt_mod2_mod2 (br_hold b) rb (br_bits b) Hrb Hnn).
        rewrite Hhold, Z.shiftl_mul_pow2 by exact Hnn.
        apply cbt_mod_add_pow2. lia. }
      pose proof (Hpd1 _ _ (br_bits b) Hi' Hi Hnn Hbad Hagree) as Heq.
      lia.
  Qed.

  Lemma fetch_go_lt14 : forall f b h b',
    FInv14 b -> inf_fetch_go f t rb b = FetchOk h b' ->
    (exists i, 0 <= i < 2 ^ rb /\ t i = h)
    /\ c_bits h <= br_bits b' /\ br_bits b' < Z.max 14 (c_bits h + 8).
  Proof.
    induction f as [|f IH]; intros b h b' Hinv Hgo;
      cbn [inf_fetch_go] in Hgo; [discriminate|].
    cbv zeta in Hgo. revert Hgo.
    match goal with
    | |- (if ?c then _ else _) = _ -> _ => destruct c eqn:Hle
    end; intros Hgo.
    - apply Z.leb_le in Hle. injection Hgo as Hh Hb. subst h b'.
      pose proof Hpd as (Hrb & _ & Hw & _).
      pose proof (cbt_idx_range14 b) as Hi.
      pose proof (Hw _ Hi).
      split; [exists (br_bits_of rb b); split; [exact Hi | reflexivity] |].
      destruct Hinv; split; lia.
    - apply Z.leb_gt in Hle. revert Hgo.
      destruct (br_pullbyte b) as [b1|] eqn:Hp; intros Hgo; [|discriminate].
      exact (IH b1 h b' (finv14_pull b b1 Hle Hp) Hgo).
  Qed.
End FetchLoop14.

(* BITSROW8-BUILD: the K twin of Section FetchLoop14 (q7 ) *)
Section FetchLoopK.
  Variable KB : Z.
  Hypothesis HK : 8 <= KB /\ KB <= 39.
  Variable t : ztbl.
  Variable rb : Z.
  Hypothesis Hpd : TblPD t rb.

  Lemma cbt_idx_range_K : forall b, 0 <= br_bits_of rb b < 2 ^ rb.
  Proof. pose proof HK as HKu.
    intros b. pose proof Hpd as (Hrb & _).
    rewrite (cbt_bits_of_mod rb b Hrb). apply Z.mod_pos_bound, pow2_pos_z. exact Hrb.
  Qed.

  (** the loop invariant: either nothing was pulled yet, or the entry now selected is wider than bits - 8 *)
  Definition FInv_K (b : BR) : Prop :=
    br_bits b < KB \/ br_bits b - 8 < c_bits (t (br_bits_of rb b)).  (* F7B: the entry bound is < KB *)

  Lemma finv14_pull_K : forall b b',
    br_bits b < c_bits (t (br_bits_of rb b)) -> br_pullbyte b = Some b' -> FInv_K b'.
  Proof. pose proof HK as HKu.
    intros b b' Hlt Hp.
    destruct (cbt_pullbyte_fields b b' Hp) as [Hbits Hhold].
    destruct (Z.lt_ge_cases (br_bits b) 0) as [Hneg|Hnn].
    - left. lia.
    - right. rewrite Hbits.
      destruct (Z.lt_ge_cases (br_bits b) (c_bits (t (br_bits_of rb b')))) as [Hok|Hbad]; [lia|exfalso].
      pose proof Hpd as (Hrb & Hpd1 & _ & _).
      pose proof (cbt_idx_range_K b') as Hi'.
      pose proof (cbt_idx_range_K b) as Hi.
      assert (Hagree : br_bits_of rb b' mod 2 ^ br_bits b = br_bits_of rb b mod 2 ^ br_bits b).
      { rewrite (cbt_bits_of_mod rb b' Hrb), (cbt_bits_of_mod rb b Hrb).
        rewrite (cbt_mod2_mod2 (br_hold b') rb (br_bits b) Hrb Hnn).
        rewrite (cbt_mod2_mod2 (br_hold b) rb (br_bits b) Hrb Hnn).
        rewrite Hhold, Z.shiftl_mul_pow2 by exact Hnn.
        apply cbt_mod_add_pow2. lia. }
      pose proof (Hpd1 _ _ (br_bits b) Hi' Hi Hnn Hbad Hagree) as Heq.
      lia.
  Qed.

  Lemma fetch_go_lt_K : forall f b h b',
    FInv_K b -> inf_fetch_go f t rb b = FetchOk h b' ->
    (exists i, 0 <= i < 2 ^ rb /\ t i = h)
    /\ c_bits h <= br_bits b' /\ br_bits b' < Z.max KB (c_bits h + 8).
  Proof. pose proof HK as HKu.
    induction f as [|f IH]; intros b h b' Hinv Hgo;
      cbn [inf_fetch_go] in Hgo; [discriminate|].
    cbv zeta in Hgo. revert Hgo.
    match goal with
    | |- (if ?c then _ else _) = _ -> _ => destruct c eqn:Hle
    end; intros Hgo.
    - apply Z.leb_le in Hle. injection Hgo as Hh Hb. subst h b'.
      pose proof Hpd as (Hrb & _ & Hw & _).
      pose proof (cbt_idx_range_K b) as Hi.
      pose proof (Hw _ Hi).
      split; [exists (br_bits_of rb b); split; [exact Hi | reflexivity] |].
      destruct Hinv; split; lia.
    - apply Z.leb_gt in Hle. revert Hgo.
      destruct (br_pullbyte b) as [b1|] eqn:Hp; intros Hgo; [|discriminate].
      exact (IH b1 h b' (finv14_pull_K b b1 Hle Hp) Hgo).
  Qed.
End FetchLoopK.

Section K_CfgBitsTblLeaf_fetch.
  Variable KB : Z.
  Hypothesis HK : 8 <= KB /\ KB <= 39.
Theorem fetch_lt_K : FETCH_LT_STMT_K KB.
Proof. pose proof HK as HKu.
  unfold FETCH_LT_STMT_K. intros t rb b h b' Hpd Hb _ Hf.
  unfold inf_fetch in Hf.
  exact (proj2 ((fetch_go_lt_K KB HK) t rb Hpd _ b h b' (or_introl Hb) Hf)).
Qed.

(** the entry a root fetch returns IS a root entry *)
Lemma fetch_root_entry_K : forall t rb b h b', TblPD t rb -> br_bits b < KB ->
  inf_fetch t rb b = FetchOk h b' -> exists i, 0 <= i < 2 ^ rb /\ t i = h.
Proof. pose proof HK as HKu.
  intros t rb b h b' Hpd Hb Hf. unfold inf_fetch in Hf.
  exact (proj1 ((fetch_go_lt_K KB HK) t rb Hpd _ b h b' (or_introl Hb) Hf)).
Qed.

End K_CfgBitsTblLeaf_fetch.

(** the landed names as the 14-instances *)
Theorem fetch_lt8 : FETCH_LT8_STMT.
Proof. exact (fetch_lt_K 14 ltac:(lia)). Qed.

Lemma fetch_root_entry : forall t rb b h b', TblPD t rb -> br_bits b < 14 ->
  inf_fetch t rb b = FetchOk h b' -> exists i, 0 <= i < 2 ^ rb /\ t i = h.
Proof. exact (fetch_root_entry_K 14 ltac:(lia)). Qed.

(* ######################################################################### *)
(* 3.  The level-2 fetch loop                                                 *)
(* ######################################################################### *)

(* bits14 v3: the tree's ORIGINAL precise second-level fetch-loop section, VERBATIM ( :209-:332) — F2Inv / f2inv_pull /
   fetch2_go_lt8 at the precise bound `br_bits b' < c_bits lst + c_bits h + 8` (cand11 fetch2_root_le :2541). Widened twins: Fetch2Loop14. *)
Section Fetch2Loop.
  Variable t : ztbl.
  Variable rb : Z.
  Variable lst : Code.
  Hypothesis Hpd : TblPD t rb.
  Hypothesis Hroot : exists i, 0 <= i < 2 ^ rb /\ t i = lst.
  Hypothesis Hop240 : Z.land (c_op lst) 240 = 0.
  Hypothesis Hopnn : 0 <= c_op lst.
  (** the degenerate op = 0 "pointer" (sub_dist's shape): its one fixed entry must not be negative-width *)
  Hypothesis Hop0 : c_op lst = 0 -> 0 <= c_bits (t (c_val lst)).

  Lemma cbt_cb_range : 1 <= c_bits lst <= rb.
  Proof.
    pose proof Hpd as (_ & _ & Hw & _). destruct Hroot as (i & Hi & Hti).
    rewrite <- Hti. exact (Hw i Hi).
  Qed.

  (** the sub index [BITS(cb + op) >> cb] is [(hold / 2^cb) mod 2^op] *)
  Lemma cbt_sidx_eq : forall b,
    Z.shiftr (br_bits_of (c_bits lst + c_op lst) b) (c_bits lst)
    = (br_hold b / 2 ^ c_bits lst) mod 2 ^ c_op lst.
  Proof.
    intros b. pose proof cbt_cb_range as Hcb.
    rewrite cbt_bits_of_mod by lia.
    rewrite Z.shiftr_div_pow2 by lia.
    rewrite Z.pow_add_r by lia.
    assert (Hp1 : 0 < 2 ^ c_bits lst) by (apply pow2_pos_z; lia).
    assert (Hp2 : 0 < 2 ^ c_op lst) by (apply pow2_pos_z; lia).
    rewrite Z.rem_mul_r by lia.
    rewrite (Z.mul_comm (2 ^ c_bits lst) (br_hold b / 2 ^ c_bits lst mod 2 ^ c_op lst)).
    rewrite Z.div_add by lia.
    rewrite (Z.div_small (br_hold b mod 2 ^ c_bits lst) (2 ^ c_bits lst)
               (Z.mod_pos_bound _ _ Hp1)).
    lia.
  Qed.

  Lemma cbt_sidx_range : forall b,
    0 <= Z.shiftr (br_bits_of (c_bits lst + c_op lst) b) (c_bits lst) < 2 ^ c_op lst.
  Proof. intros b. rewrite cbt_sidx_eq. apply Z.mod_pos_bound, pow2_pos_z. exact Hopnn. Qed.

  (** the SubPD half of TblPD, at this pointer *)
  Lemma cbt_subpd_view : c_op lst <> 0 ->
    RootPrefixDet (fun j => t (c_val lst + j)) (c_op lst)
    /\ (forall j, 0 <= j < 2 ^ c_op lst -> 1 <= c_bits (t (c_val lst + j))).
  Proof.
    intros Hnz. pose proof Hpd as (_ & _ & _ & Hs).
    destruct Hroot as (i & Hi & Hti).
    specialize (Hs i Hi). rewrite Hti in Hs. exact (Hs Hop240 Hnz).
  Qed.

  Lemma cbt_entry_nonneg : forall b,
    0 <= c_bits (t (c_val lst + Z.shiftr (br_bits_of (c_bits lst + c_op lst) b) (c_bits lst))).
  Proof.
    intros b.
    destruct (Z.eq_dec (c_op lst) 0) as [Hz|Hnz].
    - rewrite cbt_sidx_eq, Hz, Z.pow_0_r, Z.mod_1_r, Z.add_0_r. exact (Hop0 Hz).
    - destruct (cbt_subpd_view Hnz) as [_ Hpos].
      pose proof (Hpos _ (cbt_sidx_range b)). lia.
  Qed.

  Definition F2Inv (b : BR) : Prop :=
    c_bits lst <= br_bits b
    /\ (br_bits b < c_bits lst + 8
        \/ br_bits b - 8
           < c_bits lst
             + c_bits (t (c_val lst + Z.shiftr (br_bits_of (c_bits lst + c_op lst) b) (c_bits lst)))).

  Lemma f2inv_pull : forall b b',
    F2Inv b ->
    br_bits b < c_bits lst
                + c_bits (t (c_val lst + Z.shiftr (br_bits_of (c_bits lst + c_op lst) b) (c_bits lst))) ->
    br_pullbyte b = Some b' -> F2Inv b'.
  Proof.
    intros b b' [Hcb _] Hlt Hp.
    pose proof cbt_cb_range as Hcbr.
    destruct (cbt_pullbyte_fields b b' Hp) as [Hbits Hhold].
    split; [lia|]. right. rewrite Hbits.
    destruct (Z.lt_ge_cases (br_bits b)
                (c_bits lst
                 + c_bits (t (c_val lst + Z.shiftr (br_bits_of (c_bits lst + c_op lst) b') (c_bits lst)))))
      as [Hok|Hbad]; [lia|exfalso].
    destruct (Z.eq_dec (c_op lst) 0) as [Hz|Hnz].
    - (* op = 0: the sub index is 0 before and after, the entry is fixed *)
      rewrite cbt_sidx_eq, Hz, Z.pow_0_r, Z.mod_1_r in Hlt.
      rewrite cbt_sidx_eq, Hz, Z.pow_0_r, Z.mod_1_r in Hbad.
      lia.
    - destruct (cbt_subpd_view Hnz) as [HR _].
      remember (br_bits b - c_bits lst) as k eqn:Hk.
      assert (Hk0 : 0 <= k) by lia.
      pose proof (cbt_sidx_range b) as Hi.
      pose proof (cbt_sidx_range b') as Hi'.
      assert (Hagree : Z.shiftr (br_bits_of (c_bits lst + c_op lst) b') (c_bits lst) mod 2 ^ k
                       = Z.shiftr (br_bits_of (c_bits lst + c_op lst) b) (c_bits lst) mod 2 ^ k).
      { rewrite (cbt_sidx_eq b'), (cbt_sidx_eq b).
        rewrite (cbt_mod2_mod2 (br_hold b' / 2 ^ c_bits lst) (c_op lst) k Hopnn Hk0).
        rewrite (cbt_mod2_mod2 (br_hold b / 2 ^ c_bits lst) (c_op lst) k Hopnn Hk0).
        rewrite Hhold, Z.shiftl_mul_pow2 by lia.
        replace (br_bits b) with (c_bits lst + k) by lia.
        rewrite cbt_div_shift by lia.
        apply cbt_mod_add_pow2. lia. }
      assert (Hbad' : c_bits (t (c_val lst + Z.shiftr (br_bits_of (c_bits lst + c_op lst) b') (c_bits lst)))
                      <= k) by lia.
      pose proof (HR _ _ k Hi' Hi Hk0 Hbad' Hagree) as Heq.
      cbv beta in Heq. lia.
  Qed.

  Lemma fetch2_go_lt8 : forall f b h b',
    F2Inv b -> inf_fetch2_go f t lst b = FetchOk h b' ->
    c_bits lst + c_bits h <= br_bits b' /\ br_bits b' < c_bits lst + c_bits h + 8.
  Proof.
    induction f as [|f IH]; intros b h b' Hinv Hgo;
      cbn [inf_fetch2_go] in Hgo; [discriminate|].
    cbv zeta in Hgo. revert Hgo.
    match goal with
    | |- (if ?c then _ else _) = _ -> _ => destruct c eqn:Hle
    end; intros Hgo.
    - apply Z.leb_le in Hle. injection Hgo as Hh Hb. subst h b'.
      pose proof (cbt_entry_nonneg b).
      destruct Hinv as [Hcb [H1|H1]]; split; lia.
    - apply Z.leb_gt in Hle. revert Hgo.
      destruct (br_pullbyte b) as [b1|] eqn:Hp; intros Hgo; [|discriminate].
      exact (IH b1 h b' (f2inv_pull b b1 Hinv Hle Hp) Hgo).
  Qed.
End Fetch2Loop.

Section Fetch2Loop14.
  Variable t : ztbl.
  Variable rb : Z.
  Variable lst : Code.
  Hypothesis Hpd : TblPD t rb.
  Hypothesis Hroot : exists i, 0 <= i < 2 ^ rb /\ t i = lst.
  Hypothesis Hop240 : Z.land (c_op lst) 240 = 0.
  Hypothesis Hopnn : 0 <= c_op lst.
  (** the degenerate op = 0 "pointer" (sub_dist's shape): its one fixed entry must not be negative-width *)
  Hypothesis Hop0 : c_op lst = 0 -> 0 <= c_bits (t (c_val lst)).

  Lemma cbt_cb_range14 : 1 <= c_bits lst <= rb.
  Proof.
    pose proof Hpd as (_ & _ & Hw & _). destruct Hroot as (i & Hi & Hti).
    rewrite <- Hti. exact (Hw i Hi).
  Qed.

  (** the sub index [BITS(cb + op) >> cb] is [(hold / 2^cb) mod 2^op] *)
  Lemma cbt_sidx_eq14 : forall b,
    Z.shiftr (br_bits_of (c_bits lst + c_op lst) b) (c_bits lst)
    = (br_hold b / 2 ^ c_bits lst) mod 2 ^ c_op lst.
  Proof.
    intros b. pose proof cbt_cb_range14 as Hcb.
    rewrite cbt_bits_of_mod by lia.
    rewrite Z.shiftr_div_pow2 by lia.
    rewrite Z.pow_add_r by lia.
    assert (Hp1 : 0 < 2 ^ c_bits lst) by (apply pow2_pos_z; lia).
    assert (Hp2 : 0 < 2 ^ c_op lst) by (apply pow2_pos_z; lia).
    rewrite Z.rem_mul_r by lia.
    rewrite (Z.mul_comm (2 ^ c_bits lst) (br_hold b / 2 ^ c_bits lst mod 2 ^ c_op lst)).
    rewrite Z.div_add by lia.
    rewrite (Z.div_small (br_hold b mod 2 ^ c_bits lst) (2 ^ c_bits lst)
               (Z.mod_pos_bound _ _ Hp1)).
    lia.
  Qed.

  Lemma cbt_sidx_range14 : forall b,
    0 <= Z.shiftr (br_bits_of (c_bits lst + c_op lst) b) (c_bits lst) < 2 ^ c_op lst.
  Proof. intros b. rewrite cbt_sidx_eq14. apply Z.mod_pos_bound, pow2_pos_z. exact Hopnn. Qed.

  (** the SubPD half of TblPD, at this pointer *)
  Lemma cbt_subpd_view14 : c_op lst <> 0 ->
    RootPrefixDet (fun j => t (c_val lst + j)) (c_op lst)
    /\ (forall j, 0 <= j < 2 ^ c_op lst -> 1 <= c_bits (t (c_val lst + j))).
  Proof.
    intros Hnz. pose proof Hpd as (_ & _ & _ & Hs).
    destruct Hroot as (i & Hi & Hti).
    specialize (Hs i Hi). rewrite Hti in Hs. exact (Hs Hop240 Hnz).
  Qed.

  Lemma cbt_entry_nonneg14 : forall b,
    0 <= c_bits (t (c_val lst + Z.shiftr (br_bits_of (c_bits lst + c_op lst) b) (c_bits lst))).
  Proof.
    intros b.
    destruct (Z.eq_dec (c_op lst) 0) as [Hz|Hnz].
    - rewrite cbt_sidx_eq14, Hz, Z.pow_0_r, Z.mod_1_r, Z.add_0_r. exact (Hop0 Hz).
    - destruct (cbt_subpd_view14 Hnz) as [_ Hpos].
      pose proof (Hpos _ (cbt_sidx_range14 b)). lia.
  Qed.

  Definition F2Inv14 (b : BR) : Prop :=
    c_bits lst <= br_bits b
    /\ (br_bits b < Z.max 14 (c_bits lst + 8)
        \/ br_bits b - 8
           < c_bits lst
             + c_bits (t (c_val lst + Z.shiftr (br_bits_of (c_bits lst + c_op lst) b) (c_bits lst)))).

  Lemma f2inv14_pull : forall b b',
    F2Inv14 b ->
    br_bits b < c_bits lst
                + c_bits (t (c_val lst + Z.shiftr (br_bits_of (c_bits lst + c_op lst) b) (c_bits lst))) ->
    br_pullbyte b = Some b' -> F2Inv14 b'.
  Proof.
    intros b b' [Hcb _] Hlt Hp.
    pose proof cbt_cb_range14 as Hcbr.
    destruct (cbt_pullbyte_fields b b' Hp) as [Hbits Hhold].
    split; [lia|]. right. rewrite Hbits.
    destruct (Z.lt_ge_cases (br_bits b)
                (c_bits lst
                 + c_bits (t (c_val lst + Z.shiftr (br_bits_of (c_bits lst + c_op lst) b') (c_bits lst)))))
      as [Hok|Hbad]; [lia|exfalso].
    destruct (Z.eq_dec (c_op lst) 0) as [Hz|Hnz].
    - (* op = 0: the sub index is 0 before and after, the entry is fixed *)
      rewrite cbt_sidx_eq14, Hz, Z.pow_0_r, Z.mod_1_r in Hlt.
      rewrite cbt_sidx_eq14, Hz, Z.pow_0_r, Z.mod_1_r in Hbad.
      lia.
    - destruct (cbt_subpd_view14 Hnz) as [HR _].
      remember (br_bits b - c_bits lst) as k eqn:Hk.
      assert (Hk0 : 0 <= k) by lia.
      pose proof (cbt_sidx_range14 b) as Hi.
      pose proof (cbt_sidx_range14 b') as Hi'.
      assert (Hagree : Z.shiftr (br_bits_of (c_bits lst + c_op lst) b') (c_bits lst) mod 2 ^ k
                       = Z.shiftr (br_bits_of (c_bits lst + c_op lst) b) (c_bits lst) mod 2 ^ k).
      { rewrite (cbt_sidx_eq14 b'), (cbt_sidx_eq14 b).
        rewrite (cbt_mod2_mod2 (br_hold b' / 2 ^ c_bits lst) (c_op lst) k Hopnn Hk0).
        rewrite (cbt_mod2_mod2 (br_hold b / 2 ^ c_bits lst) (c_op lst) k Hopnn Hk0).
        rewrite Hhold, Z.shiftl_mul_pow2 by lia.
        replace (br_bits b) with (c_bits lst + k) by lia.
        rewrite cbt_div_shift by lia.
        apply cbt_mod_add_pow2. lia. }
      assert (Hbad' : c_bits (t (c_val lst + Z.shiftr (br_bits_of (c_bits lst + c_op lst) b') (c_bits lst)))
                      <= k) by lia.
      pose proof (HR _ _ k Hi' Hi Hk0 Hbad' Hagree) as Heq.
      cbv beta in Heq. lia.
  Qed.

  Lemma fetch2_go_lt14 : forall f b h b',
    F2Inv14 b -> inf_fetch2_go f t lst b = FetchOk h b' ->
    c_bits lst + c_bits h <= br_bits b' /\ br_bits b' < Z.max 14 (c_bits lst + c_bits h + 8) /\ 0 <= c_bits h.
  Proof.
    induction f as [|f IH]; intros b h b' Hinv Hgo;
      cbn [inf_fetch2_go] in Hgo; [discriminate|].
    cbv zeta in Hgo. revert Hgo.
    match goal with
    | |- (if ?c then _ else _) = _ -> _ => destruct c eqn:Hle
    end; intros Hgo.
    - apply Z.leb_le in Hle. injection Hgo as Hh Hb. subst h b'.
      pose proof (cbt_entry_nonneg14 b).
      destruct Hinv as [Hcb [H1|H1]]; (split; [lia | split; lia]).
    - apply Z.leb_gt in Hle. revert Hgo.
      destruct (br_pullbyte b) as [b1|] eqn:Hp; intros Hgo; [|discriminate].
      exact (IH b1 h b' (f2inv14_pull b b1 Hinv Hle Hp) Hgo).
  Qed.
End Fetch2Loop14.

(* BITSROW8-BUILD: the K twin of Section Fetch2Loop14 *)
Section Fetch2LoopK.
  Variable KB : Z.
  Hypothesis HK : 8 <= KB /\ KB <= 39.
  Variable t : ztbl.
  Variable rb : Z.
  Variable lst : Code.
  Hypothesis Hpd : TblPD t rb.
  Hypothesis Hroot : exists i, 0 <= i < 2 ^ rb /\ t i = lst.
  Hypothesis Hop240 : Z.land (c_op lst) 240 = 0.
  Hypothesis Hopnn : 0 <= c_op lst.
  (** the degenerate op = 0 "pointer" (sub_dist's shape): its one fixed entry must not be negative-width *)
  Hypothesis Hop0 : c_op lst = 0 -> 0 <= c_bits (t (c_val lst)).

  Lemma cbt_cb_range_K : 1 <= c_bits lst <= rb.
  Proof. pose proof HK as HKu.
    pose proof Hpd as (_ & _ & Hw & _). destruct Hroot as (i & Hi & Hti).
    rewrite <- Hti. exact (Hw i Hi).
  Qed.

  (** the sub index [BITS(cb + op) >> cb] is [(hold / 2^cb) mod 2^op] *)
  Lemma cbt_sidx_eq_K : forall b,
    Z.shiftr (br_bits_of (c_bits lst + c_op lst) b) (c_bits lst)
    = (br_hold b / 2 ^ c_bits lst) mod 2 ^ c_op lst.
  Proof. pose proof HK as HKu.
    intros b. pose proof cbt_cb_range_K as Hcb.
    rewrite cbt_bits_of_mod by lia.
    rewrite Z.shiftr_div_pow2 by lia.
    rewrite Z.pow_add_r by lia.
    assert (Hp1 : 0 < 2 ^ c_bits lst) by (apply pow2_pos_z; lia).
    assert (Hp2 : 0 < 2 ^ c_op lst) by (apply pow2_pos_z; lia).
    rewrite Z.rem_mul_r by lia.
    rewrite (Z.mul_comm (2 ^ c_bits lst) (br_hold b / 2 ^ c_bits lst mod 2 ^ c_op lst)).
    rewrite Z.div_add by lia.
    rewrite (Z.div_small (br_hold b mod 2 ^ c_bits lst) (2 ^ c_bits lst)
               (Z.mod_pos_bound _ _ Hp1)).
    lia.
  Qed.

  Lemma cbt_sidx_range_K : forall b,
    0 <= Z.shiftr (br_bits_of (c_bits lst + c_op lst) b) (c_bits lst) < 2 ^ c_op lst.
  Proof. pose proof HK as HKu. intros b. rewrite cbt_sidx_eq_K. apply Z.mod_pos_bound, pow2_pos_z. exact Hopnn. Qed.

  (** the SubPD half of TblPD, at this pointer *)
  Lemma cbt_subpd_view_K : c_op lst <> 0 ->
    RootPrefixDet (fun j => t (c_val lst + j)) (c_op lst)
    /\ (forall j, 0 <= j < 2 ^ c_op lst -> 1 <= c_bits (t (c_val lst + j))).
  Proof. pose proof HK as HKu.
    intros Hnz. pose proof Hpd as (_ & _ & _ & Hs).
    destruct Hroot as (i & Hi & Hti).
    specialize (Hs i Hi). rewrite Hti in Hs. exact (Hs Hop240 Hnz).
  Qed.

  Lemma cbt_entry_nonneg_K : forall b,
    0 <= c_bits (t (c_val lst + Z.shiftr (br_bits_of (c_bits lst + c_op lst) b) (c_bits lst))).
  Proof. pose proof HK as HKu.
    intros b.
    destruct (Z.eq_dec (c_op lst) 0) as [Hz|Hnz].
    - rewrite cbt_sidx_eq_K, Hz, Z.pow_0_r, Z.mod_1_r, Z.add_0_r. exact (Hop0 Hz).
    - destruct (cbt_subpd_view_K Hnz) as [_ Hpos].
      pose proof (Hpos _ (cbt_sidx_range_K b)). lia.
  Qed.

  Definition F2Inv_K (b : BR) : Prop :=
    c_bits lst <= br_bits b
    /\ (br_bits b < Z.max KB (c_bits lst + 8)
        \/ br_bits b - 8
           < c_bits lst
             + c_bits (t (c_val lst + Z.shiftr (br_bits_of (c_bits lst + c_op lst) b) (c_bits lst)))).

  Lemma f2inv14_pull_K : forall b b',
    F2Inv_K b ->
    br_bits b < c_bits lst
                + c_bits (t (c_val lst + Z.shiftr (br_bits_of (c_bits lst + c_op lst) b) (c_bits lst))) ->
    br_pullbyte b = Some b' -> F2Inv_K b'.
  Proof. pose proof HK as HKu.
    intros b b' [Hcb _] Hlt Hp.
    pose proof cbt_cb_range_K as Hcbr.
    destruct (cbt_pullbyte_fields b b' Hp) as [Hbits Hhold].
    split; [lia|]. right. rewrite Hbits.
    destruct (Z.lt_ge_cases (br_bits b)
                (c_bits lst
                 + c_bits (t (c_val lst + Z.shiftr (br_bits_of (c_bits lst + c_op lst) b') (c_bits lst)))))
      as [Hok|Hbad]; [lia|exfalso].
    destruct (Z.eq_dec (c_op lst) 0) as [Hz|Hnz].
    - (* op = 0: the sub index is 0 before and after, the entry is fixed *)
      rewrite cbt_sidx_eq_K, Hz, Z.pow_0_r, Z.mod_1_r in Hlt.
      rewrite cbt_sidx_eq_K, Hz, Z.pow_0_r, Z.mod_1_r in Hbad.
      lia.
    - destruct (cbt_subpd_view_K Hnz) as [HR _].
      remember (br_bits b - c_bits lst) as k eqn:Hk.
      assert (Hk0 : 0 <= k) by lia.
      pose proof (cbt_sidx_range_K b) as Hi.
      pose proof (cbt_sidx_range_K b') as Hi'.
      assert (Hagree : Z.shiftr (br_bits_of (c_bits lst + c_op lst) b') (c_bits lst) mod 2 ^ k
                       = Z.shiftr (br_bits_of (c_bits lst + c_op lst) b) (c_bits lst) mod 2 ^ k).
      { rewrite (cbt_sidx_eq_K b'), (cbt_sidx_eq_K b).
        rewrite (cbt_mod2_mod2 (br_hold b' / 2 ^ c_bits lst) (c_op lst) k Hopnn Hk0).
        rewrite (cbt_mod2_mod2 (br_hold b / 2 ^ c_bits lst) (c_op lst) k Hopnn Hk0).
        rewrite Hhold, Z.shiftl_mul_pow2 by lia.
        replace (br_bits b) with (c_bits lst + k) by lia.
        rewrite cbt_div_shift by lia.
        apply cbt_mod_add_pow2. lia. }
      assert (Hbad' : c_bits (t (c_val lst + Z.shiftr (br_bits_of (c_bits lst + c_op lst) b') (c_bits lst)))
                      <= k) by lia.
      pose proof (HR _ _ k Hi' Hi Hk0 Hbad' Hagree) as Heq.
      cbv beta in Heq. lia.
  Qed.

  Lemma fetch2_go_lt_K : forall f b h b',
    F2Inv_K b -> inf_fetch2_go f t lst b = FetchOk h b' ->
    c_bits lst + c_bits h <= br_bits b' /\ br_bits b' < Z.max KB (c_bits lst + c_bits h + 8) /\ 0 <= c_bits h.
  Proof. pose proof HK as HKu.
    induction f as [|f IH]; intros b h b' Hinv Hgo;
      cbn [inf_fetch2_go] in Hgo; [discriminate|].
    cbv zeta in Hgo. revert Hgo.
    match goal with
    | |- (if ?c then _ else _) = _ -> _ => destruct c eqn:Hle
    end; intros Hgo.
    - apply Z.leb_le in Hle. injection Hgo as Hh Hb. subst h b'.
      pose proof (cbt_entry_nonneg_K b).
      destruct Hinv as [Hcb [H1|H1]]; (split; [lia | split; lia]).
    - apply Z.leb_gt in Hle. revert Hgo.
      destruct (br_pullbyte b) as [b1|] eqn:Hp; intros Hgo; [|discriminate].
      exact (IH b1 h b' (f2inv14_pull_K b b1 Hinv Hle Hp) Hgo).
  Qed.
End Fetch2LoopK.

Section K_CfgBitsTblLeaf_fetch2.
  Variable KB : Z.
  Hypothesis HK : 8 <= KB /\ KB <= 39.
(** the level-2 fetch bound with the two premises it needs: [0 <= c_op lst] and, for the degenerate
    op = 0 pointer, a non-negative width at its one fixed entry. *)
Theorem fetch2_lt_K_gen : forall t rb lst b h b', TblPD t rb ->
    (exists i, 0 <= i < 2 ^ rb /\ t i = lst) -> Z.land (c_op lst) 240 = 0 ->
    0 <= c_op lst -> (c_op lst = 0 -> 0 <= c_bits (t (c_val lst))) ->
    c_bits lst <= br_bits b -> br_bits b < Z.max KB (c_bits lst + 8) ->
    inf_fetch2 t lst b = FetchOk h b' ->
    c_bits lst + c_bits h <= br_bits b' /\ br_bits b' < Z.max KB (c_bits lst + c_bits h + 8) /\ 0 <= c_bits h.
Proof. pose proof HK as HKu.
  intros t rb lst b h b' Hpd Hroot H240 Hnn H0 Hlo Hhi Hf.
  unfold inf_fetch2 in Hf.
  exact ((fetch2_go_lt_K KB HK) t rb lst Hpd Hroot H240 Hnn H0 _ b h b' (conj Hlo (or_introl Hhi)) Hf).
Qed.

(** the level-2 fetch bound at a genuine pointer ([0 < c_op lst]) — the shape sub_len reaches, and the only shape a
    DIST root entry of an inflate_table output / distfix has under sub_dist (their root ops are never 0). *)
Theorem fetch2_lt_K_ptr : forall t rb lst b h b', TblPD t rb ->
    (exists i, 0 <= i < 2 ^ rb /\ t i = lst) -> Z.land (c_op lst) 240 = 0 -> 0 < c_op lst ->
    c_bits lst <= br_bits b -> br_bits b < Z.max KB (c_bits lst + 8) -> 0 <= br_hold b ->
    inf_fetch2 t lst b = FetchOk h b' ->
    c_bits lst + c_bits h <= br_bits b' /\ br_bits b' < Z.max KB (c_bits lst + c_bits h + 8) /\ 0 <= c_bits h.
Proof. pose proof HK as HKu.
  intros t rb lst b h b' Hpd Hroot H240 Hpos Hlo Hhi _ Hf.
  apply (fetch2_lt_K_gen t rb lst b h b' Hpd Hroot H240); [lia | intros Hz; lia | exact Hlo | exact Hhi | exact Hf].
Qed.

End K_CfgBitsTblLeaf_fetch2.

(** the landed names as the 14-instances *)
Theorem fetch2_lt8_gen : forall t rb lst b h b', TblPD t rb ->
    (exists i, 0 <= i < 2 ^ rb /\ t i = lst) -> Z.land (c_op lst) 240 = 0 ->
    0 <= c_op lst -> (c_op lst = 0 -> 0 <= c_bits (t (c_val lst))) ->
    c_bits lst <= br_bits b -> br_bits b < Z.max 14 (c_bits lst + 8) ->
    inf_fetch2 t lst b = FetchOk h b' ->
    c_bits lst + c_bits h <= br_bits b' /\ br_bits b' < Z.max 14 (c_bits lst + c_bits h + 8) /\ 0 <= c_bits h.
Proof. exact (fetch2_lt_K_gen 14 ltac:(lia)). Qed.

Theorem fetch2_lt8_ptr : forall t rb lst b h b', TblPD t rb ->
    (exists i, 0 <= i < 2 ^ rb /\ t i = lst) -> Z.land (c_op lst) 240 = 0 -> 0 < c_op lst ->
    c_bits lst <= br_bits b -> br_bits b < Z.max 14 (c_bits lst + 8) -> 0 <= br_hold b ->
    inf_fetch2 t lst b = FetchOk h b' ->
    c_bits lst + c_bits h <= br_bits b' /\ br_bits b' < Z.max 14 (c_bits lst + c_bits h + 8) /\ 0 <= c_bits h.
Proof. exact (fetch2_lt_K_ptr 14 ltac:(lia)). Qed.

(* ######################################################################### *)
(* 4.  The two-level decode                                                   *)
(* ######################################################################### *)

(** what the sub-table guard must certify about the root entries it accepts (see FINDINGS) *)
Definition SubGuardGen (sub : Code -> bool) (t : ztbl) (rb : Z) : Prop :=
  forall i, 0 <= i < 2 ^ rb -> sub (t i) = true ->
    Z.land (c_op (t i)) 240 = 0 /\ 0 <= c_op (t i)
    /\ (c_op (t i) = 0 -> 0 <= c_bits (t (c_val (t i)))).

Definition SubGuardPtr (sub : Code -> bool) (t : ztbl) (rb : Z) : Prop :=
  forall i, 0 <= i < 2 ^ rb -> sub (t i) = true -> Z.land (c_op (t i)) 240 = 0 /\ 0 < c_op (t i).

Lemma subguard_ptr_gen : forall sub t rb, SubGuardPtr sub t rb -> SubGuardGen sub t rb.
Proof.
  intros sub t rb H i Hi Hs. destruct (H i Hi Hs) as [H240 Hpos].
  split; [exact H240 | split; [lia | intros Hz; lia]].
Qed.

Lemma subguard_len_of_opnn : forall t rb,
  (forall i, 0 <= i < 2 ^ rb -> 0 <= c_op (t i)) -> SubGuardPtr sub_len t rb.
Proof.
  intros t rb Hnn i Hi Hs. unfold sub_len in Hs.
  apply andb_prop in Hs as [Hnz H240].
  apply negb_true_iff in Hnz. apply Z.eqb_neq in Hnz. apply Z.eqb_eq in H240.
  pose proof (Hnn i Hi). split; [exact H240 | lia].
Qed.

Lemma subguard_dist_of_oppos : forall t rb,
  (forall i, 0 <= i < 2 ^ rb -> 0 < c_op (t i)) -> SubGuardPtr sub_dist t rb.
Proof.
  intros t rb Hpos i Hi Hs. unfold sub_dist in Hs. apply Z.eqb_eq in Hs.
  split; [exact Hs | apply Hpos; exact Hi].
Qed.

Section K_CfgBitsTblLeaf_decode.
  Variable KB : Z.
  Hypothesis HK : 8 <= KB /\ KB <= 39.
Theorem decode_lt_K_gen : forall sub t rb b h b' nb, TblPD t rb -> SubGuardGen sub t rb ->
    br_bits b < KB -> inf_decode sub t rb b = DecOk h b' nb -> br_bits b' < KB.
Proof. pose proof HK as HKu.
  intros sub t rb b h b' nb Hpd Hg Hb Hd.
  unfold inf_decode in Hd. revert Hd.
  destruct (inf_fetch t rb b) as [h0 b0|b0|] eqn:Hf; intros Hd; [|discriminate|discriminate].
  destruct ((fetch_root_entry_K KB HK) t rb b h0 b0 Hpd Hb Hf) as (i & Hi & Hti).
  pose proof ((fetch_lt_K KB HK) t rb b h0 b0 Hpd Hb) as Hf8.
  (* F7B: the root entry's width row_K (1 <= c_bits h0) feeds the `< KB` drop arithmetic below *)
  assert (Hw0 : 1 <= c_bits h0 <= rb) by (pose proof Hpd as (_ & _ & Hw & _); rewrite <- Hti; exact (Hw i Hi)).
  cbv beta iota zeta in Hd. revert Hd.
  destruct (sub h0) eqn:Hs; intros Hd.
  - revert Hd.
    destruct (inf_fetch2 t h0 b0) as [h1 b1|b1|] eqn:Hf2; intros Hd; [|discriminate|discriminate].
    cbv beta iota zeta in Hd. injection Hd as Hh Hb' Hnb. subst b'.
    specialize (Hg i Hi). rewrite Hti in Hg. specialize (Hg Hs). destruct Hg as (H240 & Hnn & H0).
    (* the root fetch's bound needs 0 <= br_hold b in the STMT shape; it is unused, so supply the loop lemma directly *)
    unfold inf_fetch in Hf.
    destruct (proj2 ((fetch_go_lt_K KB HK) t rb Hpd _ b h0 b0 (or_introl Hb) Hf)) as [Hlo Hhi].
    destruct ((fetch2_lt_K_gen KB HK) t rb h0 b0 h1 b1 Hpd (ex_intro _ i (conj Hi Hti)) H240 Hnn H0 Hlo Hhi Hf2)
      as [_ [H2 Hnn1]].
    rewrite !br_dropbits_bits. lia.
  - cbv beta iota zeta in Hd. injection Hd as Hh Hb' Hnb. subst b'.
    unfold inf_fetch in Hf.
    destruct (proj2 ((fetch_go_lt_K KB HK) t rb Hpd _ b h0 b0 (or_introl Hb) Hf)) as [Hlo Hhi].
    rewrite br_dropbits_bits. lia.
Qed.

Theorem decode_lt_K_ptr : forall sub t rb b h b' nb, TblPD t rb -> SubGuardPtr sub t rb ->
    br_bits b < KB -> 0 <= br_hold b -> inf_decode sub t rb b = DecOk h b' nb -> br_bits b' < KB.
Proof. pose proof HK as HKu.
  intros sub t rb b h b' nb Hpd Hg Hb _ Hd.
  exact (decode_lt_K_gen sub t rb b h b' nb Hpd (subguard_ptr_gen sub t rb Hg) Hb Hd).
Qed.

End K_CfgBitsTblLeaf_decode.

(** the landed names as the 14-instances *)
Theorem decode_lt8_gen : forall sub t rb b h b' nb, TblPD t rb -> SubGuardGen sub t rb ->
    br_bits b < 14 -> inf_decode sub t rb b = DecOk h b' nb -> br_bits b' < 14.
Proof. exact (decode_lt_K_gen 14 ltac:(lia)). Qed.

Theorem decode_lt8_ptr : forall sub t rb b h b' nb, TblPD t rb -> SubGuardPtr sub t rb ->
    br_bits b < 14 -> 0 <= br_hold b -> inf_decode sub t rb b = DecOk h b' nb -> br_bits b' < 14.
Proof. exact (decode_lt_K_ptr 14 ltac:(lia)). Qed.

(* ######################################################################### *)
(* 5.  The fixed tables: a decidable checker                                  *)
(* ######################################################################### *)

Definition cbt_zseq (n : Z) : list Z := map Z.of_nat (seq 0 (Z.to_nat n)).

Lemma cbt_zseq_in : forall n i, 0 <= i < n -> In i (cbt_zseq n).
Proof.
  intros n i Hi. unfold cbt_zseq. apply in_map_iff. exists (Z.to_nat i).
  split; [apply Z2Nat.id; lia |].
  apply in_seq. split; [apply Nat.le_0_l | rewrite Nat.add_0_l; apply Z2Nat.inj_lt; lia].
Qed.

Lemma cbt_forallb_zseq : forall (f : Z -> bool) n,
  forallb f (cbt_zseq n) = true -> forall i, 0 <= i < n -> f i = true.
Proof. intros f n H i Hi. rewrite forallb_forall in H. apply H, cbt_zseq_in, Hi. Qed.

(** row i: width in [1, rb] and the whole residue class of i at that width carries the same width *)
Definition cbt_rowb (t : ztbl) (rb i : Z) : bool :=
  (1 <=? c_bits (t i)) && (c_bits (t i) <=? rb) &&
  forallb (fun m => c_bits (t (i mod 2 ^ c_bits (t i) + m * 2 ^ c_bits (t i))) =? c_bits (t i))
          (cbt_zseq (2 ^ (rb - c_bits (t i)))).
Definition cbt_replb (t : ztbl) (rb : Z) : bool := forallb (cbt_rowb t rb) (cbt_zseq (2 ^ rb)).
(** no pointer-shaped root entry at all (the fixed tables have no sub-tables) *)
Definition cbt_nosubb (t : ztbl) (rb : Z) : bool :=
  forallb (fun i => negb (Z.land (c_op (t i)) 240 =? 0) || (c_op (t i) =? 0)) (cbt_zseq (2 ^ rb)).

Lemma cbt_replb_sound : forall t rb, 0 <= rb -> cbt_replb t rb = true ->
  (forall i, 0 <= i < 2 ^ rb -> 1 <= c_bits (t i) <= rb) /\ RootReplicated t rb.
Proof.
  intros t rb Hrb H.
  assert (Hrow : forall i, 0 <= i < 2 ^ rb -> cbt_rowb t rb i = true)
    by (apply cbt_forallb_zseq; exact H).
  assert (Hw : forall i, 0 <= i < 2 ^ rb -> 1 <= c_bits (t i) <= rb).
  { intros i Hi. specialize (Hrow i Hi). unfold cbt_rowb in Hrow.
    apply andb_prop in Hrow as [Hrow _]. apply andb_prop in Hrow as [H1 H2].
    apply Z.leb_le in H1, H2. lia. }
  split; [exact Hw|].
  intros i j Hi Hj Hmod.
  specialize (Hrow i Hi). unfold cbt_rowb in Hrow.
  apply andb_prop in Hrow as [_ Hrow].
  pose proof (Hw i Hi) as HL.
  assert (HpL : 0 < 2 ^ c_bits (t i)) by (apply pow2_pos_z; lia).
  assert (Hm : 0 <= j / 2 ^ c_bits (t i) < 2 ^ (rb - c_bits (t i))).
  { split; [apply Z.div_pos; lia|].
    apply Z.div_lt_upper_bound; [lia|].
    rewrite <- Z.pow_add_r by lia.
    replace (c_bits (t i) + (rb - c_bits (t i))) with rb by lia. lia. }
  pose proof (cbt_forallb_zseq _ _ Hrow (j / 2 ^ c_bits (t i)) Hm) as Hj'.
  apply Z.eqb_eq in Hj'.
  rewrite Hmod in Hj'.
  replace (j mod 2 ^ c_bits (t i) + j / 2 ^ c_bits (t i) * 2 ^ c_bits (t i)) with j in Hj'.
  - exact Hj'.
  - rewrite Z.mod_eq by lia. ring.
Qed.

Lemma cbt_nosubb_sound : forall t rb, cbt_nosubb t rb = true -> SubPD t rb.
Proof.
  intros t rb H i Hi H240 Hnz.
  pose proof (cbt_forallb_zseq _ _ H i Hi) as Hb.
  apply orb_prop in Hb as [Hb|Hb].
  - apply negb_true_iff in Hb. apply Z.eqb_neq in Hb. contradiction.
  - apply Z.eqb_eq in Hb. contradiction.
Qed.

Lemma cbt_tblpd_of_checks : forall t rb, 0 <= rb ->
  cbt_replb t rb = true -> cbt_nosubb t rb = true -> TblPD t rb.
Proof.
  intros t rb Hrb Hr Hn.
  destruct (cbt_replb_sound t rb Hrb Hr) as [Hw HR].
  split; [exact Hrb|]. split; [|split; [exact Hw | apply cbt_nosubb_sound; exact Hn]].
  apply root_repl_gives_prefixdet; [intros i Hi; apply Hw; exact Hi | exact HR].
Qed.

Theorem fix_tblpd : FIX_TBLPD_STMT.
Proof.
  unfold FIX_TBLPD_STMT. split.
  - apply cbt_tblpd_of_checks; [lia | vm_compute; reflexivity | vm_compute; reflexivity].
  - apply cbt_tblpd_of_checks; [lia | vm_compute; reflexivity | vm_compute; reflexivity].
Qed.

(* ######################################################################### *)
(* 6.  inflate_table outputs: the root half, and the sub half's interface     *)
(* ######################################################################### *)

Lemma it_model_bits_pos : forall ty lens codes root0 t0 out,
  1 <= root0 -> it_model ty lens codes root0 t0 = Some out -> o_ret out = 0 -> 1 <= o_bits out.
Proof.
  intros ty lens codes root0 t0 out Hr Hm Hret.
  unfold it_model in Hm. revert Hm.
  destruct (it_pre ty lens codes root0 t0) as [ | temp | | c st] eqn:Hpre; intros Hm.
  - injection Hm as <-. cbn [o_ret] in Hret. lia.
  - injection Hm as <-. cbn [o_bits]. lia.
  - injection Hm as <-. cbn [o_ret] in Hret. lia.
  - pose proof (it_pre_root_pos ty lens codes root0 t0 c st Hr Hpre) as Hx.
    revert Hm.
    destruct (it_loop (S (Z.to_nat codes)) c st) as [[st'|st'|tt]|] eqn:Hloop; intros Hm;
      try discriminate Hm.
    + injection Hm as <-. cbn [o_bits]. exact Hx.
    + injection Hm as <-. cbn [o_ret] in Hret. lia.
Qed.

(** the ROOT half of the it_model table facts: true as stated (no type/codes premise needed) *)
Theorem it_tblpd_root : forall ty lens codes root0 t0 out,
    0 <= codes -> (forall i, 0 <= i < codes -> 0 <= lens i <= 15) -> 1 <= root0 <= 15 ->
    it_model ty lens codes root0 t0 = Some out -> o_ret out = 0 ->
    0 <= o_bits out
    /\ RootPrefixDet (o_tbl out) (o_bits out)
    /\ (forall i, 0 <= i < 2 ^ o_bits out -> 1 <= c_bits (o_tbl out i) <= o_bits out).
Proof.
  intros ty lens codes root0 t0 out Hcodes Hlens Hroot0 Hm Hret.
  split; [pose proof (it_model_bits_pos ty lens codes root0 t0 out ltac:(lia) Hm Hret); lia | split].
  - exact (it_prefixdet_root ty lens codes root0 t0 out Hcodes Hlens Hroot0 Hm Hret).
  - exact (it_covers_root_pos ty lens codes root0 t0 out Hcodes Hlens Hroot0 Hm Hret).
Qed.

(** the caller-side type/codes premise (it_wf's 4th conjunct): it is what makes every pointer-SHAPED root entry
    (op & 0xf0 = 0, op <> 0) a genuine sub-table pointer.  Without it (CT_CODES with a symbol >= 21, or any
    type outside {CODES, LENS, DISTS}) it_here writes [x_extra c (w - 20) = work (w - 20)] as op, which can be
    any small symbol index. *)
Definition ITWF (ty codes : Z) : Prop :=
  ty = CT_CODES /\ codes <= 19 \/ ty = CT_LENS /\ codes <= 288 \/ ty = CT_DISTS /\ codes <= 32.

(* ######################################################################### *)
(* S1.  Prefix Kraft mass at scale 2^15                                        *)
(* ######################################################################### *)

Lemma it_mass_snoc : forall n len cnt,
  it_mass (S n) len cnt = 2 * it_mass n len cnt + cnt (len + Z.of_nat n).
Proof.
  induction n as [|n IH]; intros len cnt.
  - cbn [it_mass]. change (Z.of_nat 0) with 0. rewrite Z.pow_0_r, !Z.add_0_r. ring.
  - change (it_mass (S (S n)) len cnt)
      with (cnt len * 2 ^ Z.of_nat (S n) + it_mass (S n) (len + 1) cnt).
    rewrite IH.
    change (it_mass (S n) len cnt) with (cnt len * 2 ^ Z.of_nat n + it_mass n (len + 1) cnt).
    rewrite pow2_succ_nat, Nat2Z.inj_succ.
    replace (len + Z.succ (Z.of_nat n)) with (len + 1 + Z.of_nat n) by lia.
    ring.
Qed.

(** sum over l in [1, m] of cnt l * 2^(15 - l) *)
Definition pmass (m : Z) (cnt : zarr) : Z := it_mass (Z.to_nat m) 1 cnt * 2 ^ (15 - m).

Lemma pmass_0 : forall cnt, pmass 0 cnt = 0.
Proof. intros cnt. unfold pmass. change (Z.to_nat 0) with 0%nat. cbn [it_mass]. apply Z.mul_0_l. Qed.

Lemma pmass_succ : forall m cnt, 0 <= m <= 14 ->
  pmass (m + 1) cnt = pmass m cnt + cnt (m + 1) * 2 ^ (15 - (m + 1)).
Proof.
  intros m cnt Hm. unfold pmass.
  rewrite Z2Nat.inj_add by lia. change (Z.to_nat 1) with 1%nat. rewrite Nat.add_1_r.
  rewrite it_mass_snoc, Z2Nat.id by lia.
  replace (15 - m) with ((15 - (m + 1)) + 1) by lia.
  rewrite Z.pow_add_r by lia. rewrite Z.pow_1_r.
  replace (1 + m) with (m + 1) by lia. ring.
Qed.

Lemma pmass_15 : forall cnt, pmass 15 cnt = it_mass 15%nat 1 cnt.
Proof. intros cnt. unfold pmass. change (Z.to_nat 15) with 15%nat. rewrite Z.sub_diag, Z.pow_0_r. ring. Qed.

Lemma pmass_dec : forall m cnt l, 1 <= l <= m -> m <= 15 ->
  pmass m (zset cnt l (cnt l - 1)) = pmass m cnt - 2 ^ (15 - l).
Proof.
  intros m cnt l Hl Hm. unfold pmass.
  rewrite (it_mass_dec (Z.to_nat m) 1 cnt l) by (rewrite Z2Nat.id; lia).
  rewrite Z2Nat.id by lia.
  rewrite Z.mul_sub_distr_r, <- Z.pow_add_r by lia.
  f_equal. f_equal. lia.
Qed.

Lemma pmass_ext : forall m a b, 0 <= m <= 15 ->
  (forall l, 1 <= l <= m -> a l = b l) -> pmass m a = pmass m b.
Proof.
  intros m a b Hm H. unfold pmass. f_equal. apply it_mass_ext.
  intros j Hj. apply H. rewrite Z2Nat.id in Hj; lia.
Qed.

Lemma pmass_zero_on : forall m cnt, 0 <= m <= 15 ->
  (forall l, 1 <= l <= m -> cnt l = 0) -> pmass m cnt = 0.
Proof.
  intros m cnt Hm H. unfold pmass. rewrite it_mass_zero_on; [ring|].
  intros j Hj. apply H. rewrite Z2Nat.id in Hj; lia.
Qed.

Lemma pmass_nonneg : forall m cnt, 0 <= m <= 15 ->
  (forall l, 1 <= l <= m -> 0 <= cnt l) -> 0 <= pmass m cnt.
Proof.
  intros m cnt Hm H. unfold pmass. apply Z.mul_nonneg_nonneg.
  - apply it_mass_nonneg. intros j Hj. apply H. rewrite Z2Nat.id in Hj; lia.
  - apply Z.pow_nonneg. lia.
Qed.

Lemma pmass_mono : forall m n cnt, 0 <= m <= n -> n <= 15 ->
  (forall l, 1 <= l <= n -> 0 <= cnt l) -> pmass m cnt <= pmass n cnt.
Proof.
  intros m n cnt Hmn Hn Hnn.
  assert (H : forall k, m + Z.of_nat k <= n -> pmass m cnt <= pmass (m + Z.of_nat k) cnt).
  { induction k as [|k IH]; intros Hk.
    - change (Z.of_nat 0) with 0. rewrite Z.add_0_r. lia.
    - rewrite Nat2Z.inj_succ in *.
      replace (m + Z.succ (Z.of_nat k)) with ((m + Z.of_nat k) + 1) by lia.
      rewrite pmass_succ by lia.
      pose proof (IH ltac:(lia)). pose proof (Hnn (m + Z.of_nat k + 1) ltac:(lia)).
      pose proof (Z.pow_nonneg 2 (15 - (m + Z.of_nat k + 1)) ltac:(lia)). nia. }
  specialize (H (Z.to_nat (n - m))). rewrite Z2Nat.id in H by lia.
  replace (m + (n - m)) with n in H by lia. apply H. lia.
Qed.

Lemma pmass_zero_above : forall m mx cnt, 0 <= mx <= m -> m <= 15 ->
  (forall l, mx < l <= 15 -> cnt l = 0) -> pmass m cnt = pmass mx cnt.
Proof.
  intros m mx cnt Hmx Hm Hz.
  assert (H : forall k, mx + Z.of_nat k <= 15 -> pmass (mx + Z.of_nat k) cnt = pmass mx cnt).
  { induction k as [|k IH]; intros Hk.
    - change (Z.of_nat 0) with 0. rewrite Z.add_0_r. reflexivity.
    - rewrite Nat2Z.inj_succ in *.
      replace (mx + Z.succ (Z.of_nat k)) with ((mx + Z.of_nat k) + 1) by lia.
      rewrite pmass_succ by lia. rewrite IH by lia. rewrite (Hz (mx + Z.of_nat k + 1)) by lia. ring. }
  specialize (H (Z.to_nat (m - mx))). rewrite Z2Nat.id in H by lia.
  replace (mx + (m - mx)) with m in H by lia. apply H. lia.
Qed.

(* ######################################################################### *)
(* S2.  it_subsz: the sub-table is sized so the remaining codes fill it        *)
(* ######################################################################### *)

Definition SubszOk (drop mx : Z) (cnt : zarr) (curr r : Z) : Prop :=
  curr <= r /\ r + drop <= mx /\ (r + drop = mx \/ 2 ^ (15 - drop) <= pmass (r + drop) cnt).

Lemma subsz_spec : forall n cnt drop mx curr left,
  0 <= drop -> 1 <= curr -> curr + drop <= mx -> mx <= 15 ->
  mx - drop - curr < Z.of_nat n ->
  left * 2 ^ (15 - drop - curr) = 2 ^ (15 - drop) - pmass (curr + drop - 1) cnt ->
  SubszOk drop mx cnt curr (it_subsz n cnt drop mx curr left).
Proof.
  induction n as [|n IH]; intros cnt drop mx curr left Hd Hc Hcm Hmx Hfuel Hinv.
  - exfalso. cbn in Hfuel. lia.
  - cbn [it_subsz].
    destruct (Z.ltb_spec (curr + drop) mx) as [Hlt|Hge].
    + destruct (Z.leb_spec (left - cnt (curr + drop)) 0) as [Hle|Hgt].
      * (* full: return curr *)
        split; [lia|]. split; [lia|]. right.
        pose proof (pmass_succ (curr + drop - 1) cnt ltac:(lia)) as Hsucc.
        replace (curr + drop - 1 + 1) with (curr + drop) in Hsucc by lia.
        assert (Hp : 0 < 2 ^ (15 - drop - curr)) by (apply pow2_pos_z; lia).
        assert (Hpow : 2 ^ (15 - (curr + drop)) = 2 ^ (15 - drop - curr)) by (f_equal; lia).
        rewrite Hsucc, Hpow.
        (* pmass (curr+drop) = 2^(15-drop) - (left - cnt) * 2^e  with  left - cnt <= 0 *)
        nia.
      * (* grow *)
        assert (Hinv' : (left - cnt (curr + drop)) * 2 * 2 ^ (15 - drop - (curr + 1))
                        = 2 ^ (15 - drop) - pmass (curr + 1 + drop - 1) cnt).
        { replace (curr + 1 + drop - 1) with (curr + drop - 1 + 1) by lia.
          rewrite pmass_succ by lia.
          replace (curr + drop - 1 + 1) with (curr + drop) by lia.
          assert (Hpow : 2 ^ (15 - drop - curr) = 2 * 2 ^ (15 - drop - (curr + 1))).
          { replace (15 - drop - curr) with (Z.succ (15 - drop - (curr + 1))) by lia.
            rewrite Z.pow_succ_r by lia. ring. }
          assert (Hpow2 : 2 ^ (15 - (curr + drop)) = 2 * 2 ^ (15 - drop - (curr + 1))).
          { replace (15 - (curr + drop)) with (Z.succ (15 - drop - (curr + 1))) by lia.
            rewrite Z.pow_succ_r by lia. ring. }
          rewrite Hpow in Hinv. rewrite Hpow2. nia. }
        destruct (IH cnt drop mx (curr + 1) ((left - cnt (curr + drop)) * 2)
                    Hd ltac:(lia) ltac:(lia) Hmx ltac:(lia) Hinv') as (H1 & H2 & H3).
        split; [lia | split; [exact H2 | exact H3]].
    + split; [lia | split; [lia | left; lia]].
Qed.

(* ######################################################################### *)
(* S3.  Views (shifted tables) and pointwise congruences                       *)
(* ######################################################################### *)

Definition view (t : ztbl) (base : Z) : ztbl := fun j => t (base + j).

Lemma it_fill_ext : forall n t1 t2 bi incr h,
  (forall j, t1 j = t2 j) -> forall j, it_fill n t1 bi incr h j = it_fill n t2 bi incr h j.
Proof.
  induction n as [|n IH]; intros t1 t2 bi incr h Hext j; cbn [it_fill]; [apply Hext|].
  apply IH. intros k. unfold tset.
  destruct (Z.eqb k (bi + Z.of_nat n * incr)); [reflexivity | apply Hext].
Qed.

Lemma view_tset : forall t base x h j, view (tset t (base + x) h) base j = tset (view t base) x h j.
Proof.
  intros t base x h j. unfold view, tset.
  destruct (Z.eqb_spec (base + j) (base + x)) as [E|E]; destruct (Z.eqb_spec j x) as [E'|E'];
    try reflexivity; exfalso; lia.
Qed.

Lemma it_fill_view : forall n t base bi incr h j,
  it_fill n t (base + bi) incr h (base + j) = it_fill n (view t base) bi incr h j.
Proof.
  induction n as [|n IH]; intros t base bi incr h j; cbn [it_fill]; [reflexivity|].
  replace (base + bi + Z.of_nat n * incr) with (base + (bi + Z.of_nat n * incr)) by ring.
  rewrite IH. apply it_fill_ext. intros k. apply view_tset.
Qed.

Lemma classdone_ext : forall root t1 t2 P,
  (forall j, t1 j = t2 j) -> ClassDone root t1 P -> ClassDone root t2 P.
Proof.
  intros root t1 t2 P Hext H i Hi Hu j Hj Hmod.
  rewrite <- (Hext i) in Hmod. rewrite <- (Hext i), <- (Hext j).
  exact (H i Hi Hu j Hj Hmod).
Qed.

Lemma covbelow_ext : forall root t1 t2 P,
  (forall j, t1 j = t2 j) -> CovBelow root t1 P -> CovBelow root t2 P.
Proof. intros root t1 t2 P Hext H j Hj Hu. rewrite <- (Hext j). exact (H j Hj Hu). Qed.

Lemma rootprefixdet_ext_on : forall root t1 t2,
  (forall j, 0 <= j < 2 ^ root -> t1 j = t2 j) -> RootPrefixDet t1 root -> RootPrefixDet t2 root.
Proof.
  intros root t1 t2 Hext H i j k Hi Hj Hk Hle Hmod.
  rewrite <- (Hext i Hi) in Hle. rewrite <- (Hext i Hi), <- (Hext j Hj).
  exact (H i j k Hi Hj Hk Hle Hmod).
Qed.

Lemma covbelow_zero : forall root t, 0 <= root <= 15 -> CovBelow root t 0.
Proof.
  intros root t Hr j Hj Hu.
  pose proof (zrev_nonneg (Z.to_nat root) j). pose proof (pow2_pos_z (15 - root) ltac:(lia)).
  exfalso. nia.
Qed.

(* ######################################################################### *)
(* S4.  Leaf entries are never pointer-shaped (under the it_wf type/codes premise) *)
(* ######################################################################### *)

Definition LeafOp (e : Code) : Prop := c_op e = 0 \/ Z.land (c_op e) 240 <> 0.

Lemma leaf_mkCodeT_0 : forall b v, LeafOp (mkCodeT 0 b v).
Proof. intros b v. left. reflexivity. Qed.

Lemma leaf_mkCodeT_64 : forall b v, LeafOp (mkCodeT 64 b v).
Proof. intros b v. right. intro H. vm_compute in H. discriminate H. Qed.

Lemma leaf_mkCodeT_96 : forall b v, LeafOp (mkCodeT (32 + 64) b v).
Proof. intros b v. right. intro H. vm_compute in H. discriminate H. Qed.

Definition ok_ext (e : Z) : bool :=
  (e =? 0) || ((0 <=? e) && (e <? 256) && negb (Z.land e 240 =? 0)).

Lemma ok_ext_leaf : forall e b v, ok_ext e = true -> LeafOp (mkCodeT e b v).
Proof.
  intros e b v H. unfold ok_ext in H. apply orb_prop in H as [H|H].
  - apply Z.eqb_eq in H. subst e. apply leaf_mkCodeT_0.
  - apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
    apply Z.leb_le in H1. apply Z.ltb_lt in H2. apply negb_true_iff in H3. apply Z.eqb_neq in H3.
    right. unfold mkCodeT. cbn [c_op]. rewrite u8_id by lia. exact H3.
Qed.

Lemma zlist_ok_ext : forall l, forallb ok_ext (0 :: l) = true -> forall i, ok_ext (zlist l i) = true.
Proof.
  intros l H i. rewrite forallb_forall in H. unfold zlist.
  destruct (nth_in_or_default (Z.to_nat i) l 0) as [Hin | Heq].
  - apply H. right. exact Hin.
  - rewrite Heq. apply H. left. reflexivity.
Qed.

Lemma lext_ok : forallb ok_ext (0 :: lext_l) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma dext_ok : forallb ok_ext (0 :: dext_l) = true.
Proof. vm_compute. reflexivity. Qed.

Definition CtxLeafOk (c : ItCtx) : Prop :=
  (x_match c = 20 /\ forall j, x_work c j < 19)
  \/ (x_match c = 257 /\ x_extra c = lext)
  \/ (x_match c = 0 /\ x_extra c = dext).

Lemma it_here_leaf : forall c st, CtxLeafOk c -> LeafOp (it_here c st).
Proof.
  intros c st Hc. unfold it_here. cbv zeta.
  destruct (Z.ltb_spec (x_work c (s_sym st) + 1) (x_match c)) as [Hlt|Hge].
  - apply leaf_mkCodeT_0.
  - destruct (Z.leb_spec (x_match c) (x_work c (s_sym st))) as [Hle|Hgt].
    + destruct Hc as [[Hm Hw] | [[Hm He] | [Hm He]]].
      * exfalso. specialize (Hw (s_sym st)). lia.
      * rewrite He. unfold lext. apply ok_ext_leaf. apply zlist_ok_ext. exact lext_ok.
      * rewrite He. unfold dext. apply ok_ext_leaf. apply zlist_ok_ext. exact dext_ok.
    + apply leaf_mkCodeT_96.
Qed.

Lemma it_sort_work_lt : forall n i lens offs work B,
  (forall j, work j < B) -> i + Z.of_nat n <= B ->
  forall j, snd (it_sort n i lens offs work) j < B.
Proof.
  induction n as [|n IH]; intros i lens offs work B Hw Hb j; cbn [it_sort]; cbv zeta.
  - cbn [snd]. apply Hw.
  - rewrite Nat2Z.inj_succ in Hb.
    destruct (Z.eqb (lens i) 0).
    + apply IH; [exact Hw | lia].
    + apply IH; [| lia].
      intro j'. unfold zset. destruct (Z.eqb j' (offs (lens i))); [lia | apply Hw].
Qed.

Lemma sw_work_lt : forall lens codes j, 0 <= codes -> sw_work lens codes j < Z.max 1 codes.
Proof.
  intros lens codes j Hc. unfold sw_work.
  apply it_sort_work_lt; [intros k; unfold zzero, zconst; lia | rewrite Z2Nat.id; lia].
Qed.

Lemma cbt_prego_inj_c : forall c1 st1 c2 st2, PreGo c1 st1 = PreGo c2 st2 -> c1 = c2.
Proof. intros c1 st1 c2 st2 H. injection H as H _. exact H. Qed.

Lemma it_pre_go_ctx : forall ty lens codes root0 t0 c st,
  it_pre ty lens codes root0 t0 = PreGo c st ->
  x_type c = ty /\ x_codes c = codes
  /\ x_match c = (if Z.eqb ty CT_LENS then 257 else if Z.eqb ty CT_DISTS then 0 else 20)
  /\ x_extra c = (if Z.eqb ty CT_LENS then lext else if Z.eqb ty CT_DISTS then dext else x_work c)
  /\ x_work c = sw_work lens codes
  /\ s_used st = Z.shiftl 1 (x_root c) /\ s_curr st = x_root c /\ s_next st = 0 /\ s_drop st = 0.
Proof.
  intros ty lens codes root0 t0 c st H.
  unfold it_pre in H. cbv zeta in H.
  destruct (Z.eqb (it_findmax 15%nat MAXBITS (it_count (Z.to_nat codes) 0 lens zzero)) 0);
    [discriminate H|].
  destruct (it_kraft 15%nat 1 1 (it_count (Z.to_nat codes) 0 lens zzero)) as [lft|];
    [|discriminate H].
  destruct (it_incomplete ty lft _); [discriminate H|].
  destruct (it_enough ty _); [discriminate H|].
  pose proof (cbt_prego_inj_c _ _ _ _ H) as Hc. pose proof (prego_inj_st _ _ _ _ H) as Hst.
  rewrite <- Hc, <- Hst.
  cbn [x_type x_codes x_match x_extra x_work x_root s_used s_curr s_next s_drop].
  repeat split; reflexivity.
Qed.

Lemma ctx_leaf_of_wf : forall ty lens codes root0 t0 c st,
  0 <= codes -> ITWF ty codes ->
  it_pre ty lens codes root0 t0 = PreGo c st -> CtxLeafOk c.
Proof.
  intros ty lens codes root0 t0 c st Hcodes Hwf Hpre.
  destruct (it_pre_go_ctx ty lens codes root0 t0 c st Hpre) as (Hty & Hcod & Hm & He & Hw & _).
  unfold CtxLeafOk, ITWF, CT_CODES, CT_LENS, CT_DISTS in *.
  destruct Hwf as [[Hty0 Hc] | [[Hty0 Hc] | [Hty0 Hc]]]; subst ty; cbn in Hm, He.
  - left. split; [exact Hm|]. intros j. rewrite Hw.
    pose proof (sw_work_lt lens codes j Hcodes). lia.
  - right; left. split; [exact Hm | exact He].
  - right; right. split; [exact Hm | exact He].
Qed.

(* ######################################################################### *)
(* S5.  The full field shape of an ItCont step                                 *)
(* ######################################################################### *)

Definition FILL (c : ItCtx) (st : ItSt) : ztbl :=
  it_fill (Z.to_nat (Z.shiftl 1 (s_curr st) / Z.shiftl 1 (s_len st - s_drop st)))
          (s_tbl st) (s_next st + Z.shiftr (s_huff st) (s_drop st))
          (Z.shiftl 1 (s_len st - s_drop st)) (it_here c st).

Definition ContFields (c : ItCtx) (st st' : ItSt) : Prop :=
  s_huff st' = it_rev_incr (s_huff st) (s_len st)
  /\ s_count st' = zset (s_count st) (s_len st) (s_count st (s_len st) - 1)
  /\ ( (s_tbl st' = FILL c st /\ s_next st' = s_next st /\ s_curr st' = s_curr st
        /\ s_drop st' = s_drop st /\ s_low st' = s_low st /\ s_used st' = s_used st
        /\ (s_len st' <= x_root c \/ Z.land (s_huff st') (x_mask c) = s_low st))
     \/ (exists curr',
          s_tbl st' = tset (FILL c st) (s_low st')
                        (mkCodeT curr' (x_root c) (s_next st + Z.shiftl 1 (s_curr st)))
          /\ s_next st' = s_next st + Z.shiftl 1 (s_curr st)
          /\ s_curr st' = curr'
          /\ s_drop st' = (if Z.eqb (s_drop st) 0 then x_root c else s_drop st)
          /\ s_low st' = Z.land (s_huff st') (x_mask c)
          /\ s_used st' = s_used st + Z.shiftl 1 curr'
          /\ x_root c < s_len st'
          /\ Z.land (s_huff st') (x_mask c) <> s_low st
          /\ curr' = it_subsz 16%nat (s_count st') (s_drop st') (x_max c)
                       (s_len st' - s_drop st') (Z.shiftl 1 (s_len st' - s_drop st'))) ).

Lemma cont_fields : forall c st st', it_step c st = ItCont st' -> ContFields c st st'.
Proof.
  intros c st st' Hstep. unfold it_step in Hstep. cbv zeta in Hstep.
  set (cnt1 := zset (s_count st) (s_len st) (s_count st (s_len st) - 1)) in *.
  set (huff1 := it_rev_incr (s_huff st) (s_len st)) in *.
  unfold ContFields, FILL.
  destruct (Z.eqb (cnt1 (s_len st)) 0) eqn:Hhit.
  - destruct (Z.eqb (s_len st) (x_max c)) eqn:Hmxeq; cbn [andb] in Hstep; [discriminate Hstep|].
    destruct (Z.ltb (x_root c) (x_lens c (x_work c (s_sym st + 1)))) eqn:Hgt.
    + destruct (Z.eqb (Z.land huff1 (x_mask c)) (s_low st)) eqn:Hsame; cbn [andb negb] in Hstep.
      * injection Hstep as Hst'. subst st'.
        cbn [s_huff s_count s_tbl s_next s_curr s_drop s_low s_used s_len].
        split; [reflexivity | split; [reflexivity | left]].
        repeat split; try reflexivity. right. apply Z.eqb_eq. exact Hsame.
      * match type of Hstep with
        | (if it_enough _ (_ + Z.shiftl 1 ?cv) then _ else _) = _ =>
            remember cv as curr' eqn:Hcurr'
        end.
        match type of Hstep with
        | (if ?b then _ else _) = _ => remember b as en eqn:Hen; destruct en
        end; [discriminate Hstep|].
        injection Hstep as Hst'. subst st'.
        cbn [s_huff s_count s_tbl s_next s_curr s_drop s_low s_used s_len].
        split; [reflexivity | split; [reflexivity | right]].
        exists curr'. repeat split; try reflexivity.
        -- apply Z.ltb_lt. exact Hgt.
        -- apply Z.eqb_neq. exact Hsame.
        -- exact Hcurr'.
    + cbn [andb] in Hstep. injection Hstep as Hst'. subst st'.
      cbn [s_huff s_count s_tbl s_next s_curr s_drop s_low s_used s_len].
      split; [reflexivity | split; [reflexivity | left]].
      repeat split; try reflexivity. left. apply Z.ltb_ge. exact Hgt.
  - cbn [andb] in Hstep.
    destruct (Z.ltb (x_root c) (s_len st)) eqn:Hgt.
    + destruct (Z.eqb (Z.land huff1 (x_mask c)) (s_low st)) eqn:Hsame; cbn [andb negb] in Hstep.
      * injection Hstep as Hst'. subst st'.
        cbn [s_huff s_count s_tbl s_next s_curr s_drop s_low s_used s_len].
        split; [reflexivity | split; [reflexivity | left]].
        repeat split; try reflexivity. right. apply Z.eqb_eq. exact Hsame.
      * match type of Hstep with
        | (if it_enough _ (_ + Z.shiftl 1 ?cv) then _ else _) = _ =>
            remember cv as curr' eqn:Hcurr'
        end.
        match type of Hstep with
        | (if ?b then _ else _) = _ => remember b as en eqn:Hen; destruct en
        end; [discriminate Hstep|].
        injection Hstep as Hst'. subst st'.
        cbn [s_huff s_count s_tbl s_next s_curr s_drop s_low s_used s_len].
        split; [reflexivity | split; [reflexivity | right]].
        exists curr'. repeat split; try reflexivity.
        -- apply Z.ltb_lt. exact Hgt.
        -- apply Z.eqb_neq. exact Hsame.
        -- exact Hcurr'.
    + cbn [andb] in Hstep. injection Hstep as Hst'. subst st'.
      cbn [s_huff s_count s_tbl s_next s_curr s_drop s_low s_used s_len].
      split; [reflexivity | split; [reflexivity | left]].
      repeat split; try reflexivity. left. apply Z.ltb_ge. exact Hgt.
Qed.

(* ######################################################################### *)
(* S6.  The sub-table invariant                                                *)
(* ######################################################################### *)

(** the position at which root prefix [p]'s unit starts *)
Definition ustart (R p : Z) : Z := zrev (Z.to_nat R) p * 2 ^ (15 - R).

(** a root entry whose unit is done: a leaf, or a genuine pointer whose sub-table lies in [2^R, nx) and is
    prefix-deterministic with positive widths *)
Definition PtrOk (R nx : Z) (t : ztbl) (i : Z) : Prop :=
  LeafOp (t i)
  \/ (0 < c_op (t i) /\ 2 ^ R <= c_val (t i) /\ c_val (t i) + 2 ^ c_op (t i) <= nx
      /\ RootPrefixDet (view t (c_val (t i))) (c_op (t i))
      /\ (forall j, 0 <= j < 2 ^ c_op (t i) -> 1 <= c_bits (t (c_val (t i) + j)))).

Definition DonePtrs (R nx : Z) (t : ztbl) (P : Z) : Prop :=
  forall i, 0 <= i < 2 ^ R -> UnitDone R i P -> PtrOk R nx t i.

Definition SubSt (c : ItCtx) (cnt0 : zarr) (st : ItSt) : Prop :=
  DonePtrs (x_root c) (s_next st) (s_tbl st) (Pos (it_mass 15%nat 1 cnt0) st)
  /\ s_next st + 2 ^ s_curr st = s_used st
  /\ ( (s_len st <= x_root c /\ s_used st = 2 ^ x_root c)
       \/ (x_root c < s_len st
           /\ c_op (s_tbl st (s_low st)) = s_curr st
           /\ c_val (s_tbl st (s_low st)) = s_next st
           /\ 1 <= s_curr st /\ s_curr st + x_root c <= x_max c
           /\ ClassDone (s_curr st) (view (s_tbl st) (s_next st))
                ((Pos (it_mass 15%nat 1 cnt0) st - ustart (x_root c) (s_low st)) * 2 ^ x_root c)
           /\ CovBelow (s_curr st) (view (s_tbl st) (s_next st))
                ((Pos (it_mass 15%nat 1 cnt0) st - ustart (x_root c) (s_low st)) * 2 ^ x_root c)
           /\ ustart (x_root c) (s_low st) + 2 ^ (15 - x_root c) - Pos (it_mass 15%nat 1 cnt0) st
              <= pmass (s_curr st + x_root c) (s_count st)
           /\ s_used st <= 2 ^ x_root c
                           + (zrev (Z.to_nat (x_root c)) (s_low st) + 1) * 2 ^ (x_max c - x_root c)) ).

Lemma ptrok_ext : forall R nx nx' t1 t2 i, nx <= nx' -> t1 i = t2 i ->
  (forall j, 2 ^ R <= j < nx -> t1 j = t2 j) -> PtrOk R nx t1 i -> PtrOk R nx' t2 i.
Proof.
  intros R nx nx' t1 t2 i Hnx Hi Hreg [Hleaf | (Hop & Hlo & Hhi & HR & Hpos)].
  - left. rewrite <- Hi. exact Hleaf.
  - right. rewrite <- Hi.
    assert (Hp : 0 < 2 ^ c_op (t1 i)) by (apply pow2_pos_z; lia).
    split; [exact Hop | split; [exact Hlo | split; [lia |]]].
    split.
    + apply (rootprefixdet_ext_on _ (view t1 (c_val (t1 i)))); [| exact HR].
      intros j Hj. unfold view. apply Hreg. lia.
    + intros j Hj. rewrite <- Hreg by lia. exact (Hpos j Hj).
Qed.

Lemma view_fill : forall n t base bi incr h j,
  view (it_fill n t (base + bi) incr h) base j = it_fill n (view t base) bi incr h j.
Proof.
  intros n t base bi incr h j.
  change (view (it_fill n t (base + bi) incr h) base j) with (it_fill n t (base + bi) incr h (base + j)).
  apply it_fill_view.
Qed.

(** the split of the position link at a phase-2 state: P = (unit start of low) + (sub position) *)
Lemma pos_split : forall R len huff,
  1 <= R -> R < len -> len <= 15 -> 0 <= huff < 2 ^ len ->
  zrev (Z.to_nat len) huff * 2 ^ (15 - len)
  = ustart R (huff mod 2 ^ R) + zrev (Z.to_nat (len - R)) (huff / 2 ^ R) * 2 ^ (15 - len).
Proof.
  intros R len huff HR Hrl Hlen Hhuff.
  assert (HpR : 0 < 2 ^ R) by (apply pow2_pos_z; lia).
  set (a := huff mod 2 ^ R). set (b := huff / 2 ^ R).
  assert (Ha : 0 <= a < 2 ^ Z.of_nat (Z.to_nat R))
    by (rewrite Z2Nat.id by lia; apply Z.mod_pos_bound; exact HpR).
  assert (Hab : a + b * 2 ^ R = huff).
  { unfold a, b. pose proof (Z.div_mod huff (2 ^ R) ltac:(lia)) as Hdm.
    rewrite Z.mul_comm in Hdm. lia. }
  assert (Hz : zrev (Z.to_nat len) huff
               = zrev (Z.to_nat R) a * 2 ^ (len - R) + zrev (Z.to_nat (len - R)) b).
  { pose proof (zrev_split (Z.to_nat R) (Z.to_nat (len - R)) a b Ha) as Hs.
    rewrite !Z2Nat.id in Hs by lia.
    rewrite <- Z2Nat.inj_add in Hs by lia.
    replace (R + (len - R)) with len in Hs by lia.
    rewrite Hab in Hs. exact Hs. }
  rewrite Hz. unfold ustart.
  rewrite Z.mul_add_distr_r, <- Z.mul_assoc, <- Z.pow_add_r by lia.
  replace (len - R + (15 - len)) with (15 - R) by lia.
  reflexivity.
Qed.

(* ######################################################################### *)
(* S7.  What one fill does to the sub-table invariant                          *)
(* ######################################################################### *)

Ltac sub_intro Hctx Hinv :=
  destruct Hctx as (Hroot & Hmask & Hmx & Hmxnz & Hmxz & Hnn & Hcodes & Hlens & Hcnt0 & Hwork
                    & Hupper & Hcase & Hrootmx);
  destruct Hinv as (Hlen & Hhuff & HwinL & HwinU & Hcnt & Hpos & Hcov & Hphase).

(** phase 1: the fill is the root class of huff *)
Lemma fill_phase1 : forall c cnt0 st, CovCtxOk c cnt0 -> CovInv c cnt0 st -> s_len st <= x_root c ->
  FILL c st = it_fill (Z.to_nat (2 ^ (x_root c - s_len st))) (s_tbl st) (s_huff st) (2 ^ s_len st) (it_here c st).
Proof.
  intros c cnt0 st Hctx Hinv Hle. sub_intro Hctx Hinv.
  destruct Hphase as [(Hd & Hc & Hnx & Hlow & Hlr) | (Hd & Hrl & _)]; [| exfalso; lia].
  unfold FILL. rewrite Hd, Hc, Hnx, Z.shiftr_0_r, Z.sub_0_r, Z.add_0_l.
  rewrite (shiftl1 (s_len st)) by lia. rewrite (shiftl1 (x_root c)) by lia.
  rewrite <- Z.pow_sub_r by lia. reflexivity.
Qed.

(** phase 2: the sizing invariant forces the code to fit the current sub-table *)
Lemma sub_len_le_curr : forall c cnt0 st, CovCtxOk c cnt0 -> CovInv c cnt0 st -> SubSt c cnt0 st ->
  x_root c < s_len st -> s_len st - x_root c <= s_curr st.
Proof.
  intros c cnt0 st Hctx Hinv Hsub Hrl. sub_intro Hctx Hinv.
  destruct Hsub as (Hdone & Hused & [(Hlr & _) | (_ & Hop & Hval & Hc1 & Hcm & Hcd & Hcb & Hsz & Hub)]);
    [exfalso; lia|].
  destruct Hphase as [(Hd & Hc & Hnx & Hlow & Hlr) | (Hd & _ & Hnx & Hlow & Hlb)]; [exfalso; lia|].
  (* P is inside the unit of low *)
  assert (Hin : Pos (it_mass 15%nat 1 cnt0) st < ustart (x_root c) (s_low st) + 2 ^ (15 - x_root c)).
  { rewrite Hpos, Hlow. unfold ustart.
    pose proof (pos_in_root_unit_z (x_root c) (s_len st) (s_huff st) ltac:(lia) ltac:(lia) Hhuff). lia. }
  destruct (Z.le_gt_cases (s_len st - x_root c) (s_curr st)) as [Hok|Hbad]; [exact Hok | exfalso].
  assert (Hz : pmass (s_curr st + x_root c) (s_count st) = 0).
  { apply pmass_zero_on; [lia|]. intros l Hl. rewrite (Hcnt l ltac:(lia)).
    destruct (Z.ltb_spec l (s_len st)) as [H1|H1]; [reflexivity | lia]. }
  lia.
Qed.

Lemma fill_phase2 : forall c cnt0 st, CovCtxOk c cnt0 -> CovInv c cnt0 st -> SubSt c cnt0 st ->
  x_root c < s_len st ->
  FILL c st = it_fill (Z.to_nat (2 ^ (s_curr st - (s_len st - x_root c)))) (s_tbl st)
                (s_next st + s_huff st / 2 ^ x_root c) (2 ^ (s_len st - x_root c)) (it_here c st).
Proof.
  intros c cnt0 st Hctx Hinv Hsub Hrl.
  pose proof (sub_len_le_curr c cnt0 st Hctx Hinv Hsub Hrl) as Hlc.
  sub_intro Hctx Hinv.
  destruct Hphase as [(Hd & Hc & Hnx & Hlow & Hlr) | (Hd & _ & Hnx & Hlow & Hlb)]; [exfalso; lia|].
  unfold FILL. rewrite Hd.
  rewrite (shiftl1 (s_curr st)) by lia. rewrite (shiftl1 (s_len st - x_root c)) by lia.
  rewrite <- Z.pow_sub_r by lia. rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

(** phase 2: where the position sits relative to the current unit *)
Lemma sub_pos_facts : forall c cnt0 st, CovCtxOk c cnt0 -> CovInv c cnt0 st -> x_root c < s_len st ->
  Pos (it_mass 15%nat 1 cnt0) st
  = ustart (x_root c) (s_low st)
    + zrev (Z.to_nat (s_len st - x_root c)) (s_huff st / 2 ^ x_root c) * 2 ^ (15 - s_len st)
  /\ 0 <= s_huff st / 2 ^ x_root c < 2 ^ (s_len st - x_root c)
  /\ ustart (x_root c) (s_low st) <= Pos (it_mass 15%nat 1 cnt0) st
  /\ Pos (it_mass 15%nat 1 cnt0) st + 2 ^ (15 - s_len st)
     <= ustart (x_root c) (s_low st) + 2 ^ (15 - x_root c).
Proof.
  intros c cnt0 st Hctx Hinv Hrl. sub_intro Hctx Hinv.
  destruct Hphase as [(Hd & Hc & Hnx & Hlow & Hlr) | (Hd & _ & Hnx & Hlow & Hlb)]; [exfalso; lia|].
  assert (HpR : 0 < 2 ^ x_root c) by (apply pow2_pos_z; lia).
  assert (HpL : 0 < 2 ^ (s_len st - x_root c)) by (apply pow2_pos_z; lia).
  assert (Hb : 0 <= s_huff st / 2 ^ x_root c < 2 ^ (s_len st - x_root c)).
  { split; [apply Z.div_pos; lia|].
    apply Z.div_lt_upper_bound; [lia|]. rewrite <- Z.pow_add_r by lia.
    replace (x_root c + (s_len st - x_root c)) with (s_len st) by lia. lia. }
  assert (Hsplit : Pos (it_mass 15%nat 1 cnt0) st
                   = ustart (x_root c) (s_low st)
                     + zrev (Z.to_nat (s_len st - x_root c)) (s_huff st / 2 ^ x_root c) * 2 ^ (15 - s_len st)).
  { rewrite Hpos, Hlow. apply pos_split; lia. }
  split; [exact Hsplit | split; [exact Hb |]].
  pose proof (zrev_nonneg (Z.to_nat (s_len st - x_root c)) (s_huff st / 2 ^ x_root c)) as Hz0.
  pose proof (zrev_lt (Z.to_nat (s_len st - x_root c)) (s_huff st / 2 ^ x_root c)) as Hz1.
  rewrite (to_nat_pow (s_len st - x_root c) ltac:(lia)) in Hz1.
  assert (Hp15 : 0 < 2 ^ (15 - s_len st)) by (apply pow2_pos_z; lia).
  assert (Hpow : 2 ^ (s_len st - x_root c) * 2 ^ (15 - s_len st) = 2 ^ (15 - x_root c))
    by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  split; [nia | nia].
Qed.

(** (a) the fill never writes below next *)
Lemma after_fill_a : forall c cnt0 st, CovCtxOk c cnt0 -> CovInv c cnt0 st -> SubSt c cnt0 st ->
  forall j, j < s_next st -> FILL c st j = s_tbl st j.
Proof.
  intros c cnt0 st Hctx Hinv Hsub j Hj.
  pose proof Hctx as Hctx2. pose proof Hinv as Hinv2. sub_intro Hctx Hinv.
  destruct (Z.le_gt_cases (s_len st) (x_root c)) as [Hle|Hgt].
  - rewrite (fill_phase1 c cnt0 st Hctx2 Hinv2 Hle).
    destruct Hphase as [(Hd & Hc & Hnx & Hlow & Hlr) | (Hd & Hrl & _)]; [| exfalso; lia].
    apply fill_miss_below; [apply pow2_pos_z; lia | lia].
  - rewrite (fill_phase2 c cnt0 st Hctx2 Hinv2 Hsub Hgt).
    apply fill_miss_below; [apply pow2_pos_z; lia |].
    assert (0 <= s_huff st / 2 ^ x_root c) by (apply Z.div_pos; [lia | apply pow2_pos_z; lia]). lia.
Qed.

(** (b) units done BEFORE the fill keep their pointer status *)
Lemma after_fill_b : forall c cnt0 st, CovCtxOk c cnt0 -> CovInv c cnt0 st -> SubSt c cnt0 st ->
  DonePtrs (x_root c) (s_next st) (FILL c st) (Pos (it_mass 15%nat 1 cnt0) st).
Proof.
  intros c cnt0 st Hctx Hinv Hsub i Hi Hu.
  pose proof Hctx as Hctx2. pose proof Hinv as Hinv2.
  pose proof (after_fill_a c cnt0 st Hctx Hinv Hsub) as Ha.
  destruct Hsub as (Hdone & _ & _). pose proof (Hdone i Hi Hu) as Hp.
  sub_intro Hctx Hinv.
  destruct (Z.le_gt_cases (s_len st) (x_root c)) as [Hle|Hgt].
  - (* phase 1: the done index is outside huff's class *)
    destruct Hphase as [(Hd & Hc & Hnx & Hlow & Hlr) | (Hd & Hrl & _)]; [| exfalso; lia].
    assert (Hne : i mod 2 ^ s_len st <> s_huff st).
    { intro E.
      destruct (class_window_z (x_root c) (s_len st) (s_huff st) i ltac:(lia) ltac:(lia) Hhuff Hi E)
        as [Hnd _].
      apply Hnd. rewrite <- Hpos. exact Hu. }
    apply (ptrok_ext (x_root c) (s_next st) (s_next st) (s_tbl st) (FILL c st) i); [lia | | | exact Hp].
    + rewrite (fill_phase1 c cnt0 st Hctx2 Hinv2 Hle). symmetry. apply fill_class_miss; [lia | exact Hhuff | exact Hne].
    + intros j Hj. rewrite Hnx in Hj. pose proof (pow2_pos_z (x_root c) ltac:(lia)). lia.
  - apply (ptrok_ext (x_root c) (s_next st) (s_next st) (s_tbl st) (FILL c st) i); [lia | | | exact Hp].
    + destruct Hphase as [(Hd & Hc & Hnx & Hlow & Hlr) | (Hd & Hrl & Hnx & Hlow & Hlb)]; [exfalso; lia|].
      symmetry. apply Ha. lia.
    + intros j Hj. symmetry. apply Ha. lia.
Qed.

(** (c) phase 1: a unit completed by the fill carries the leaf just written *)
Lemma after_fill_c : forall c cnt0 st, CovCtxOk c cnt0 -> CovInv c cnt0 st -> CtxLeafOk c ->
  s_len st <= x_root c ->
  forall i, 0 <= i < 2 ^ x_root c ->
    UnitDone (x_root c) i (Pos (it_mass 15%nat 1 cnt0) st + 2 ^ (15 - s_len st)) ->
    ~ UnitDone (x_root c) i (Pos (it_mass 15%nat 1 cnt0) st) -> LeafOp (FILL c st i).
Proof.
  intros c cnt0 st Hctx Hinv Hleaf Hle i Hi Hu1 Hu0.
  pose proof Hctx as Hctx2. pose proof Hinv as Hinv2. sub_intro Hctx Hinv.
  rewrite (fill_phase1 c cnt0 st Hctx2 Hinv2 Hle).
  assert (Hcls : i mod 2 ^ s_len st = s_huff st).
  { apply (unit_cross_short_z (x_root c) (s_len st) (s_huff st) i); try lia; try exact Hhuff; try exact Hi.
    - unfold UnitDone in Hu0. rewrite Hpos in Hu0. lia.
    - unfold UnitDone in Hu1. rewrite Hpos in Hu1. lia. }
  rewrite fill_class_hit by (try lia; try exact Hhuff; try exact Hi; exact Hcls).
  apply it_here_leaf. exact Hleaf.
Qed.

(** (d) phase 2: the current sub-table's class/coverage clauses advance by one code *)
Lemma after_fill_d : forall c cnt0 st, CovCtxOk c cnt0 -> CovInv c cnt0 st -> SubSt c cnt0 st ->
  x_root c < s_len st ->
  ClassDone (s_curr st) (view (FILL c st) (s_next st))
    ((Pos (it_mass 15%nat 1 cnt0) st + 2 ^ (15 - s_len st) - ustart (x_root c) (s_low st)) * 2 ^ x_root c)
  /\ CovBelow (s_curr st) (view (FILL c st) (s_next st))
    ((Pos (it_mass 15%nat 1 cnt0) st + 2 ^ (15 - s_len st) - ustart (x_root c) (s_low st)) * 2 ^ x_root c).
Proof.
  intros c cnt0 st Hctx Hinv Hsub Hrl.
  pose proof Hctx as Hctx2. pose proof Hinv as Hinv2.
  pose proof (sub_len_le_curr c cnt0 st Hctx Hinv Hsub Hrl) as Hlc.
  pose proof (fill_phase2 c cnt0 st Hctx Hinv Hsub Hrl) as HF.
  destruct (sub_pos_facts c cnt0 st Hctx Hinv Hrl) as (Hsplit & Hb & Hlo & Hhi).
  destruct Hsub as (Hdone & Hused & [(Hlr & _) | (_ & Hop & Hval & Hc1 & Hcm & Hcd & Hcb & Hsz & Hub)]);
    [exfalso; lia|].
  sub_intro Hctx Hinv.
  destruct Hphase as [(Hd & Hc & Hnx & Hlow & Hlr) | (Hd & _ & Hnx & Hlow & Hlb)]; [exfalso; lia|].
  assert (Hbits : c_bits (it_here c st) = s_len st - x_root c)
    by (rewrite bits_here_val by lia; lia).
  assert (Hpow : 2 ^ (15 - s_len st) * 2 ^ x_root c = 2 ^ (15 - (s_len st - x_root c)))
    by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  assert (HQ : (Pos (it_mass 15%nat 1 cnt0) st - ustart (x_root c) (s_low st)) * 2 ^ x_root c
               = zrev (Z.to_nat (s_len st - x_root c)) (s_huff st / 2 ^ x_root c)
                 * 2 ^ (15 - (s_len st - x_root c))).
  { rewrite Hsplit. rewrite <- Hpow. ring. }
  assert (HQ1 : (Pos (it_mass 15%nat 1 cnt0) st + 2 ^ (15 - s_len st) - ustart (x_root c) (s_low st))
                * 2 ^ x_root c
                = (Pos (it_mass 15%nat 1 cnt0) st - ustart (x_root c) (s_low st)) * 2 ^ x_root c
                  + 2 ^ (15 - (s_len st - x_root c))).
  { rewrite <- Hpow. ring. }
  rewrite HQ1.
  split.
  - pose proof (classdone_fill_short (s_curr st) (s_len st - x_root c) (s_huff st / 2 ^ x_root c)
                  (view (s_tbl st) (s_next st)) (it_here c st)
                  ((Pos (it_mass 15%nat 1 cnt0) st - ustart (x_root c) (s_low st)) * 2 ^ x_root c)
                  ltac:(lia) ltac:(lia) Hb Hbits HQ Hcd) as Hcd'.
    eapply classdone_ext; [| exact Hcd'].
    intros j. rewrite HF. symmetry. apply view_fill.
  - rewrite HQ in Hcb.
    pose proof (cov_step_short (s_curr st) (s_len st - x_root c) (s_huff st / 2 ^ x_root c)
                  (view (s_tbl st) (s_next st)) (it_here c st)
                  ltac:(lia) ltac:(lia) Hb ltac:(lia) Hcb) as Hcb'.
    rewrite <- Z.pow_sub_r in Hcb' by lia.
    rewrite <- HQ in Hcb'.
    eapply covbelow_ext; [| exact Hcb'].
    intros j. rewrite HF. symmetry. apply view_fill.
Qed.

(** (e) phase 2: a unit completed by the fill is the current one, completed exactly *)
Lemma after_fill_e : forall c cnt0 st, CovCtxOk c cnt0 -> CovInv c cnt0 st ->
  x_root c < s_len st ->
  forall i, 0 <= i < 2 ^ x_root c ->
    UnitDone (x_root c) i (Pos (it_mass 15%nat 1 cnt0) st + 2 ^ (15 - s_len st)) ->
    ~ UnitDone (x_root c) i (Pos (it_mass 15%nat 1 cnt0) st) ->
    i = s_low st
    /\ Pos (it_mass 15%nat 1 cnt0) st + 2 ^ (15 - s_len st)
       = ustart (x_root c) (s_low st) + 2 ^ (15 - x_root c).
Proof.
  intros c cnt0 st Hctx Hinv Hrl i Hi Hu1 Hu0.
  destruct (sub_pos_facts c cnt0 st Hctx Hinv Hrl) as (Hsplit & Hb & Hlo & Hhi).
  sub_intro Hctx Hinv.
  destruct Hphase as [(Hd & Hc & Hnx & Hlow & Hlr) | (Hd & _ & Hnx & Hlow & Hlb)]; [exfalso; lia|].
  assert (Hil : i = s_low st).
  { rewrite Hlow.
    apply (unit_cross_long_z (x_root c) (s_len st) (s_huff st) i); try lia; try exact Hhuff; try exact Hi.
    - unfold UnitDone in Hu0. rewrite Hpos in Hu0. lia.
    - unfold UnitDone in Hu1. rewrite Hpos in Hu1. lia. }
  split; [exact Hil|].
  unfold UnitDone in Hu1. rewrite Hil in Hu1. unfold ustart in *. lia.
Qed.

(** the pointer of a sub-table that the fill has just completed *)
Lemma sub_completed_ptr : forall c cnt0 st, CovCtxOk c cnt0 -> CovInv c cnt0 st -> SubSt c cnt0 st ->
  x_root c < s_len st ->
  Pos (it_mass 15%nat 1 cnt0) st + 2 ^ (15 - s_len st) = ustart (x_root c) (s_low st) + 2 ^ (15 - x_root c) ->
  PtrOk (x_root c) (s_next st + 2 ^ s_curr st) (FILL c st) (s_low st).
Proof.
  intros c cnt0 st Hctx Hinv Hsub Hrl Hfull.
  pose proof (after_fill_a c cnt0 st Hctx Hinv Hsub) as Ha.
  destruct (after_fill_d c cnt0 st Hctx Hinv Hsub Hrl) as [Hcd Hcb].
  destruct Hsub as (Hdone & Hused & [(Hlr & _) | (_ & Hop & Hval & Hc1 & Hcm & Hcd0 & Hcb0 & Hsz & Hub)]);
    [exfalso; lia|].
  sub_intro Hctx Hinv.
  destruct Hphase as [(Hd & Hc & Hnx & Hlow & Hlr) | (Hd & _ & Hnx & Hlow & Hlb)]; [exfalso; lia|].
  assert (Hlowr : 0 <= s_low st < 2 ^ x_root c) by (rewrite Hlow; apply Z.mod_pos_bound, pow2_pos_z; lia).
  assert (Hkeep : FILL c st (s_low st) = s_tbl st (s_low st)) by (apply Ha; lia).
  assert (H15 : (Pos (it_mass 15%nat 1 cnt0) st + 2 ^ (15 - s_len st) - ustart (x_root c) (s_low st))
                * 2 ^ x_root c = 2 ^ 15).
  { rewrite Hfull. replace (ustart (x_root c) (s_low st) + 2 ^ (15 - x_root c) - ustart (x_root c) (s_low st))
      with (2 ^ (15 - x_root c)) by ring.
    rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  rewrite H15 in Hcd, Hcb.
  assert (Hposv : forall j, 0 <= j < 2 ^ s_curr st -> 1 <= c_bits (view (FILL c st) (s_next st) j)).
  { intros j Hj. pose proof (Hcb j Hj (unit_done_at_full (s_curr st) j ltac:(lia))). lia. }
  right. rewrite Hkeep, Hop, Hval.
  split; [lia | split; [lia | split; [lia | split]]].
  - apply root_repl_gives_prefixdet; [exact Hposv|].
    apply (repl_at_full (s_curr st)); [lia|]. apply classdone_repl. exact Hcd.
  - intros j Hj. exact (Hposv j Hj).
Qed.

(* ######################################################################### *)
(* S8.  The trip, the exit, the loop, the prologue                              *)
(* ######################################################################### *)

Lemma sub_step_cont : forall c cnt0 st st',
  CovCtxOk c cnt0 -> CovInv c cnt0 st -> CtxLeafOk c -> SubSt c cnt0 st ->
  it_step c st = ItCont st' -> SubSt c cnt0 st'.
Proof.
  intros c cnt0 st st' Hctx Hinv Hleaf Hsub Hstep.
  pose proof (cov_step_cont c cnt0 st st' Hctx Hinv Hstep) as Hinv'.
  pose proof (cont_fields c st st' Hstep) as (Hh1 & Hcnt1 & Hbr).
  pose proof (after_fill_a c cnt0 st Hctx Hinv Hsub) as Ha.
  pose proof (after_fill_b c cnt0 st Hctx Hinv Hsub) as Hb.
  pose proof (after_fill_c c cnt0 st Hctx Hinv Hleaf) as Hc.
  pose proof (after_fill_d c cnt0 st Hctx Hinv Hsub) as Hd.
  pose proof (after_fill_e c cnt0 st Hctx Hinv) as He.
  pose proof (sub_completed_ptr c cnt0 st Hctx Hinv Hsub) as Hcp.
  pose proof (sub_len_le_curr c cnt0 st Hctx Hinv Hsub) as Hlc.
  pose proof (fun Hrl => sub_pos_facts c cnt0 st Hctx Hinv Hrl) as Hpf.
  pose proof Hctx as Hctx2. pose proof Hinv as Hinv2. pose proof Hinv' as Hinv2'.
  destruct Hsub as (Hdone & Hused & Hph).
  sub_intro Hctx Hinv.
  destruct Hinv' as (Hlen' & Hhuff' & HwinL' & HwinU' & Hcnt' & Hpos' & Hcov' & Hphase').
  assert (Hpos1 : Pos (it_mass 15%nat 1 cnt0) st' = Pos (it_mass 15%nat 1 cnt0) st + 2 ^ (15 - s_len st))
    by (apply (step_pos_advance_cont _ c st st'); [lia | exact Hstep]).
  assert (HpR : 0 < 2 ^ x_root c) by (apply pow2_pos_z; lia).
  assert (Hk : 0 < 2 ^ (15 - x_root c)) by (apply pow2_pos_z; lia).
  assert (Hp15 : 0 < 2 ^ (15 - s_len st)) by (apply pow2_pos_z; lia).
  (* the length never decreases across a trip *)
  assert (Hlenmono : s_len st <= s_len st').
  { destruct (Z.le_gt_cases (s_len st) (s_len st')) as [H|H]; [exact H | exfalso].
    pose proof (Hcnt' (s_len st') ltac:(lia)) as Hc'. rewrite Hcnt1 in Hc'.
    rewrite Z.ltb_irrefl, Z.eqb_refl in Hc'.
    unfold zset in Hc'. destruct (Z.eqb_spec (s_len st') (s_len st)) as [E|E]; [lia|].
    rewrite (Hcnt (s_len st') ltac:(lia)) in Hc'.
    destruct (Z.ltb_spec (s_len st') (s_len st)) as [H1|H1]; lia. }
  assert (Hlowmod : Z.land (s_huff st') (x_mask c) = s_huff st' mod 2 ^ x_root c).
  { rewrite Hmask. apply land_ones_mod. lia. }
  assert (Hmodr : 0 <= s_huff st' mod 2 ^ x_root c < 2 ^ x_root c) by (apply Z.mod_pos_bound; lia).
  assert (Hcurr0 : 0 <= s_curr st).
  { destruct Hph as [(Hlr & _) | (_ & _ & _ & Hc1 & _)]; [| lia].
    destruct Hphase as [(_ & Hcq & _) | (_ & Hrl & _)]; lia. }
  assert (Hlowr : x_root c < s_len st -> 0 <= s_low st < 2 ^ x_root c).
  { intros Hrl. destruct Hphase as [(_ & _ & _ & _ & Hlr) | (_ & _ & _ & Hlow & _)]; [lia|].
    rewrite Hlow. apply Z.mod_pos_bound. lia. }
  destruct Hbr as [(Htbl & Hnx' & Hcu' & Hdr' & Hlo' & Hus' & Hcond)
                  | (curr' & Htbl & Hnx' & Hcu' & Hdr' & Hlo' & Hus' & Hrl' & Hdiff & Hcurr')].
  - (* ===== NO SUB-TABLE CREATED ===== *)
    unfold SubSt. rewrite Htbl, Hnx', Hcu', Hlo', Hus'.
    destruct (Z.le_gt_cases (s_len st') (x_root c)) as [Hle'|Hgt'].
    + (* still phase 1 *)
      assert (Hle : s_len st <= x_root c) by lia.
      destruct Hph as [(_ & Hu2R) | (Hrl & _)]; [| exfalso; lia].
      split; [| split; [exact Hused | left; split; [exact Hle' | exact Hu2R]]].
      intros i Hi Hu. rewrite Hpos1 in Hu.
      destruct (Z.le_gt_cases ((zrev (Z.to_nat (x_root c)) i + 1) * 2 ^ (15 - x_root c))
                  (Pos (it_mass 15%nat 1 cnt0) st)) as [Hold|Hnew].
      * exact (Hb i Hi Hold).
      * left. apply (Hc Hle i Hi Hu). unfold UnitDone. lia.
    + (* phase 2 at st', hence at st *)
      assert (Hrl : x_root c < s_len st).
      { destruct (Z.le_gt_cases (s_len st) (x_root c)) as [Hle|Hgt]; [exfalso | exact Hgt].
        destruct Hphase as [(Hd0 & Hcq & Hnx & Hlow & Hlr) | (Hd0 & Hrl & _)]; [| lia].
        destruct Hcond as [Hcond|Hcond]; [lia|].
        rewrite Hlowmod, Hlow in Hcond.
        assert (2 ^ x_root c <= 2 ^ 15) by (apply Z.pow_le_mono_r; lia). lia. }
      destruct Hph as [(Hlr & _) | (_ & Hop & Hval & Hc1 & Hcm & Hcd & Hcb & Hsz & Hub)]; [exfalso; lia|].
      destruct Hcond as [Hcond|Hcond]; [exfalso; lia|].
      destruct (Hd Hrl) as [Hcd' Hcb'].
      specialize (Hlc Hrl). specialize (Hlowr Hrl).
      (* the same prefix: the new position is still inside the unit of low *)
      assert (Hin' : Pos (it_mass 15%nat 1 cnt0) st + 2 ^ (15 - s_len st)
                     < ustart (x_root c) (s_low st) + 2 ^ (15 - x_root c)).
      { rewrite <- Hpos1, Hpos'. unfold ustart. rewrite <- Hcond, Hlowmod.
        pose proof (pos_in_root_unit_z (x_root c) (s_len st') (s_huff st') ltac:(lia) ltac:(lia) Hhuff') as Hpu.
        lia. }
      split; [| split; [exact Hused | right]].
      * intros i Hi Hu. rewrite Hpos1 in Hu.
        destruct (Z.le_gt_cases ((zrev (Z.to_nat (x_root c)) i + 1) * 2 ^ (15 - x_root c))
                    (Pos (it_mass 15%nat 1 cnt0) st)) as [Hold|Hnew].
        -- exact (Hb i Hi Hold).
        -- exfalso. destruct (He Hrl i Hi Hu ltac:(unfold UnitDone; lia)) as [_ Hfull]. lia.
      * assert (Hkeep : FILL c st (s_low st) = s_tbl st (s_low st)).
        { apply Ha. destruct Hphase as [(_ & _ & _ & _ & Hlr) | (_ & _ & Hnx & _)]; lia. }
        rewrite Hkeep, Hpos1.
        split; [exact Hgt' | split; [exact Hop | split; [exact Hval | split; [exact Hc1 | split; [exact Hcm |]]]]].
        split; [exact Hcd' | split; [exact Hcb' | split; [| exact Hub]]].
        rewrite Hcnt1, pmass_dec by lia. lia.
  - (* ===== A SUB-TABLE IS CREATED ===== *)
    assert (Hdrop' : s_drop st' = x_root c).
    { rewrite Hdr'. destruct Hphase as [(Hd0 & _) | (Hd0 & _)]; rewrite Hd0; [reflexivity |].
      replace (Z.eqb (x_root c) 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
    rewrite Hdrop' in Hcurr'.
    assert (Hlenmx : s_len st' <= x_max c).
    { destruct (Z.le_gt_cases (s_len st') (x_max c)) as [H|H]; [exact H | exfalso].
      rewrite (Hmxz (s_len st') ltac:(lia)) in HwinU'. lia. }
    assert (Hz' : forall l, 1 <= l < s_len st' -> s_count st' l = 0).
    { intros l Hl. rewrite (Hcnt' l ltac:(lia)).
      destruct (Z.ltb_spec l (s_len st')) as [H|H]; [reflexivity | lia]. }
    assert (Hcnt'nn : forall l, 1 <= l <= 15 -> 0 <= s_count st' l).
    { intros l Hl. rewrite (Hcnt' l Hl).
      destruct (Z.ltb l (s_len st')); [lia|].
      destruct (Z.eqb_spec l (s_len st')); [lia | apply Hnn; lia]. }
    assert (Hcnt'above : forall l, x_max c < l <= 15 -> s_count st' l = 0).
    { intros l Hl. rewrite (Hcnt' l ltac:(lia)).
      destruct (Z.ltb_spec l (s_len st')) as [H|H]; [lia|].
      destruct (Z.eqb_spec l (s_len st')) as [E|E]; [lia | apply Hmxz; lia]. }
    (* the it_subsz sizing *)
    assert (Hsz' : SubszOk (x_root c) (x_max c) (s_count st') (s_len st' - x_root c) curr').
    { rewrite Hcurr'. apply subsz_spec; [lia | lia | lia | lia | change (Z.of_nat 16) with 16; lia |].
      rewrite shiftl1 by lia.
      replace (s_len st' - x_root c + x_root c - 1) with (s_len st' - 1) by lia.
      rewrite (pmass_zero_on (s_len st' - 1) (s_count st') ltac:(lia) ltac:(intros l Hl; apply Hz'; lia)).
      rewrite Z.sub_0_r, <- Z.pow_add_r by lia. f_equal. lia. }
    destruct Hsz' as (Hcge & Hcmx & Hcase').
    assert (Hlow'r : 0 <= s_low st' < 2 ^ x_root c) by (rewrite Hlo', Hlowmod; exact Hmodr).
    destruct (sub_pos_facts c cnt0 st' Hctx2 Hinv2' Hrl') as (Hsplit' & Hb' & Hlo1 & Hhi1).
    assert (Hup1 : Pos (it_mass 15%nat 1 cnt0) st' < ustart (x_root c) (s_low st') + 2 ^ (15 - x_root c))
      by (pose proof (pow2_pos_z (15 - s_len st') ltac:(lia)); lia).
    (* P1 is a multiple of 2^(15-R); in phase 2 it is exactly the end of the old unit *)
    assert (HP1eq : x_root c < s_len st ->
              Pos (it_mass 15%nat 1 cnt0) st' = ustart (x_root c) (s_low st) + 2 ^ (15 - x_root c)).
    { intros Hrl. specialize (Hlowr Hrl).
      destruct (Hpf Hrl) as (Hsplit & Hb0 & Hlo0 & Hhi0).
      rewrite Hpos1.
      destruct (Z.eq_dec (Pos (it_mass 15%nat 1 cnt0) st + 2 ^ (15 - s_len st))
                  (ustart (x_root c) (s_low st) + 2 ^ (15 - x_root c))) as [E|E]; [exact E | exfalso].
      (* then P1 lies in the unit of low AND in the unit of low' with low <> low' *)
      assert (Hzl : zrev (Z.to_nat (x_root c)) (s_low st) = zrev (Z.to_nat (x_root c)) (s_low st')).
      { unfold ustart in *. rewrite Hpos1 in Hlo1, Hup1.
        apply Z.le_antisymm.
        - apply Z.lt_succ_r. apply (mul_lt_cancel_r _ _ _ Hk). rewrite Z.mul_succ_l. lia.
        - apply Z.lt_succ_r. apply (mul_lt_cancel_r _ _ _ Hk). rewrite Z.mul_succ_l. lia. }
      apply zrev_inj in Hzl; try (rewrite (to_nat_pow (x_root c) ltac:(lia)); lia).
      rewrite Hlo' in Hzl. apply Hdiff. symmetry. exact Hzl. }
    assert (HP1U' : Pos (it_mass 15%nat 1 cnt0) st' = ustart (x_root c) (s_low st')).
    { assert (HP1mult : exists q, Pos (it_mass 15%nat 1 cnt0) st' = q * 2 ^ (15 - x_root c)).
      { destruct (Z.le_gt_cases (s_len st) (x_root c)) as [Hle|Hgt].
        - rewrite Hpos1, Hpos.
          exists (zrev (Z.to_nat (s_len st)) (s_huff st) * 2 ^ (x_root c - s_len st)
                  + 2 ^ (x_root c - s_len st)).
          assert (Hpw : 2 ^ (x_root c - s_len st) * 2 ^ (15 - x_root c) = 2 ^ (15 - s_len st))
            by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
          rewrite <- Hpw. ring.
        - rewrite (HP1eq Hgt). unfold ustart. exists (zrev (Z.to_nat (x_root c)) (s_low st) + 1). ring. }
      destruct HP1mult as [q Hq]. unfold ustart in *.
      assert (Hzq : zrev (Z.to_nat (x_root c)) (s_low st') = q).
      { apply Z.le_antisymm.
        - apply Z.lt_succ_r. apply (mul_lt_cancel_r _ _ _ Hk). rewrite Z.mul_succ_l. lia.
        - apply Z.lt_succ_r. apply (mul_lt_cancel_r _ _ _ Hk). rewrite Z.mul_succ_l. lia. }
      rewrite Hzq. exact Hq. }
    (* in phase 2 the new unit is the successor of the old one *)
    assert (Hzsucc : x_root c < s_len st ->
              zrev (Z.to_nat (x_root c)) (s_low st') = zrev (Z.to_nat (x_root c)) (s_low st) + 1).
    { intros Hrl. pose proof (HP1eq Hrl) as E. rewrite HP1U' in E. unfold ustart in E.
      apply (Z.mul_cancel_r _ _ (2 ^ (15 - x_root c))); [lia |]. rewrite Z.mul_add_distr_r. lia. }
    (* the new pointer *)
    assert (Hnext'eq : s_next st + Z.shiftl 1 (s_curr st) = s_next st + 2 ^ s_curr st)
      by (rewrite shiftl1 by lia; reflexivity).
    assert (Hpow15 : 2 ^ x_root c * 2 ^ (15 - x_root c) = 2 ^ 15)
      by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
    assert (HpowM : 2 ^ x_root c * 2 ^ (x_max c - x_root c) = 2 ^ x_max c)
      by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
    assert (HpM15 : 2 ^ x_max c <= 2 ^ 15) by (apply Z.pow_le_mono_r; lia).
    assert (HpR15 : 2 ^ x_root c <= 2 ^ 15) by (apply Z.pow_le_mono_r; lia).
    assert (HpMR : 0 < 2 ^ (x_max c - x_root c)) by (apply pow2_pos_z; lia).
    assert (Hzlt' : zrev (Z.to_nat (x_root c)) (s_low st') < 2 ^ x_root c).
    { pose proof (zrev_lt (Z.to_nat (x_root c)) (s_low st')) as H.
      rewrite (to_nat_pow (x_root c) ltac:(lia)) in H. exact H. }
    assert (Hz0' : 0 <= zrev (Z.to_nat (x_root c)) (s_low st')) by apply zrev_nonneg.
    assert (Hnext'bound : 0 <= s_next st + 2 ^ s_curr st < 65536).
    { rewrite Hused.
      destruct Hph as [(Hlr & Hu2R) | (Hrl & _ & _ & _ & _ & _ & _ & _ & Hub)].
      - rewrite Hu2R. change (2 ^ 15) with 32768 in HpR15. lia.
      - pose proof (Hzsucc Hrl) as Hs. change (2 ^ 15) with 32768 in HpM15, HpR15.
        pose proof (zrev_nonneg (Z.to_nat (x_root c)) (s_low st)) as Hz0.
        destruct Hphase as [(_ & _ & _ & _ & Hlr) | (_ & _ & Hnx & _)]; [lia |].
        rewrite <- Hs in Hub.
        assert (Hprod : zrev (Z.to_nat (x_root c)) (s_low st') * 2 ^ (x_max c - x_root c)
                        + 2 ^ (x_max c - x_root c) <= 2 ^ x_root c * 2 ^ (x_max c - x_root c)).
        { replace (zrev (Z.to_nat (x_root c)) (s_low st') * 2 ^ (x_max c - x_root c) + 2 ^ (x_max c - x_root c))
            with ((zrev (Z.to_nat (x_root c)) (s_low st') + 1) * 2 ^ (x_max c - x_root c)) by ring.
          apply Z.mul_le_mono_nonneg_r; lia. }
        rewrite HpowM in Hprod. pose proof (pow2_pos_z (s_curr st) Hcurr0) as Hpc.
        clear - Hub Hprod HpM15 HpR15 HpMR Hused Hnx HpR Hpc. lia. }
    assert (Hcurr1 : 1 <= curr' <= 14) by lia.
    assert (He_op : c_op (mkCodeT curr' (x_root c) (s_next st + 2 ^ s_curr st)) = curr')
      by (unfold mkCodeT; cbn [c_op]; apply u8_id; lia).
    assert (He_val : c_val (mkCodeT curr' (x_root c) (s_next st + 2 ^ s_curr st))
                     = s_next st + 2 ^ s_curr st)
      by (unfold mkCodeT; cbn [c_val]; apply u16_id; lia).
    (* low' is not done at P1 *)
    assert (Hnotdone : ~ UnitDone (x_root c) (s_low st') (Pos (it_mass 15%nat 1 cnt0) st')).
    { unfold UnitDone. rewrite HP1U'. unfold ustart. lia. }
    unfold SubSt. rewrite Htbl, Hnx', Hcu', Hus', Hnext'eq.
    split; [| split; [| right]].
    + (* DonePtrs *)
      intros i Hi Hu.
      assert (Hne : i <> s_low st') by (intro E; subst i; exact (Hnotdone Hu)).
      rewrite Hpos1 in Hu.
      destruct (Z.le_gt_cases ((zrev (Z.to_nat (x_root c)) i + 1) * 2 ^ (15 - x_root c))
                  (Pos (it_mass 15%nat 1 cnt0) st)) as [Hold|Hnew].
      * apply (ptrok_ext (x_root c) (s_next st) (s_next st + 2 ^ s_curr st) (FILL c st) _ i);
          [pose proof (pow2_pos_z (s_curr st) Hcurr0); lia | | | exact (Hb i Hi Hold)].
        -- symmetry. apply tset_other. exact Hne.
        -- intros j Hj. symmetry. apply tset_other. lia.
      * destruct (Z.le_gt_cases (s_len st) (x_root c)) as [Hle|Hgt].
        -- left. rewrite tset_other by exact Hne. apply (Hc Hle i Hi Hu). unfold UnitDone. lia.
        -- destruct (He Hgt i Hi Hu ltac:(unfold UnitDone; lia)) as [Hil Hfull]. subst i.
           apply (ptrok_ext (x_root c) (s_next st + 2 ^ s_curr st) (s_next st + 2 ^ s_curr st)
                    (FILL c st) _ (s_low st)); [lia | | | exact (Hcp Hgt Hfull)].
           ++ symmetry. apply tset_other. exact Hne.
           ++ intros j Hj. symmetry. apply tset_other. lia.
    + rewrite shiftl1 by lia. lia.
    + (* the phase-2 clause of the new state *)
      rewrite tset_same, He_op, He_val, HP1U'.
      split; [exact Hrl' | split; [reflexivity | split; [reflexivity | split; [lia | split; [exact Hcmx |]]]]].
      rewrite Z.sub_diag, Z.mul_0_l.
      split; [apply classdone_zero; lia | split; [apply covbelow_zero; lia | split]].
      * (* sizing *)
        replace (ustart (x_root c) (s_low st') + 2 ^ (15 - x_root c) - ustart (x_root c) (s_low st'))
          with (2 ^ (15 - x_root c)) by ring.
        destruct Hcase' as [Hmxeq | Hbig]; [| exact Hbig].
        rewrite Hmxeq.
        rewrite <- (pmass_zero_above 15 (x_max c) (s_count st') ltac:(lia) ltac:(lia) Hcnt'above).
        rewrite pmass_15.
        (* the remaining mass is 2^15 - P1 = 2^15 - U' *)
        assert (Hrem : it_mass 15%nat 1 (s_count st') = it_mass 15%nat 1 cnt0 - Pos (it_mass 15%nat 1 cnt0) st')
          by (unfold Pos; ring).
        rewrite Hrem, HP1U'.
        destruct Hcase as [Hfull | [Hmx1 _]]; [| exfalso; lia].
        rewrite Hfull. unfold ustart.
        assert (Hle15 : (zrev (Z.to_nat (x_root c)) (s_low st') + 1) * 2 ^ (15 - x_root c)
                        <= 2 ^ x_root c * 2 ^ (15 - x_root c))
          by (apply Z.mul_le_mono_nonneg_r; lia).
        rewrite Hpow15, Z.mul_add_distr_r, Z.mul_1_l in Hle15.
        clear - Hle15. lia.
      * (* the used bound *)
        rewrite shiftl1 by lia.
        assert (Hc2 : 2 ^ curr' <= 2 ^ (x_max c - x_root c)) by (apply Z.pow_le_mono_r; lia).
        destruct Hph as [(Hlr & Hu2R) | (Hrl & _ & _ & _ & _ & _ & _ & _ & Hub)].
        -- rewrite Hu2R.
           pose proof (Z.mul_nonneg_nonneg (zrev (Z.to_nat (x_root c)) (s_low st'))
                         (2 ^ (x_max c - x_root c)) Hz0' ltac:(lia)) as Hnn0.
           rewrite Z.mul_add_distr_r, Z.mul_1_l. clear - Hc2 Hnn0. lia.
        -- rewrite (Hzsucc Hrl). rewrite !Z.mul_add_distr_r, !Z.mul_1_l in *. clear - Hub Hc2. lia.
Qed.

Lemma sub_step_break : forall c cnt0 st st1,
  CovCtxOk c cnt0 -> CovInv c cnt0 st -> CtxLeafOk c -> SubSt c cnt0 st ->
  it_step c st = ItBreak st1 -> SubPD (it_finish st1) (x_root c).
Proof.
  intros c cnt0 st st1 Hctx Hinv Hleaf Hsub Hstep.
  assert (Hr256 : 0 <= x_root c < 256) by (destruct Hctx as (Hr & _); lia).
  destruct (step_shape_break c st st1 Hr256 Hstep) as (Htbl & Hh1 & Hlen1 & Hdrop1 & Hnext1).
  assert (HtblF : s_tbl st1 = FILL c st) by exact Htbl. clear Htbl.
  pose proof (step_break_cond c st st1 Hstep) as [Hhit Hmxeq].
  pose proof (after_fill_a c cnt0 st Hctx Hinv Hsub) as Ha.
  pose proof (after_fill_b c cnt0 st Hctx Hinv Hsub) as Hb.
  pose proof (after_fill_c c cnt0 st Hctx Hinv Hleaf) as Hc.
  pose proof (after_fill_e c cnt0 st Hctx Hinv) as He.
  pose proof (sub_completed_ptr c cnt0 st Hctx Hinv Hsub) as Hcp.
  pose proof Hctx as Hctx2. pose proof Hinv as Hinv2.
  destruct Hsub as (Hdone & Hused & Hph).
  sub_intro Hctx Hinv.
  set (cnt1 := zset (s_count st) (s_len st) (s_count st (s_len st) - 1)) in *.
  assert (Hcnt1 : forall l, 1 <= l <= 15 -> cnt1 l = 0).
  { intros l Hl. unfold cnt1, zset.
    destruct (Z.eqb_spec l (s_len st)) as [->|Hne].
    - unfold cnt1, zset in Hhit. rewrite Z.eqb_refl in Hhit. exact Hhit.
    - rewrite (Hcnt l Hl).
      destruct (Z.ltb_spec l (s_len st)) as [H1|H1]; [reflexivity|].
      destruct (Z.eqb_spec l (s_len st)) as [H2|H2]; [contradiction|].
      apply Hmxz. lia. }
  assert (Hmass0 : it_mass 15%nat 1 cnt1 = 0)
    by (apply it_mass_zero_on; intros i Hi; apply Hcnt1; cbn in Hi; lia).
  assert (Hposbrk : Pos (it_mass 15%nat 1 cnt0) st + 2 ^ (15 - s_len st) = it_mass 15%nat 1 cnt0).
  { unfold Pos. rewrite <- (pos_advance (it_mass 15%nat 1 cnt0) (s_count st) (s_len st) ltac:(lia)).
    unfold cnt1 in Hmass0. rewrite Hmass0. ring. }
  assert (Hcurr0 : 0 <= s_curr st).
  { destruct Hph as [(Hlr & _) | (_ & _ & _ & Hc1 & _)]; [| lia].
    destruct Hphase as [(_ & Hcq & _) | (_ & Hrl & _)]; lia. }
  assert (Hpc : 0 < 2 ^ s_curr st) by (apply pow2_pos_z; lia).
  (* the entry at a done unit, after the fill *)
  assert (Hptr : forall i, 0 <= i < 2 ^ x_root c ->
            UnitDone (x_root c) i (Pos (it_mass 15%nat 1 cnt0) st + 2 ^ (15 - s_len st)) ->
            PtrOk (x_root c) (s_next st + 2 ^ s_curr st) (FILL c st) i).
  { intros i Hi Hu1.
    destruct (Z.le_gt_cases ((zrev (Z.to_nat (x_root c)) i + 1) * 2 ^ (15 - x_root c))
                (Pos (it_mass 15%nat 1 cnt0) st)) as [Hold|Hnew].
    - apply (ptrok_ext (x_root c) (s_next st) (s_next st + 2 ^ s_curr st) (FILL c st) (FILL c st) i);
        [lia | reflexivity | intros j _; reflexivity | exact (Hb i Hi Hold)].
    - destruct (Z.le_gt_cases (s_len st) (x_root c)) as [Hle|Hgt].
      + left. apply (Hc Hle i Hi Hu1). unfold UnitDone. lia.
      + destruct (He Hgt i Hi Hu1 ltac:(unfold UnitDone; lia)) as [Hil Hfull]. subst i.
        exact (Hcp Hgt Hfull). }
  assert (Hhuff'' : 0 <= s_huff st < 2 ^ Z.of_nat (Z.to_nat (s_len st)))
    by (rewrite (to_nat_pow (s_len st) ltac:(lia)); exact Hhuff).
  pose proof (zrev_it_rev_incr (Z.to_nat (s_len st)) (s_huff st) ltac:(lia) Hhuff'') as Hinc.
  rewrite (Z2Nat.id (s_len st)) in Hinc by lia.
  destruct Hcase as [Hfull | [Hmx1 Hhalf]].
  - (* COMPLETE: it_finish writes nothing *)
    assert (Hzfull : zrev (Z.to_nat (s_len st)) (s_huff st) = 2 ^ s_len st - 1).
    { assert (Hsplit : 2 ^ 15 = 2 ^ s_len st * 2 ^ (15 - s_len st))
        by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
      assert (Hp : 0 < 2 ^ (15 - s_len st)) by (apply pow2_pos_z; lia).
      rewrite Hpos, Hfull in Hposbrk.
      apply (Z.mul_cancel_r _ _ (2 ^ (15 - s_len st))); [lia|].
      rewrite Z.mul_sub_distr_r, Z.mul_1_l. clear - Hposbrk Hsplit. lia. }
    assert (Hh0 : it_rev_incr (s_huff st) (s_len st) = 0).
    { destruct Hinc as [[Hw _] | [_ Hgood]]; [exact Hw | exfalso].
      pose proof (zrev_lt (Z.to_nat (s_len st)) (it_rev_incr (s_huff st) (s_len st))) as Hlt.
      rewrite (to_nat_pow (s_len st) ltac:(lia)) in Hlt.
      rewrite Hzfull in Hgood. lia. }
    assert (Hfin : it_finish st1 = s_tbl st1).
    { unfold it_finish. rewrite Hh1, Hh0, Z.eqb_refl. reflexivity. }
    rewrite Hfin, HtblF.
    intros i Hi H240 Hnz.
    assert (Hu1 : UnitDone (x_root c) i (Pos (it_mass 15%nat 1 cnt0) st + 2 ^ (15 - s_len st)))
      by (rewrite Hposbrk, Hfull; apply unit_done_at_full; lia).
    destruct (Hptr i Hi Hu1) as [[Hz | Hl] | (Hop & Hlo & Hhi & HR & Hpos2)];
      [contradiction | contradiction |].
    split; [exact HR | exact Hpos2].
  - (* INCOMPLETE-BUT-ACCEPTED: max = 1, root = 1, the fix-up writes the second root entry *)
    assert (HR1 : x_root c = 1) by lia.
    assert (Hlen1' : s_len st = 1) by lia.
    destruct Hphase as [(Hd & Hcq & Hnx & Hlow & Hlr) | (Hd & Hrl & _)]; [| exfalso; lia].
    assert (Hhuff0 : s_huff st = 0).
    { rewrite Hpos, Hlen1' in Hposbrk. rewrite Hhalf in Hposbrk. change (15 - 1) with 14 in Hposbrk.
      assert (Hp : 0 < 2 ^ 14) by (apply pow2_pos_z; lia).
      assert (Hz : zrev (Z.to_nat 1) (s_huff st) = 0) by nia.
      rewrite Hlen1' in Hhuff. change (2 ^ 1) with 2 in Hhuff.
      assert (s_huff st = 0 \/ s_huff st = 1) as [H|H] by lia; [exact H | exfalso].
      rewrite H in Hz. vm_compute in Hz. discriminate Hz. }
    assert (Hh1v : s_huff st1 = 1) by (rewrite Hh1, Hhuff0, Hlen1'; reflexivity).
    assert (Hfin : it_finish st1
                   = tset (s_tbl st1) 1 (mkCodeT 64 (s_len st1 - s_drop st1) 0)).
    { unfold it_finish. rewrite Hh1v, Hnext1, Hnx. reflexivity. }
    rewrite Hfin, HtblF.
    intros i Hi H240 Hnz.
    rewrite HR1 in Hi. change (2 ^ 1) with 2 in Hi.
    destruct (Z.eq_dec i 1) as [-> | Hne].
    + exfalso. rewrite tset_same in H240. vm_compute in H240. discriminate H240.
    + assert (Hi0 : i = 0) by lia. subst i.
      rewrite tset_other in H240, Hnz |- * by lia.
      assert (Hu1 : UnitDone (x_root c) 0 (Pos (it_mass 15%nat 1 cnt0) st + 2 ^ (15 - s_len st))).
      { rewrite Hposbrk, Hhalf. unfold UnitDone. rewrite HR1.
        change (zrev (Z.to_nat 1) 0) with 0. lia. }
      destruct (Hptr 0 ltac:(lia) Hu1) as [[Hz | Hl] | (Hop & Hlo & Hhi & HR & Hpos2)];
        [contradiction | contradiction |].
      rewrite HR1 in Hlo. change (2 ^ 1) with 2 in Hlo.
      split.
      * apply (rootprefixdet_ext_on _ (view (FILL c st) (c_val (FILL c st 0)))); [| exact HR].
        intros j Hj. unfold view. symmetry. apply tset_other. lia.
      * intros j Hj. rewrite tset_other by lia. exact (Hpos2 j Hj).
Qed.

Lemma sub_loop : forall n c cnt0 st st1,
  CovCtxOk c cnt0 -> CovInv c cnt0 st -> CtxLeafOk c -> SubSt c cnt0 st ->
  it_loop n c st = Some (ItBreak st1) -> SubPD (it_finish st1) (x_root c).
Proof.
  induction n as [|k IH]; intros c cnt0 st st1 Hctx Hinv Hleaf Hsub Hloop;
    cbn [it_loop] in Hloop; [discriminate Hloop|].
  destruct (it_step c st) as [st'|st'|t] eqn:Hs.
  - apply (IH c cnt0 st' st1 Hctx (cov_step_cont c cnt0 st st' Hctx Hinv Hs) Hleaf
             (sub_step_cont c cnt0 st st' Hctx Hinv Hleaf Hsub Hs) Hloop).
  - injection Hloop as <-. apply (sub_step_break c cnt0 st _ Hctx Hinv Hleaf Hsub Hs).
  - discriminate Hloop.
Qed.

Lemma sub_pre : forall ty lens codes root0 t0 c st,
  0 <= codes -> (forall i, 0 <= i < codes -> 0 <= lens i <= 15) -> 1 <= root0 <= 15 ->
  it_pre ty lens codes root0 t0 = PreGo c st -> SubSt c (sw_cnt lens codes) st.
Proof.
  intros ty lens codes root0 t0 c st Hcodes Hlens Hroot0 Hpre.
  destruct (cov_pre ty lens codes root0 t0 c st Hcodes Hlens Hroot0 Hpre) as [Hctx Hinv].
  destruct (it_pre_go_ctx ty lens codes root0 t0 c st Hpre) as (_ & _ & _ & _ & _ & Hused & Hcurr & Hnext & Hdrop).
  destruct (it_pre_go_start ty lens codes root0 t0 c st Hpre) as [Hh Hnx].
  destruct Hctx as (Hroot & _).
  destruct Hinv as (Hlen & Hhuff & _ & _ & _ & Hpos & _ & Hphase).
  assert (Hp0 : Pos (it_mass 15%nat 1 (sw_cnt lens codes)) st = 0).
  { rewrite Hpos, Hh, zrev_zero. ring. }
  split; [| split].
  - intros i Hi Hu. exfalso. rewrite Hp0 in Hu. exact (unit_not_done_zero (x_root c) i ltac:(lia) Hu).
  - rewrite Hnext, Hcurr, Hused, shiftl1 by lia. ring.
  - left.
    destruct Hphase as [(_ & _ & _ & _ & Hlr) | (_ & _ & Hnx2 & _)].
    + split; [exact Hlr | rewrite Hused, shiftl1 by lia; reflexivity].
    + exfalso. rewrite Hnext in Hnx2. pose proof (pow2_pos_z (x_root c) ltac:(lia)). lia.
Qed.

(** THE SUB HALF: SubPD for every accepted inflate_table call under the it_wf type/codes premise *)
Theorem it_subpd_wf : forall ty lens codes root0 t0 out,
  0 <= codes -> (forall i, 0 <= i < codes -> 0 <= lens i <= 15) -> 1 <= root0 <= 15 ->
  ITWF ty codes -> it_model ty lens codes root0 t0 = Some out -> o_ret out = 0 ->
  SubPD (o_tbl out) (o_bits out).
Proof.
  intros ty lens codes root0 t0 out Hcodes Hlens Hroot0 Hwf Hmodel Hret.
  unfold it_model in Hmodel.
  destruct (it_pre ty lens codes root0 t0) as [ | temp | | c st] eqn:Hpre.
  - injection Hmodel as <-. cbn in Hret. lia.
  - rewrite (it_pre_empty_shape ty lens codes root0 t0 temp Hpre) in Hmodel.
    injection Hmodel as <-. cbn [o_tbl o_bits].
    intros i Hi H240 Hnz. exfalso. change (2 ^ 1) with 2 in Hi.
    assert (Hop : c_op (tset (tset t0 0 (mkCodeT 64 1 0)) 1 (mkCodeT 64 1 0) i) = 64).
    { destruct (Z.eq_dec i 1) as [->|H1]; [rewrite tset_same; reflexivity |].
      rewrite tset_other by lia. assert (Hi0 : i = 0) by lia. rewrite Hi0, tset_same. reflexivity. }
    rewrite Hop in H240. vm_compute in H240. discriminate H240.
  - injection Hmodel as <-. cbn in Hret. lia.
  - destruct (cov_pre ty lens codes root0 t0 c st Hcodes Hlens Hroot0 Hpre) as [Hctx Hinv].
    pose proof (sub_pre ty lens codes root0 t0 c st Hcodes Hlens Hroot0 Hpre) as Hsub.
    pose proof (ctx_leaf_of_wf ty lens codes root0 t0 c st Hcodes Hwf Hpre) as Hleaf.
    destruct (it_loop (S (Z.to_nat codes)) c st) as [[st'|st'|tt]|] eqn:Hloop;
      try discriminate Hmodel; injection Hmodel as <-; try (cbn in Hret; lia).
    cbn [o_tbl o_bits].
    apply (sub_loop (S (Z.to_nat codes)) c (sw_cnt lens codes) st st' Hctx Hinv Hleaf Hsub Hloop).
Qed.

(** TblPD of an it_model output under the it_wf type/codes premise, CLOSED (root half + sub half) *)
Theorem it_tblpd_wf : forall ty lens codes root0 t0 out,
  0 <= codes -> (forall i, 0 <= i < codes -> 0 <= lens i <= 15) -> 1 <= root0 <= 15 ->
  ITWF ty codes -> it_model ty lens codes root0 t0 = Some out -> o_ret out = 0 ->
  TblPD (o_tbl out) (o_bits out).
Proof.
  intros ty lens codes root0 t0 out Hcodes Hlens Hroot0 Hwf Hm Hret.
  destruct (it_tblpd_root ty lens codes root0 t0 out Hcodes Hlens Hroot0 Hm Hret) as (H0 & HR & Hw).
  split; [exact H0 | split; [exact HR | split; [exact Hw |]]].
  exact (it_subpd_wf ty lens codes root0 t0 out Hcodes Hlens Hroot0 Hwf Hm Hret).
Qed.
