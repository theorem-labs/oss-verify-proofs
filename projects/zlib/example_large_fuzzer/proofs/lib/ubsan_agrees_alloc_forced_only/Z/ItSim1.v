(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ModelRel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ItDefs.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ItGen.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ItMath.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition fill_list (here incr base : Z) (m : nat) : list (Z * Z) :=
  map (fun j => (base + Z.of_nat j * incr, here)) (List.rev (seq 0 m)).

Lemma fill_list_S : forall here incr base m,
  fill_list here incr base (S m) = (base + Z.of_nat m * incr, here) :: fill_list here incr base m.
Proof.
  intros. unfold fill_list. rewrite seq_S, List.rev_app_distr. cbn [List.rev map app Nat.add]. reflexivity.
Qed.

Definition fill_stepf (here incr huff drop next : Z) (ft : Z * arr) : bool * (Z * arr) :=
  let '(fill, tbl) := ft in
  let fill := wrap32 (fill - incr) in
  let tbl := arr_set tbl (next + (Z.shiftr huff drop + fill)) here in
  if negb (fill =? 0) then (true, (fill, tbl)) else (false, (fill, tbl)).

Lemma it_fill_unfold : forall here incr huff drop next fill tbl,
  it_fill here incr huff drop next fill tbl = snd (loopZ fill (fill_stepf here incr huff drop next) (fill, tbl)).
Proof. reflexivity. Qed.

Lemma fill_stepf_eq : forall here incr huff drop next fill t,
  fill_stepf here incr huff drop next (fill, t) =
  (negb (wrap32 (fill - incr) =? 0), (wrap32 (fill - incr), arr_set t (next + (Z.shiftr huff drop + wrap32 (fill - incr))) here)).
Proof. intros. unfold fill_stepf. destruct (negb (wrap32 (fill - incr) =? 0)); reflexivity. Qed.

Lemma it_fill_loop : forall here incr huff drop next (m : nat) fuel t,
  1 <= incr -> (1 <= m)%nat -> Z.of_nat m * incr < 4294967296 -> Z.of_nat m <= fuel ->
  loopZ fuel (fill_stepf here incr huff drop next) (Z.of_nat m * incr, t)
  = (0, applyw (fill_list here incr (next + Z.shiftr huff drop) m) t).
Proof.
  intros here incr huff drop next m. induction m as [|m IH]; intros fuel t Hincr Hm Hb Hf; [lia|].
  rewrite loopZ_step by lia. rewrite fill_stepf_eq.
  replace (Z.of_nat (S m) * incr - incr) with (Z.of_nat m * incr) by lia.
  rewrite (wrap32_small (Z.of_nat m * incr)) by nia.
  rewrite fill_list_S, applyw_cons.
  replace (next + (Z.shiftr huff drop + Z.of_nat m * incr)) with (next + Z.shiftr huff drop + Z.of_nat m * incr) by lia.
  destruct m as [|m'].
  - cbn [Z.of_nat]. rewrite Z.mul_0_l. cbn [Z.eqb negb]. rewrite Z.add_0_r. reflexivity.
  - destruct (Z.eqb_spec (Z.of_nat (S m') * incr) 0); [nia|]. cbn [negb].
    apply IH; lia.
Qed.

Lemma it_fill_eq : forall here l huff drop next c t,
  0 <= l <= c -> c <= 15 -> 0 <= drop ->
  it_fill here (2 ^ l) huff drop next (2 ^ c) t =
  applyw (fill_list here (2 ^ l) (next + huff / 2 ^ drop) (Z.to_nat (2 ^ (c - l)))) t.
Proof.
  intros here l huff drop next c t Hl Hc Hd. rewrite it_fill_unfold.
  pose proof (pow2_le_15 l ltac:(lia)). pose proof (pow2_le_15 c ltac:(lia)). pose proof (pow2_le_15 (c - l) ltac:(lia)).
  assert (E : 2 ^ c = Z.of_nat (Z.to_nat (2 ^ (c - l))) * 2 ^ l).
  { rewrite Z2Nat.id by lia. rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  rewrite E at 1 2. rewrite it_fill_loop; try lia.
  - cbn [snd]. rewrite Z.shiftr_div_pow2 by lia. reflexivity.
  - rewrite Z2Nat.id by lia. nia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint ib (w : nat) (h : Z) : Z :=
  if Z.odd (h / 2 ^ Z.of_nat w) then match w with O => 0 | S w' => ib w' h end
  else 2 ^ Z.of_nat w.

Definition ib_step (huff : Z) (incr : Z) : bool * Z :=
  if negb (Z.land huff incr =? 0) then (true, Z.shiftr incr 1) else (false, incr).

Lemma ib_loop : forall h w fuel, Z.of_nat w + 2 <= fuel ->
  loopZ fuel (ib_step h) (2 ^ Z.of_nat w) = ib w h.
Proof.
  intros h w. induction w as [|w IH]; intros fuel Hf.
  - rewrite loopZ_step by lia. unfold ib_step at 1.
    rewrite land_pow2_eq0 by lia. cbn [ib]. change (2 ^ Z.of_nat 0) with 1. rewrite !Z.div_1_r.
    destruct (Z.odd h); cbn [negb].
    + change (Z.shiftr 1 1) with 0. rewrite loopZ_step by lia. unfold ib_step at 1. rewrite Z.land_0_r. cbn [Z.eqb negb]. reflexivity.
    + reflexivity.
  - rewrite loopZ_step by lia. unfold ib_step at 1. rewrite land_pow2_eq0 by lia. cbn [ib].
    destruct (Z.odd (h / 2 ^ Z.of_nat (S w))); cbn [negb]; [|reflexivity].
    rewrite Z.shiftr_div_pow2 by lia. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
    replace (2 * 2 ^ Z.of_nat w / 2 ^ 1) with (2 ^ Z.of_nat w) by (rewrite Z.mul_comm; apply eq_sym, Z.div_mul; lia).
    apply IH. lia.
Qed.

Lemma it_incr_back_ib : forall h len, 1 <= len <= 15 ->
  it_incr_back h len = ib (Z.to_nat (len - 1)) h.
Proof.
  intros h len Hl. unfold it_incr_back. rewrite shl32_pow2 by lia.
  replace (len - 1) with (Z.of_nat (Z.to_nat (len - 1))) at 1 by lia.
  apply (ib_loop h (Z.to_nat (len - 1)) 32). lia.
Qed.

Lemma ib_cases : forall w h, ib w h = 0 \/ exists p, 0 <= p <= Z.of_nat w /\ ib w h = 2 ^ p.
Proof.
  induction w as [|w IH]; intros h; cbn [ib].
  - destruct (Z.odd _); [left; reflexivity | right; exists 0; split; [lia|reflexivity]].
  - destruct (Z.odd _).
    + destruct (IH h) as [E|[p [Hp E]]]; [left; exact E | right; exists p; split; [lia| exact E]].
    + right. exists (Z.of_nat (S w)). split; [lia|reflexivity].
Qed.

(* [comment removed for export] *)
Lemma ib_high : forall w r q, 0 <= r -> 0 <= q ->
  ib w (q * 2 ^ (Z.of_nat w + 1) + r) = ib w r.
Proof.
  induction w as [|w IH]; intros r q Hr Hq.
  - cbn [ib]. change (2 ^ Z.of_nat 0) with 1. change (Z.of_nat 0 + 1) with 1. rewrite Z.pow_1_r, !Z.div_1_r.
    replace (q * 2 + r) with (r + 2 * q) by lia. rewrite Z.odd_add_mul_2. reflexivity.
  - cbn [ib].
    assert (E : (q * 2 ^ (Z.of_nat (S w) + 1) + r) / 2 ^ Z.of_nat (S w) = r / 2 ^ Z.of_nat (S w) + 2 * q).
    { rewrite Z.pow_add_r, Z.pow_1_r by lia.
      replace (q * (2 ^ Z.of_nat (S w) * 2) + r) with (r + (q * 2) * 2 ^ Z.of_nat (S w)) by lia.
      rewrite Z.div_add by (apply Z.pow_nonzero; lia). lia. }
    rewrite E, Z.odd_add_mul_2.
    destruct (Z.odd (r / 2 ^ Z.of_nat (S w))); [|reflexivity].
    replace (q * 2 ^ (Z.of_nat (S w) + 1)) with ((q * 2) * 2 ^ (Z.of_nat w + 1)).
    2:{ rewrite Nat2Z.inj_succ. replace (Z.succ (Z.of_nat w) + 1) with ((Z.of_nat w + 1) + 1) by lia. rewrite (Z.pow_add_r 2 (Z.of_nat w + 1) 1) by lia. lia. }
    apply IH; lia.
Qed.

(* [comment removed for export] *)
Lemma ib_rev : forall w c, 0 <= c < 2 ^ (Z.of_nat w + 1) ->
  let h := rev (Z.of_nat w + 1) c in
  (c + 1 < 2 ^ (Z.of_nat w + 1) -> ib w h <> 0 /\ Z.land h (ib w h - 1) + ib w h = rev (Z.of_nat w + 1) (c + 1)) /\
  (c + 1 = 2 ^ (Z.of_nat w + 1) -> ib w h = 0).
Proof.
  induction w as [|w IH]; intros c Hc; cbn zeta.
  - change (Z.of_nat 0 + 1) with 1 in *. change (2 ^ 1) with 2 in *.
    assert (c = 0 \/ c = 1) as [->| ->] by lia.
    + cbn. split; [intros _; split; [discriminate|reflexivity] | lia].
    + cbn. split; [lia | reflexivity].
  - set (W1 := Z.of_nat (S w) + 1) in *.
    assert (HW1 : W1 = (Z.of_nat w + 1) + 1) by (subst W1; lia).
    pose proof (Z.pow_nonneg 2 (Z.of_nat w + 1) ltac:(lia)) as P0.
    assert (P1 : 2 ^ W1 = 2 * 2 ^ (Z.of_nat w + 1)) by (rewrite HW1, Z.pow_add_r by lia; lia).
    pose proof (Z.mod_pos_bound c 2 ltac:(lia)) as Mc. pose proof (Z.div_mod c 2 ltac:(lia)) as Dc.
    assert (Hc2 : 0 <= c / 2 < 2 ^ (Z.of_nat w + 1)) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
    (* [comment removed for export] *)
    assert (Eh : rev W1 c = (c mod 2) * 2 ^ (Z.of_nat w + 1) + rev (Z.of_nat w + 1) (c / 2)).
    { rewrite HW1. apply rev_S; lia. }
    pose proof (rev_bound (Z.of_nat w + 1) (c / 2) ltac:(lia)) as Rb.
    set (r := rev (Z.of_nat w + 1) (c / 2)) in *.
    (* [comment removed for export] *)
    assert (Etop : Z.odd (rev W1 c / 2 ^ Z.of_nat (S w)) = Z.odd c).
    { rewrite Eh. replace (Z.of_nat (S w)) with (Z.of_nat w + 1) by lia.
      rewrite Z.add_comm, Z.div_add by lia. rewrite (Z.div_small r) by lia. rewrite Z.add_0_l.
      rewrite Zmod_odd. destruct (Z.odd c); reflexivity. }
    cbn [ib]. rewrite Etop.
    destruct (Z.odd c) eqn:Hodd.
    + (* [comment removed for export] *)
      assert (Hm : c mod 2 = 1) by (rewrite Zmod_odd, Hodd; reflexivity).
      assert (Eib : ib w (rev W1 c) = ib w r).
      { rewrite Eh, Hm, Z.mul_1_l. rewrite <- (Z.mul_1_l (2 ^ (Z.of_nat w + 1))). apply ib_high; lia. }
      rewrite Eib. specialize (IH (c / 2) Hc2). cbn zeta in IH. fold r in IH. destruct IH as [IH1 IH2].
      split.
      * intros Hlt. assert (Hlt2 : c / 2 + 1 < 2 ^ (Z.of_nat w + 1)) by lia.
        destruct (IH1 Hlt2) as [NZ0 E]. split; [exact NZ0|].
        destruct (ib_cases w r) as [Z0|[p [Hp Ep]]]; [contradiction|]. rewrite Ep in *.
        (* [comment removed for export] *)
        assert (EL : Z.land (rev W1 c) (2 ^ p - 1) = Z.land r (2 ^ p - 1)).
        { rewrite !land_ones' by lia. rewrite Eh, Hm, Z.mul_1_l.
          rewrite (pow2_split (Z.of_nat w + 1) p) by lia. rewrite Z.add_comm, Z.mod_add; [reflexivity| apply Z.pow_nonzero; lia]. }
        rewrite EL, E. rewrite HW1. rewrite (rev_S (Z.of_nat w + 1) (c + 1)) by lia.
        replace ((c + 1) mod 2) with 0.
        2:{ replace (c + 1) with (0 + (c / 2 + 1) * 2) by lia. rewrite Z_mod_plus_full. reflexivity. }
        replace ((c + 1) / 2) with (c / 2 + 1).
        2:{ replace (c + 1) with ((c / 2 + 1) * 2) by lia. rewrite Z.div_mul by lia. reflexivity. }
        lia.
      * intros Heq. apply IH2. lia.
    + (* [comment removed for export] *)
      assert (Hm : c mod 2 = 0) by (rewrite Zmod_odd, Hodd; reflexivity).
      split.
      * intros Hlt. split; [apply Z.pow_nonzero; lia|].
        replace (Z.of_nat (S w)) with (Z.of_nat w + 1) by lia.
        rewrite land_ones' by lia. rewrite Eh, Hm, Z.mul_0_l, Z.add_0_l. rewrite (Z.mod_small r) by lia.
        rewrite HW1. rewrite (rev_S (Z.of_nat w + 1) (c + 1)) by lia.
        replace ((c + 1) mod 2) with 1.
        2:{ replace (c + 1) with (1 + (c / 2) * 2) by lia. rewrite Z_mod_plus_full. reflexivity. }
        replace ((c + 1) / 2) with (c / 2).
        2:{ replace (c + 1) with (c / 2 * 2 + 1) by lia. rewrite Z.div_add_l by lia. change (1 / 2) with 0. lia. }
        subst r. lia.
      * intros Heq. exfalso. lia.
Qed.

(* [comment removed for export] *)
Lemma huff_update : forall len c, 1 <= len <= 15 -> 0 <= c < 2 ^ len ->
  (if negb (it_incr_back (rev len c) len =? 0)
   then Z.land (rev len c) (it_incr_back (rev len c) len - 1) + it_incr_back (rev len c) len
   else 0)
  = (if c + 1 <? 2 ^ len then rev len (c + 1) else 0).
Proof.
  intros len c Hl Hc. rewrite it_incr_back_ib by lia.
  pose proof (ib_rev (Z.to_nat (len - 1)) c) as B.
  replace (Z.of_nat (Z.to_nat (len - 1)) + 1) with len in B by lia.
  specialize (B Hc). cbn zeta in B. destruct B as [B1 B2].
  destruct (Z.ltb_spec (c + 1) (2 ^ len)).
  - destruct (B1 ltac:(lia)) as [NZ0 E]. destruct (Z.eqb_spec (ib (Z.to_nat (len - 1)) (rev len c)) 0); [contradiction|].
    cbn [negb]. exact E.
  - rewrite (B2 ltac:(lia)). reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Sub.
  Variable wl : list Z.
  Hypothesis HW : forall l, 0 <= W wl l.
  Hypothesis HL : length wl = 16%nat.
  Variable root : Z.
  Hypothesis Hroot : MINL wl <= root <= MAXL wl.
  Hypothesis HM1 : 1 <= MAXL wl.
  #[local] Set Default Proof Using "HW HL Hroot HM1".

  Local Notation W := (W wl).
  Local Notation MAXL := (MAXL wl).
  Local Notation TM := (TM wl).
  Local Notation len_at := (len_at wl).
  Local Notation rank_at := (rank_at wl).
  Local Notation Apos := (Apos wl).
  Local Notation NZ := (NZ wl).
  Local Notation GR := (GR wl root).
  Local Notation Pfx := (Pfx wl root).
  Local Notation cstar := (cstar wl root).

  (* [comment removed for export] *)
  Definition REM (k l : Z) : Z :=
    if l <? len_at k then 0 else if l =? len_at k then W l - rank_at k else W l.

  Definition sub_step (count : arr) (drop max : Z) (cl : Z * Z) : bool * (Z * Z) :=
    let '(curr, lft) := cl in
    if wrap32 (curr + drop) <? max then
      let lft := lft - arr_get count (wrap32 (curr + drop)) in
      if lft <=? 0 then (false, (curr, lft)) else (true, (wrap32 (curr + 1), Z.shiftl lft 1))
    else (false, (curr, lft)).

  Lemma subtable_curr_spec : forall count k, 0 <= k < NZ -> newtable wl root k = true ->
    (forall l, len_at k <= l <= 15 -> arr_get count l = REM k l) ->
    it_subtable_curr count (len_at k) root MAXL = cstar (Pfx k) (len_at k - root).
  Proof.
    intros count k Hk HN Hcnt.
    pose proof (root_range wl HW HL root Hroot HM1) as RR. pose proof (MAXL_spec wl HW HL) as [MM _].
    pose proof (newtable_long wl HW HL root Hroot HM1 k HN) as HLg. pose proof HLg as HLg'. unfold islong in HLg'. apply Z.ltb_lt in HLg'.
    pose proof (len_at_range wl HW HL k Hk) as LR. pose proof (rank_at_spec wl HW HL k Hk) as RK.
    pose proof (group_start wl HW HL root Hroot HM1 k Hk HN) as GS.
    pose proof (GR_pos wl HW HL root Hroot HM1) as GP.
    set (L := len_at k) in *. set (c0 := L - root).
    pose proof (cstar_spec wl HW HL root Hroot HM1 (Pfx k) c0 ltac:(lia)) as [C1 [C2 C3]].
    set (cs := cstar (Pfx k) c0) in *.
    (* [comment removed for export] *)
    set (RM := fun l => if l <? L then 0 else TM l - Apos k).
    assert (RM_step : forall c, c0 <= c <= MAXL - root ->
              arr_get count (root + c) * 2 ^ (MAXL - root - c) = RM (root + c) - RM (root + c - 1)).
    { intros c Hc. rewrite Hcnt by lia. unfold REM, RM. fold L.
      destruct (Z.ltb_spec (root + c) L); [lia|]. 
      destruct (Z.eqb_spec (root + c) L) as [E|NE].
      - destruct (Z.ltb_spec (root + c - 1) L); [|lia]. rewrite E.
        unfold ItDefs.Apos. fold L. rewrite (TM_step' wl HW HL L) by lia.
        replace (MAXL - root - c) with (MAXL - L) by lia. nia.
      - destruct (Z.ltb_spec (root + c - 1) L); [lia|].
        rewrite (TM_step' wl HW HL (root + c)) by lia. replace (MAXL - root - c) with (MAXL - (root + c)) by lia. nia. }
    assert (RM_c0 : RM (root + c0 - 1) = 0).
    { unfold RM. destruct (Z.ltb_spec (root + c0 - 1) L); [reflexivity|lia]. }
    assert (RM_TM : forall c, c0 <= c -> RM (root + c) = TM (root + c) - Apos k).
    { intros c Hc. unfold RM. destruct (Z.ltb_spec (root + c) L); [lia|reflexivity]. }
    (* [comment removed for export] *)
    assert (LOOP : forall c lft fuel, c0 <= c <= cs -> lft * 2 ^ (MAXL - root - c) = GR - RM (root + c - 1) ->
              cs - c + 1 <= fuel ->
              fst (loopZ fuel (sub_step count root MAXL) (c, lft)) = cs).
    { intros c lft fuel Hc. remember (Z.to_nat (cs - c)) as n eqn:Hn. revert c lft fuel Hc Hn.
      induction n as [|n IH]; intros c lft fuel Hc Hn Hinv Hf.
      - assert (c = cs) by lia. subst c. rewrite loopZ_step by lia. unfold sub_step at 1.
        replace (cs + root) with (root + cs) by lia. rewrite (wrap32_small (root + cs)) by lia.
        destruct (Z.ltb_spec (root + cs) MAXL); [|reflexivity].
        destruct C2 as [C2|C2]; [lia|].
        pose proof (RM_step cs ltac:(lia)) as RS. pose proof (RM_TM cs ltac:(lia)) as RT.
        pose proof (pow2_pos (MAXL - root - cs) ltac:(lia)) as PP.
        assert ((lft - arr_get count (root + cs)) * 2 ^ (MAXL - root - cs) <= 0).
        { rewrite Z.mul_sub_distr_r, RS, Hinv, RT, GS. lia. }
        destruct (Z.leb_spec (lft - arr_get count (root + cs)) 0); [reflexivity| nia].
      - rewrite loopZ_step by lia. unfold sub_step at 1.
        replace (c + root) with (root + c) by lia. rewrite (wrap32_small (root + c)) by lia.
        destruct (C3 c ltac:(lia)) as [D1 D2].
        destruct (Z.ltb_spec (root + c) MAXL); [|lia].
        pose proof (RM_step c ltac:(lia)) as RS. pose proof (RM_TM c ltac:(lia)) as RT.
        pose proof (pow2_pos (MAXL - root - c) ltac:(lia)) as PP.
        assert (HP : 0 < (lft - arr_get count (root + c)) * 2 ^ (MAXL - root - c)).
        { rewrite Z.mul_sub_distr_r, RS, Hinv, RT, GS. lia. }
        destruct (Z.leb_spec (lft - arr_get count (root + c)) 0); [nia|].
        cbn [fst]. rewrite (wrap32_small (c + 1)) by lia. apply IH; try lia.
        rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
        replace (root + (c + 1) - 1) with (root + c) by lia.
        rewrite <- Z.mul_assoc. replace (2 * 2 ^ (MAXL - root - (c + 1))) with (2 ^ (MAXL - root - c)).
        2:{ rewrite <- Z.pow_succ_r by lia. f_equal. lia. }
        rewrite Z.mul_sub_distr_r, RS, Hinv. lia. }
    unfold it_subtable_curr. fold L. rewrite (wrap32_small (L - root)) by lia.
    pose proof (pow2_le_15 (L - root) ltac:(lia)).
    rewrite swrap32_small by (rewrite Z.shiftl_1_l; lia). rewrite Z.shiftl_1_l.
    change (fst (loopZ 16 (sub_step count root MAXL) (L - root, 2 ^ (L - root))) = cs).
    apply LOOP; [lia| |lia].
    fold c0. rewrite RM_c0, <- Z.pow_add_r by lia. unfold ItDefs.GR. rewrite Z.sub_0_r. f_equal. lia.
  Qed.
End Sub.
