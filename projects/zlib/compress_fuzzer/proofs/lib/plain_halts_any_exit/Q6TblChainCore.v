(** * Q6TblChainCore — the TABLE-chain value walk, stage lemmas.

    OWNER: an earlier development run (stage-4 split).  The per-stage agreement lemmas of
    the TABLE -> LENLENS -> CODELENS chain, kept import-stable (no root
    Q6 assembly files): the endpoint [ZrTableChain] and its composition
    live in Q6TblChain.v, which additionally imports ZReproL0E /
    Q6HuffResidue (window-blocked at authoring time by model-rt's
    zr-byte-repair).  TRUST BOUNDARY: pure Gallina. *)

From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Chunk Bits BwStream ZBitsIn Huff DeflateSpec Inftrees
  InflateFast Inflate InflateThy StepReach LdDynCl InftreesBridge LdDynRT.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import ZReproQ6A.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(* ==========================================================================
   2.  W1: the TABLE arm's 14-bit header reads agree with the
       declarative 5+5+4 reads on the same stream.
   ========================================================================== *)

Lemma zr_table_reads : forall b b',
  br_wf b ->
  inf_nb 14 b = NBOk b' ->
  read_bits 5%nat (br_stream b)
    = Some (br_bits_of 5 b', br_stream (br_dropbits 5 b'))
  /\ read_bits 5%nat (br_stream (br_dropbits 5 b'))
    = Some (br_bits_of 5 (br_dropbits 5 b'),
            br_stream (br_dropbits 5 (br_dropbits 5 b')))
  /\ read_bits 4%nat (br_stream (br_dropbits 5 (br_dropbits 5 b')))
    = Some (br_bits_of 4 (br_dropbits 5 (br_dropbits 5 b')),
            br_stream (br_dropbits 4 (br_dropbits 5 (br_dropbits 5 b'))))
  /\ br_wf (br_dropbits 4 (br_dropbits 5 (br_dropbits 5 b')))
  /\ br_bits (br_dropbits 4 (br_dropbits 5 (br_dropbits 5 b')))
     = br_bits b' - 14
  /\ 0 <= br_bits_of 5 b' < 32
  /\ 0 <= br_bits_of 5 (br_dropbits 5 b') < 32
  /\ 0 <= br_bits_of 4 (br_dropbits 5 (br_dropbits 5 b')) < 16.
Proof.
  intros b b' Hwf Hnb.
  destruct (inf_nb_ok 14 b b' Hwf ltac:(lia) Hnb) as (Hs & Hwf' & Hb14).
  assert (Hwf1 : br_wf (br_dropbits 5 b'))
    by (apply br_wf_dropbits; [exact Hwf' | lia]).
  pose proof (br_dropbits_bits 5 b') as Hbits1.
  assert (Hwf2 : br_wf (br_dropbits 5 (br_dropbits 5 b')))
    by (apply br_wf_dropbits; [exact Hwf1 | lia]).
  pose proof (br_dropbits_bits 5 (br_dropbits 5 b')) as Hbits2.
  assert (Hwf3 : br_wf (br_dropbits 4 (br_dropbits 5 (br_dropbits 5 b'))))
    by (apply br_wf_dropbits; [exact Hwf2 | lia]).
  pose proof (br_dropbits_bits 4 (br_dropbits 5 (br_dropbits 5 b')))
    as Hbits3.
  assert (Hh' : 0 <= br_hold b')
    by (destruct Hwf' as (_ & Hh & _); lia).
  assert (Hh1 : 0 <= br_hold (br_dropbits 5 b'))
    by (destruct Hwf1 as (_ & Hh & _); lia).
  assert (Hh2 : 0 <= br_hold (br_dropbits 5 (br_dropbits 5 b')))
    by (destruct Hwf2 as (_ & Hh & _); lia).
  pose proof (br_bits_of_range 5 b' ltac:(lia) Hh') as Hr1.
  pose proof (br_bits_of_range 5 (br_dropbits 5 b') ltac:(lia) Hh1) as Hr2.
  pose proof (br_bits_of_range 4 (br_dropbits 5 (br_dropbits 5 b'))
                ltac:(lia) Hh2) as Hr3.
  change (Z.shiftl 1 5) with 32 in Hr1, Hr2.
  change (Z.shiftl 1 4) with 16 in Hr3.
  rewrite <- Hs.
  split.
  { exact (br_read_agree 5 b' Hwf' ltac:(lia)). }
  split.
  { exact (br_read_agree 5 (br_dropbits 5 b') Hwf1 ltac:(lia)). }
  split.
  { exact (br_read_agree 4 (br_dropbits 5 (br_dropbits 5 b')) Hwf2
             ltac:(lia)). }
  split; [exact Hwf3|].
  split; [lia|].
  auto.
Qed.

Print Assumptions zr_table_reads.

(* ==========================================================================
   3.  W2: LENLENS's two whiles agree with [read_cl_lengths]'s reads.
       [scatter_cl_at] (LdDynCl) + [inf_order_covers] (StepReach) carry
       the permutation to the final scatter tie; here are the two facts
       neither had — injectivity and the [pos_of] inverse — plus the
       value-agreement walks themselves.
   ========================================================================== *)

Definition inf_order_inj_chk : bool :=
  forallb (fun i =>
    forallb (fun j =>
      negb (Z.eqb (inf_order (Z.of_nat i)) (inf_order (Z.of_nat j)))
      || Nat.eqb i j)
      (seq 0 19))
    (seq 0 19).

Lemma inf_order_inj_chk_true : inf_order_inj_chk = true.
Proof. vm_compute. reflexivity. Qed.

Lemma inf_order_inj : forall h1 h2,
  0 <= h1 < 19 -> 0 <= h2 < 19 ->
  inf_order h1 = inf_order h2 -> h1 = h2.
Proof.
  intros h1 h2 H1 H2 He.
  pose proof inf_order_inj_chk_true as Hc.
  unfold inf_order_inj_chk in Hc.
  rewrite forallb_forall in Hc.
  specialize (Hc (Z.to_nat h1) ltac:(apply in_seq; lia)).
  rewrite forallb_forall in Hc.
  specialize (Hc (Z.to_nat h2) ltac:(apply in_seq; lia)).
  rewrite !Z2Nat.id in Hc by lia.
  rewrite He, Z.eqb_refl in Hc. cbn [negb orb] in Hc.
  apply Nat.eqb_eq in Hc. lia.
Qed.

Definition inf_order_inv_chk : bool :=
  forallb (fun h =>
    match pos_of (Z.to_nat (inf_order (Z.of_nat h))) cl_order with
    | Some i => Nat.eqb i h
    | None => false
    end)
    (seq 0 19).

Lemma inf_order_inv_chk_true : inf_order_inv_chk = true.
Proof. vm_compute. reflexivity. Qed.

Lemma pos_of_inf_order : forall h,
  0 <= h < 19 ->
  pos_of (Z.to_nat (inf_order h)) cl_order = Some (Z.to_nat h).
Proof.
  intros h Hh.
  pose proof inf_order_inv_chk_true as Hc.
  unfold inf_order_inv_chk in Hc.
  rewrite forallb_forall in Hc.
  specialize (Hc (Z.to_nat h) ltac:(apply in_seq; lia)).
  rewrite Z2Nat.id in Hc by lia.
  destruct (pos_of (Z.to_nat (inf_order h)) cl_order) as [i|];
    [|discriminate Hc].
  apply Nat.eqb_eq in Hc. now rewrite Hc.
Qed.

(** The first while: every 3-bit read lands where [read_3bit_vals] says,
    and everything else is untouched. *)
Lemma ll_go_agree :
  forall f ncode have lens b,
    br_wf b ->
    0 <= have <= ncode -> ncode <= 19 ->
    ncode - have <= Z.of_nat f ->
    match ll_go f ncode have lens b with
    | LlOk hv ls b' =>
        hv = ncode
        /\ br_wf b'
        /\ exists vals,
             read_3bit_vals (Z.to_nat (ncode - have)) (br_stream b)
               = Some (vals, br_stream b')
             /\ length vals = Z.to_nat (ncode - have)
             /\ (forall k, 0 <= k < ncode - have ->
                   ls (inf_order (have + k))
                   = Z.of_nat (nth (Z.to_nat k) vals 0%nat))
             /\ (forall i,
                   (forall k, 0 <= k < ncode - have ->
                      i <> inf_order (have + k)) ->
                   ls i = lens i)
    | LlLeave _ _ _ => True
    end.
Proof.
  induction f as [|f IH]; intros ncode have lens b Hwf Hhn Hn19 Hfuel;
    cbn [ll_go].
  - assert (Heq : have = ncode) by lia. subst ncode.
    split; [reflexivity|]. split; [exact Hwf|].
    exists [].
    replace (Z.to_nat (have - have)) with 0%nat by lia.
    cbn [read_3bit_vals].
    split; [reflexivity|]. split; [reflexivity|].
    split; [intros k Hk; lia|].
    intros i _. reflexivity.
  - destruct (Z.ltb_spec have ncode) as [Hlt|Hge]; cbv beta iota.
    2:{ assert (Heq : have = ncode) by lia. subst ncode.
        split; [reflexivity|]. split; [exact Hwf|].
        exists [].
        replace (Z.to_nat (have - have)) with 0%nat by lia.
        cbn [read_3bit_vals].
        split; [reflexivity|]. split; [reflexivity|].
        split; [intros k Hk; lia|].
        intros i _. reflexivity. }
    destruct (inf_nb 3 b) as [b3|b3] eqn:Enb; cbv beta iota; [|exact I].
    destruct (inf_nb_ok 3 b b3 Hwf ltac:(lia) Enb) as (Hs3 & Hwf3 & Hb3).
    assert (Hwf4 : br_wf (br_dropbits 3 b3))
      by (apply br_wf_dropbits; [exact Hwf3 | lia]).
    assert (Hh3 : 0 <= br_hold b3)
      by (destruct Hwf3 as (_ & Hh & _); lia).
    pose proof (br_bits_of_range 3 b3 ltac:(lia) Hh3) as Hv3.
    change (Z.shiftl 1 3) with 8 in Hv3.
    pose proof (br_read_agree 3 b3 Hwf3 ltac:(lia)) as Hrd.
    change (Z.to_nat 3) with 3%nat in Hrd.
    specialize (IH ncode (have + 1)
                  (zset lens (inf_order have) (br_bits_of 3 b3))
                  (br_dropbits 3 b3) Hwf4 ltac:(lia) Hn19 ltac:(lia)).
    destruct (ll_go f ncode (have + 1)
                (zset lens (inf_order have) (br_bits_of 3 b3))
                (br_dropbits 3 b3)) as [hv ls b'|hv ls b']; [|exact I].
    destruct IH as (Hhv & Hwf' & vals' & Hread' & Hlen' & Hval' & Hfr').
    split; [exact Hhv|]. split; [exact Hwf'|].
    exists (Z.to_nat (br_bits_of 3 b3) :: vals').
    assert (HS : Z.to_nat (ncode - have) = S (Z.to_nat (ncode - have - 1)))
      by lia.
    rewrite HS. cbn [read_3bit_vals].
    rewrite <- Hs3, Hrd. cbv beta iota.
    replace (Z.to_nat (ncode - have - 1))
      with (Z.to_nat (ncode - (have + 1))) by lia.
    rewrite Hread'. cbv beta iota.
    split; [reflexivity|].
    split; [cbn [length]; lia|].
    split.
    { intros k Hk.
      destruct (Z.eq_dec k 0) as [->|Hk0].
      - replace (have + 0) with have by lia.
        assert (Hne : forall k', 0 <= k' < ncode - (have + 1) ->
                  inf_order have <> inf_order (have + 1 + k')).
        { intros k' Hk' He.
          pose proof (inf_order_inj have (have + 1 + k')
                        ltac:(lia) ltac:(lia) He). lia. }
        rewrite (Hfr' (inf_order have) Hne).
        rewrite zset_same.
        change (Z.to_nat 0) with 0%nat. cbn [nth].
        symmetry. apply Z2Nat.id. lia.
      - specialize (Hval' (k - 1) ltac:(lia)).
        replace (have + 1 + (k - 1)) with (have + k) in Hval' by lia.
        rewrite Hval'.
        replace (Z.to_nat k) with (S (Z.to_nat (k - 1))) by lia.
        cbn [nth]. reflexivity. }
    { intros i Hi.
      rewrite (Hfr' i)
        by (intros k' Hk';
            replace (have + 1 + k') with (have + (1 + k')) by lia;
            apply Hi; lia).
      apply zset_other.
      specialize (Hi 0 ltac:(lia)).
      replace (have + 0) with have in Hi by lia.
      exact Hi. }
Qed.

(** The second while: positions [inf_order [have..19)] zeroed, the rest
    untouched. *)
Lemma ll_zero_agree :
  forall f have lens hv ls,
    0 <= have <= 19 -> 19 - have <= Z.of_nat f ->
    ll_zero f have lens = (hv, ls) ->
    hv = 19
    /\ (forall k, have <= k < 19 -> ls (inf_order k) = 0)
    /\ (forall i, (forall k, have <= k < 19 -> i <> inf_order k) ->
          ls i = lens i).
Proof.
  induction f as [|f IH]; intros have lens hv ls Hh Hf Heq;
    cbn [ll_zero] in Heq.
  - assert (have = 19) by lia. subst have.
    injection Heq as <- <-.
    split; [reflexivity|].
    split; [intros k Hk; lia | intros i _; reflexivity].
  - destruct (Z.ltb_spec have 19) as [Hlt|Hge].
    + destruct (IH (have + 1) (zset lens (inf_order have) 0) hv ls
                  ltac:(lia) ltac:(lia) Heq) as (H1 & H2 & H3).
      split; [exact H1|].
      split.
      * intros k Hk.
        destruct (Z.eq_dec k have) as [->|Hne].
        -- assert (Hnf : forall k', have + 1 <= k' < 19 ->
                     inf_order have <> inf_order k').
           { intros k' Hk' He.
             pose proof (inf_order_inj have k' ltac:(lia) ltac:(lia) He).
             lia. }
           rewrite (H3 (inf_order have) Hnf). apply zset_same.
        -- apply H2. lia.
      * intros i Hi.
        rewrite (H3 i) by (intros k' Hk'; apply Hi; lia).
        apply zset_other.
        exact (Hi have ltac:(lia)).
    + assert (have = 19) by lia. subst have.
      injection Heq as <- <-.
      split; [reflexivity|].
      split; [intros k Hk; lia | intros i _; reflexivity].
Qed.

Print Assumptions ll_go_agree.
Print Assumptions ll_zero_agree.

(** The scatter tie: the two whiles' combined [lens] IS
    [zlens (scatter_cl vals)] on the table's whole domain. *)
Lemma scatter_tie :
  forall vals ncode (ls1 : zarr),
    0 <= ncode <= 19 ->
    length vals = Z.to_nat ncode ->
    (forall k, 0 <= k < ncode ->
       ls1 (inf_order k) = Z.of_nat (nth (Z.to_nat k) vals 0%nat)) ->
    (forall k, ncode <= k < 19 -> ls1 (inf_order k) = 0) ->
    forall j, 0 <= j < 19 -> ls1 j = zlens (scatter_cl vals) j.
Proof.
  intros vals ncode ls1 Hnc Hlen Hlow Hhigh j Hj.
  destruct (inf_order_covers j Hj) as (h & Hh & Hoh).
  unfold zlens.
  rewrite (scatter_cl_at vals (Z.to_nat j)) by lia.
  rewrite <- Hoh.
  rewrite (pos_of_inf_order h Hh).
  cbv beta iota.
  destruct (Z_lt_le_dec h ncode) as [Hlt|Hge].
  - rewrite (Hlow h ltac:(lia)). reflexivity.
  - rewrite (Hhigh h ltac:(lia)).
    rewrite nth_overflow by (rewrite Hlen; lia).
    reflexivity.
Qed.

Print Assumptions scatter_tie.

(* ==========================================================================
   4.  W3/W5: an accepted build's length list passes the declarative
       validity check.  Parametric in the bound: the CODES site consumes
       it at m = 7 (via the maxbits transfer), LENS/DISTS at m = 15.
       Stated over the machine's [lens] ARRAY with the window tie
       [arr_eq_on] — no it_model extensionality needed anywhere.
   ========================================================================== *)

(** [findmax = 0] forces every counted bucket empty. *)
Lemma it_findmax_zero : forall n m cnt,
  0 <= m ->
  Z.of_nat n >= m ->
  it_findmax n m cnt = 0 ->
  forall l, 0 < l <= m -> cnt l = 0.
Proof.
  induction n as [|n IH]; intros m cnt Hm Hf Hz l Hl;
    cbn [it_findmax] in Hz; [lia|].
  destruct (Z.eqb_spec (cnt m) 0) as [E|E].
  - destruct (Z.eq_dec l m) as [->|Hne]; [exact E|].
    exact (IH (m - 1) cnt ltac:(lia) ltac:(lia) Hz l ltac:(lia)).
  - lia.
Qed.

(** All-zero lists have Kraft mass zero. *)
Lemma kraft_sum_all_zero : forall (L : list nat) m,
  (forall len, In len L -> len = 0%nat) ->
  kraft_sum L m = 0%nat.
Proof.
  induction L as [|x L IH]; intros m Hz;
    unfold kraft_sum in *; [apply kraft_sum_from_nil|].
  rewrite kraft_sum_from_cons.
  rewrite (Hz x (or_introl eq_refl)).
  rewrite (IH m (fun len H => Hz len (or_intror H))).
  reflexivity.
Qed.

(** [it_pre]'s empty arm exposes its findmax. *)
Lemma it_pre_empty_findmax : forall ty lens codes root0 t0 t,
  it_pre ty lens codes root0 t0 = PreEmpty t ->
  it_findmax 15%nat MAXBITS (it_count (Z.to_nat codes) 0 lens zzero) = 0.
Proof.
  intros ty lens codes root0 t0 t H.
  unfold it_pre in H. cbv zeta in H.
  destruct (Z.eqb_spec
    (it_findmax 15%nat MAXBITS (it_count (Z.to_nat codes) 0 lens zzero)) 0)
    as [E|E]; [exact E|].
  destruct (it_kraft 15%nat 1 1 (it_count (Z.to_nat codes) 0 lens zzero))
    as [lft|]; [|discriminate H].
  destruct (it_incomplete ty lft _); [discriminate H|].
  destruct (it_enough ty _); discriminate H.
Qed.

(** THE bridge. *)
Lemma accept_valid : forall ty (lens : zarr) (L : list nat) codes root0
                            t0 out (m : nat),
  codes = Z.of_nat (length L) ->
  arr_eq_on lens (zlens L) 0 codes ->
  (forall len, In len L -> (len <= m)%nat) ->
  (m <= 15)%nat ->
  it_model ty lens codes root0 t0 = Some out ->
  o_ret out = 0 ->
  valid_lengths_b L m = true.
Proof.
  intros ty lens L codes root0 t0 out m Hcodes Hag Hle Hm Hmod Hret.
  pose proof (counts_of_it_count_agree lens codes L 15%nat Hcodes Hag)
    as Hcnt.
  assert (Hle15 : forall len, In len L -> (len <= 15)%nat)
    by (intros len Hin; pose proof (Hle len Hin); lia).
  apply vl_true.
  apply (proj2 (valid_lengths_maxbits_irrelevant L m 15%nat Hle Hm)).
  unfold it_model in Hmod.
  destruct (it_pre ty lens codes root0 t0) as [ | temp | | c st] eqn:Hpre.
  - injection Hmod as <-. cbn in Hret. lia.
  - (* PreEmpty: every length is zero *)
    pose proof (it_pre_empty_findmax ty lens codes root0 t0 temp Hpre)
      as Hfz.
    assert (Hz : forall len, In len L -> len = 0%nat).
    { intros len Hin.
      destruct len as [|k]; [reflexivity|exfalso].
      pose proof (it_findmax_zero 15%nat MAXBITS
                    (it_count (Z.to_nat codes) 0 lens zzero)
                    ltac:(unfold MAXBITS; lia)
                    ltac:(unfold MAXBITS; lia) Hfz
                    (Z.of_nat (S k))
                    ltac:(pose proof (Hle15 _ Hin); unfold MAXBITS; lia))
        as Hc0.
      specialize (Hcnt (S k) ltac:(pose proof (Hle15 _ Hin); lia)).
      unfold it_cnt0 in Hcnt. rewrite Hc0 in Hcnt.
      assert (Hpos : (0 < count_len L (S k))%nat).
      { unfold count_len. apply count_occ_In. exact Hin. }
      lia. }
    split; [exact Hle15|].
    rewrite (kraft_sum_all_zero L 15%nat Hz). lia.
  - injection Hmod as <-. cbn in Hret. lia.
  - (* PreGo: the accept pair held *)
    destruct (it_pre_go_inv ty lens codes root0 t0 c st Hpre)
      as (_ & _ & Hacc).
    exact (it_accept_valid ty (it_mx lens codes) (it_cnt0 lens codes) L
             Hle15 Hcnt Hacc).
Qed.

Print Assumptions accept_valid.

(* ==========================================================================
   5.  W4: CODELENS's inner while agrees with [read_lengths] — modulo the
       per-symbol FETCH BRIDGE, hypothesized in exactly the shape the
       shared stage-4 instrument provides (model-rt's generic
       fetch-vs-hdecode lemma at an accepted build, or a discharge from
       ZReproQ6K's symbol class at CT_CODES when an earlier development run lands).
       The bridge is CODES-shaped: no pointer hops, symbols are [c_val],
       widths within [1,15] <= 7 after the root clamp.
   ========================================================================== *)

Definition zr_codes_fetch_bridge (cl : list nat) (T : ztbl) (nb : Z)
  : Prop :=
  forall b, br_wf b ->
    match inf_fetch T nb b with
    | FetchOk h b' =>
        br_stream b' = br_stream b
        /\ br_wf b'
        /\ 0 <= c_bits h <= 15
        /\ c_bits h <= br_bits b'
        /\ 0 <= c_val h <= 18
        /\ hdecode (code_table cl 7%nat) (br_stream b')
           = Some (Z.to_nat (c_val h),
                   br_stream (br_dropbits (c_bits h) b'))
    | FetchLeave _ => True
    | FetchFuel => True
    end.

(** Window bookkeeping: the machine's [lens] window mirrors the
    declarative accumulator through both write shapes. *)

Lemma nth_repeat_lt : forall (x d : nat) k n,
  (n < k)%nat -> nth n (repeat x k) d = x.
Proof.
  intros x d k. induction k as [|k IH]; intros n Hn; [lia|].
  destruct n as [|n]; cbn [repeat nth]; [reflexivity|].
  apply IH. lia.
Qed.

Lemma window_snoc : forall (ls : zarr) acc (x : nat),
  arr_eq_on ls (zlens acc) 0 (Z.of_nat (length acc)) ->
  arr_eq_on (zset ls (Z.of_nat (length acc)) (Z.of_nat x))
            (zlens (acc ++ [x])) 0 (Z.of_nat (length (acc ++ [x]))).
Proof.
  intros ls acc x Hag i Hi.
  rewrite length_app in Hi. cbn [length] in Hi.
  destruct (Z.eq_dec i (Z.of_nat (length acc))) as [->|Hne].
  - rewrite zset_same. unfold zlens.
    rewrite Nat2Z.id, app_nth2 by lia.
    replace (length acc - length acc)%nat with 0%nat by lia.
    reflexivity.
  - rewrite zset_other by exact Hne.
    rewrite (Hag i ltac:(lia)).
    unfold zlens. rewrite app_nth1 by lia.
    reflexivity.
Qed.

Lemma window_fill : forall (ls : zarr) acc (x : nat) k,
  arr_eq_on ls (zlens acc) 0 (Z.of_nat (length acc)) ->
  arr_eq_on (zfill k ls (Z.of_nat (length acc)) (Z.of_nat x))
            (zlens (acc ++ repeat x k))
            0 (Z.of_nat (length (acc ++ repeat x k))).
Proof.
  intros ls acc x k Hag i Hi.
  rewrite length_app, repeat_length in Hi.
  destruct (Z_lt_le_dec i (Z.of_nat (length acc))) as [Hlt|Hge].
  - rewrite zfill_miss by (intros m Hm; lia).
    rewrite (Hag i ltac:(lia)).
    unfold zlens. rewrite app_nth1 by lia. reflexivity.
  - replace i with (Z.of_nat (length acc)
                    + Z.of_nat (Z.to_nat (i - Z.of_nat (length acc))))
      by lia.
    rewrite zfill_hit by lia.
    unfold zlens.
    rewrite app_nth2 by lia.
    rewrite nth_repeat_lt by lia.
    reflexivity.
Qed.

Lemma window_last : forall (ls : zarr) acc,
  arr_eq_on ls (zlens acc) 0 (Z.of_nat (length acc)) ->
  (0 < length acc)%nat ->
  exists prev, last_len acc = Some prev
    /\ ls (Z.of_nat (length acc) - 1) = Z.of_nat prev
    /\ In prev acc.
Proof.
  intros ls acc Hag Hlen.
  assert (Hne : acc <> []) by (destruct acc; cbn in Hlen; [lia|congruence]).
  destruct (exists_last Hne) as (acc0 & x & ->).
  rewrite last_len_snoc.
  exists x.
  split; [reflexivity|].
  split.
  - rewrite (Hag (Z.of_nat (length (acc0 ++ [x])) - 1)
              ltac:(rewrite length_app; cbn [length]; lia)).
    unfold zlens.
    rewrite length_app. cbn [length].
    replace (Z.to_nat (Z.of_nat (length acc0 + 1) - 1))
      with (length acc0) by lia.
    rewrite app_nth2 by lia.
    replace (length acc0 - length acc0)%nat with 0%nat by lia.
    reflexivity.
  - apply in_or_app. right. left. reflexivity.
Qed.

Print Assumptions window_fill.

(** Z-valued wrappers, spelled the way the machine writes. *)
Lemma window_snoc_z : forall (ls : zarr) acc v,
  0 <= v ->
  arr_eq_on ls (zlens acc) 0 (Z.of_nat (length acc)) ->
  arr_eq_on (zset ls (Z.of_nat (length acc)) v)
            (zlens (acc ++ [Z.to_nat v])) 0
            (Z.of_nat (length acc) + 1).
Proof.
  intros ls acc v Hv Hag.
  pose proof (window_snoc ls acc (Z.to_nat v) Hag) as H.
  rewrite Z2Nat.id in H by exact Hv.
  rewrite length_app in H. cbn [length] in H.
  intros i Hi. apply H. lia.
Qed.

Lemma window_fill_z : forall (ls : zarr) acc v k,
  0 <= v ->
  arr_eq_on ls (zlens acc) 0 (Z.of_nat (length acc)) ->
  arr_eq_on (zfill k ls (Z.of_nat (length acc)) v)
            (zlens (acc ++ repeat (Z.to_nat v) k)) 0
            (Z.of_nat (length acc) + Z.of_nat k).
Proof.
  intros ls acc v k Hv Hag.
  pose proof (window_fill ls acc (Z.to_nat v) k Hag) as H.
  rewrite Z2Nat.id in H by exact Hv.
  rewrite length_app, repeat_length in H.
  intros i Hi. apply H. lia.
Qed.

(** One CODELENS trip, against one [read_lengths_fuel] unfolding. *)
Lemma cl_step_agree :
  forall cl T nb tot s acc,
    zr_codes_fetch_bridge cl T nb ->
    br_wf (cl_br s) ->
    cl_have s = Z.of_nat (length acc) ->
    (forall x, In x acc -> (x <= 15)%nat) ->
    arr_eq_on (cl_lens s) (zlens acc) 0 (cl_have s) ->
    match cl_step T nb tot s with
    | ClDone s' => s' = s /\ tot <= cl_have s
    | ClCont s1 =>
        cl_have s < tot
        /\ br_wf (cl_br s1)
        /\ exists acc1,
             cl_have s1 = Z.of_nat (length acc1)
             /\ arr_eq_on (cl_lens s1) (zlens acc1) 0 (cl_have s1)
             /\ (forall x, In x acc1 -> (x <= 15)%nat)
             /\ cl_have s < cl_have s1 <= tot
             /\ (forall f',
                  read_lengths_fuel (S f') cl (Z.to_nat (tot - cl_have s))
                    acc (br_stream (cl_br s))
                  = read_lengths_fuel f' cl (Z.to_nat (tot - cl_have s1))
                      acc1 (br_stream (cl_br s1)))
    | _ => True
    end.
Proof.
  intros cl T nb tot s acc HB Hwf Hlen Hbnd Hwin.
  unfold cl_step.
  destruct (Z.leb_spec tot (cl_have s)) as [Hle|Hgt].
  { split; [reflexivity | exact Hle]. }
  pose proof (HB (cl_br s) Hwf) as HF.
  destruct (inf_fetch T nb (cl_br s)) as [h b'|b'|] eqn:EF;
    [| exact I | exact I].
  destruct HF as (Hsb & Hwfb & Hbits & Hbb & Hval & Hdec).
  assert (HneedS : Z.to_nat (tot - cl_have s)
                   = S (Z.to_nat (tot - cl_have s - 1))) by lia.
  destruct (Z.ltb_spec (c_val h) 16) as [Hv16|Hv16].
  - (* :941-944 a length proper *)
    split; [exact Hgt|].
    cbn [cl_br cl_have cl_lens].
    assert (Hwfd : br_wf (br_dropbits (c_bits h) b'))
      by (apply br_wf_dropbits; [exact Hwfb | lia]).
    split; [exact Hwfd|].
    exists (acc ++ [Z.to_nat (c_val h)]).
    split.
    { rewrite length_app. cbn [length]. lia. }
    split.
    { rewrite Hlen.
      replace (Z.of_nat (length acc) + 1)
        with (Z.of_nat (length acc) + 1) by reflexivity.
      apply window_snoc_z; [lia|].
      rewrite <- Hlen. exact Hwin. }
    split.
    { intros x Hin. apply in_app_or in Hin as [Hin|[<-|[]]];
        [exact (Hbnd x Hin) | lia]. }
    split; [lia|].
    intros f'.
    rewrite HneedS. cbn [read_lengths_fuel].
    rewrite <- Hsb, Hdec.
    cbv beta iota.
    replace (Nat.leb (Z.to_nat (c_val h)) 15) with true
      by (symmetry; apply Nat.leb_le; lia).
    cbv beta iota.
    replace (S (Z.to_nat (tot - cl_have s - 1)) - 1)%nat
      with (Z.to_nat (tot - (cl_have s + 1))) by lia.
    reflexivity.
  - (* :946-971 a repeat *)
    assert (Hval3 : c_val h = 16 \/ c_val h = 17 \/ c_val h = 18) by lia.
    set (need := if Z.eqb (c_val h) 16 then c_bits h + 2
                 else if Z.eqb (c_val h) 17 then c_bits h + 3
                 else c_bits h + 7).
    assert (Hneed : c_bits h + 2 <= need <= c_bits h + 7).
    { unfold need.
      destruct (Z.eqb_spec (c_val h) 16); [lia|].
      destruct (Z.eqb_spec (c_val h) 17); lia. }
    destruct (inf_nb need b') as [b2|b2] eqn:ENB; cbv beta iota;
      [| exact I].
    destruct (inf_nb_ok need b' b2 Hwfb ltac:(lia) ENB)
      as (Hs2 & Hwf2 & Hb2).
    assert (Hwfd1 : br_wf (br_dropbits (c_bits h) b2))
      by (apply br_wf_dropbits; [exact Hwf2 | lia]).
    (* the two drops read the same stream *)
    pose proof (br_read_agree (c_bits h) b' Hwfb ltac:(lia)) as HA1.
    pose proof (br_read_agree (c_bits h) b2 Hwf2 ltac:(lia)) as HA2.
    rewrite Hs2 in HA2.
    rewrite HA1 in HA2.
    injection HA2 as Hbo12 Hst12.
    (* the extra-bits read on the post-drop reader *)
    assert (Hbd1 : br_bits (br_dropbits (c_bits h) b2)
                   = br_bits b2 - c_bits h)
      by apply br_dropbits_bits.
    destruct Hval3 as [Hv|[Hv|Hv]].
    + (* symbol 16: repeat the previous length *)
      replace (Z.eqb (c_val h) 16) with true
        by (symmetry; apply Z.eqb_eq; exact Hv).
      rewrite Hv in Hdec.
      cbv beta iota.
      destruct (Z.eqb_spec (cl_have s) 0) as [Hz|Hz]; cbv beta iota;
        [exact I|].
      assert (Hacc0 : (0 < length acc)%nat) by lia.
      destruct (window_last (cl_lens s) acc
                  ltac:(rewrite <- Hlen; exact Hwin) Hacc0)
        as (prev & Hll & Hread & Hinp).
      destruct (Z.ltb_spec tot
                  (cl_have s + (3 + br_bits_of 2 (br_dropbits (c_bits h) b2))))
        as [Hover|Hfit]; cbv beta iota; [exact I|].
      split; [exact Hgt|].
      cbn [cl_br cl_have cl_lens].
      assert (Hwfd2 : br_wf (br_dropbits 2 (br_dropbits (c_bits h) b2)))
        by (apply br_wf_dropbits;
            [exact Hwfd1 | unfold need in *; rewrite Hbd1; lia]).
      split; [exact Hwfd2|].
      assert (Hh1 : 0 <= br_hold (br_dropbits (c_bits h) b2))
        by (destruct Hwfd1 as (_ & Hh & _); lia).
      pose proof (br_bits_of_range 2 (br_dropbits (c_bits h) b2)
                    ltac:(lia) Hh1) as He2.
      change (Z.shiftl 1 2) with 4 in He2.
      exists (acc ++ repeat prev (Z.to_nat
                (3 + br_bits_of 2 (br_dropbits (c_bits h) b2)))).
      split.
      { rewrite length_app, repeat_length. lia. }
      split.
      { assert (Hwin' : arr_eq_on (cl_lens s) (zlens acc) 0
                           (Z.of_nat (length acc)))
          by (rewrite <- Hlen; exact Hwin).
        rewrite Hlen, Hread.
        intros i Hi.
        apply (window_fill (cl_lens s) acc prev
                 (Z.to_nat (3 + br_bits_of 2 (br_dropbits (c_bits h) b2)))
                 Hwin' i).
        rewrite length_app, repeat_length. lia. }
      split.
      { intros x Hin. apply in_app_or in Hin as [Hin|Hin];
          [exact (Hbnd x Hin)|].
        apply repeat_spec in Hin. subst x. exact (Hbnd prev Hinp). }
      split; [lia|].
      intros f'.
      rewrite HneedS. cbn [read_lengths_fuel].
      rewrite <- Hsb, Hdec.
      cbv beta iota.
      replace (Nat.leb (Z.to_nat 16) 15) with false
        by (symmetry; apply Nat.leb_gt; lia).
      cbv beta iota.
      unfold rl_run.
      replace (Nat.eqb (Z.to_nat 16) 16) with true
        by (symmetry; apply Nat.eqb_eq; lia).
      cbv beta iota.
      rewrite Hll.
      cbv beta iota.
      rewrite Hst12.
      pose proof (br_read_agree 2 (br_dropbits (c_bits h) b2) Hwfd1
                    ltac:(unfold need in *; rewrite Hbd1; lia)) as HA3.
      change (Z.to_nat 2) with 2%nat in HA3.
      rewrite HA3.
      cbv beta iota.
      replace (Nat.ltb (S (Z.to_nat (tot - cl_have s - 1)))
                 (Z.to_nat (br_bits_of 2 (br_dropbits (c_bits h) b2)) + 3))
        with false
        by (symmetry; apply Nat.ltb_ge; lia).
      cbv beta iota.
      replace (Z.to_nat (br_bits_of 2 (br_dropbits (c_bits h) b2)) + 3)%nat
        with (Z.to_nat (3 + br_bits_of 2 (br_dropbits (c_bits h) b2)))
        by lia.
      replace (S (Z.to_nat (tot - cl_have s - 1))
               - Z.to_nat (3 + br_bits_of 2 (br_dropbits (c_bits h) b2)))%nat
        with (Z.to_nat (tot - (cl_have s
                + (3 + br_bits_of 2 (br_dropbits (c_bits h) b2))))) by lia.
      reflexivity.
    + (* symbol 17: 3+extra zeros *)
      replace (Z.eqb (c_val h) 16) with false
        by (symmetry; apply Z.eqb_neq; lia).
      replace (Z.eqb (c_val h) 17) with true
        by (symmetry; apply Z.eqb_eq; exact Hv).
      rewrite Hv in Hdec.
      assert (Hneedv : need = c_bits h + 3)
        by (unfold need; rewrite Hv; reflexivity).
      rewrite Hneedv in Hb2.
      cbv beta iota.
      destruct (Z.ltb_spec tot
                  (cl_have s + (3 + br_bits_of 3 (br_dropbits (c_bits h) b2))))
        as [Hover|Hfit]; cbv beta iota; [exact I|].
      split; [exact Hgt|].
      cbn [cl_br cl_have cl_lens].
      assert (Hwfd2 : br_wf (br_dropbits 3 (br_dropbits (c_bits h) b2)))
        by (apply br_wf_dropbits;
            [exact Hwfd1 | rewrite Hbd1; lia]).
      split; [exact Hwfd2|].
      assert (Hh1 : 0 <= br_hold (br_dropbits (c_bits h) b2))
        by (destruct Hwfd1 as (_ & Hh & _); lia).
      pose proof (br_bits_of_range 3 (br_dropbits (c_bits h) b2)
                    ltac:(lia) Hh1) as He2.
      change (Z.shiftl 1 3) with 8 in He2.
      exists (acc ++ repeat 0%nat (Z.to_nat
                (3 + br_bits_of 3 (br_dropbits (c_bits h) b2)))).
      split.
      { rewrite length_app, repeat_length. lia. }
      split.
      { rewrite Hlen.
        replace (Z.of_nat (length acc)
                 + (3 + br_bits_of 3 (br_dropbits (c_bits h) b2)))
          with (Z.of_nat (length acc)
                + Z.of_nat (Z.to_nat
                    (3 + br_bits_of 3 (br_dropbits (c_bits h) b2))))
          by lia.
        replace 0%nat with (Z.to_nat 0) by lia.
        apply window_fill_z; [lia|].
        rewrite <- Hlen. exact Hwin. }
      split.
      { intros x Hin. apply in_app_or in Hin as [Hin|Hin];
          [exact (Hbnd x Hin)|].
        apply repeat_spec in Hin. lia. }
      split; [lia|].
      intros f'.
      rewrite HneedS. cbn [read_lengths_fuel].
      rewrite <- Hsb, Hdec.
      cbv beta iota.
      replace (Nat.leb (Z.to_nat 17) 15) with false
        by (symmetry; apply Nat.leb_gt; lia).
      cbv beta iota.
      unfold rl_run.
      replace (Nat.eqb (Z.to_nat 17) 16) with false
        by (symmetry; apply Nat.eqb_neq; lia).
      replace (Nat.eqb (Z.to_nat 17) 17) with true
        by (symmetry; apply Nat.eqb_eq; lia).
      cbv beta iota.
      rewrite Hst12.
      pose proof (br_read_agree 3 (br_dropbits (c_bits h) b2) Hwfd1
                    ltac:(rewrite Hbd1; lia)) as HA3.
      change (Z.to_nat 3) with 3%nat in HA3.
      rewrite HA3.
      cbv beta iota.
      replace (Nat.ltb (S (Z.to_nat (tot - cl_have s - 1)))
                 (Z.to_nat (br_bits_of 3 (br_dropbits (c_bits h) b2)) + 3))
        with false
        by (symmetry; apply Nat.ltb_ge; lia).
      cbv beta iota.
      replace (Z.to_nat (br_bits_of 3 (br_dropbits (c_bits h) b2)) + 3)%nat
        with (Z.to_nat (3 + br_bits_of 3 (br_dropbits (c_bits h) b2)))
        by lia.
      replace (S (Z.to_nat (tot - cl_have s - 1))
               - Z.to_nat (3 + br_bits_of 3 (br_dropbits (c_bits h) b2)))%nat
        with (Z.to_nat (tot - (cl_have s
                + (3 + br_bits_of 3 (br_dropbits (c_bits h) b2))))) by lia.
      reflexivity.
    + (* symbol 18: 11+extra zeros *)
      replace (Z.eqb (c_val h) 16) with false
        by (symmetry; apply Z.eqb_neq; lia).
      replace (Z.eqb (c_val h) 17) with false
        by (symmetry; apply Z.eqb_neq; lia).
      rewrite Hv in Hdec.
      assert (Hneedv : need = c_bits h + 7)
        by (unfold need; rewrite Hv; reflexivity).
      rewrite Hneedv in Hb2.
      cbv beta iota.
      destruct (Z.ltb_spec tot
                  (cl_have s + (11 + br_bits_of 7 (br_dropbits (c_bits h) b2))))
        as [Hover|Hfit]; cbv beta iota; [exact I|].
      split; [exact Hgt|].
      cbn [cl_br cl_have cl_lens].
      assert (Hwfd2 : br_wf (br_dropbits 7 (br_dropbits (c_bits h) b2)))
        by (apply br_wf_dropbits;
            [exact Hwfd1 | rewrite Hbd1; lia]).
      split; [exact Hwfd2|].
      assert (Hh1 : 0 <= br_hold (br_dropbits (c_bits h) b2))
        by (destruct Hwfd1 as (_ & Hh & _); lia).
      pose proof (br_bits_of_range 7 (br_dropbits (c_bits h) b2)
                    ltac:(lia) Hh1) as He2.
      change (Z.shiftl 1 7) with 128 in He2.
      exists (acc ++ repeat 0%nat (Z.to_nat
                (11 + br_bits_of 7 (br_dropbits (c_bits h) b2)))).
      split.
      { rewrite length_app, repeat_length. lia. }
      split.
      { rewrite Hlen.
        replace (Z.of_nat (length acc)
                 + (11 + br_bits_of 7 (br_dropbits (c_bits h) b2)))
          with (Z.of_nat (length acc)
                + Z.of_nat (Z.to_nat
                    (11 + br_bits_of 7 (br_dropbits (c_bits h) b2))))
          by lia.
        replace 0%nat with (Z.to_nat 0) by lia.
        apply window_fill_z; [lia|].
        rewrite <- Hlen. exact Hwin. }
      split.
      { intros x Hin. apply in_app_or in Hin as [Hin|Hin];
          [exact (Hbnd x Hin)|].
        apply repeat_spec in Hin. lia. }
      split; [lia|].
      intros f'.
      rewrite HneedS. cbn [read_lengths_fuel].
      rewrite <- Hsb, Hdec.
      cbv beta iota.
      replace (Nat.leb (Z.to_nat 18) 15) with false
        by (symmetry; apply Nat.leb_gt; lia).
      cbv beta iota.
      unfold rl_run.
      replace (Nat.eqb (Z.to_nat 18) 16) with false
        by (symmetry; apply Nat.eqb_neq; lia).
      replace (Nat.eqb (Z.to_nat 18) 17) with false
        by (symmetry; apply Nat.eqb_neq; lia).
      replace (Nat.eqb (Z.to_nat 18) 18) with true
        by (symmetry; apply Nat.eqb_eq; lia).
      cbv beta iota.
      rewrite Hst12.
      pose proof (br_read_agree 7 (br_dropbits (c_bits h) b2) Hwfd1
                    ltac:(rewrite Hbd1; lia)) as HA3.
      change (Z.to_nat 7) with 7%nat in HA3.
      rewrite HA3.
      cbv beta iota.
      replace (Nat.ltb (S (Z.to_nat (tot - cl_have s - 1)))
                 (Z.to_nat (br_bits_of 7 (br_dropbits (c_bits h) b2)) + 11))
        with false
        by (symmetry; apply Nat.ltb_ge; lia).
      cbv beta iota.
      replace (Z.to_nat (br_bits_of 7 (br_dropbits (c_bits h) b2)) + 11)%nat
        with (Z.to_nat (11 + br_bits_of 7 (br_dropbits (c_bits h) b2)))
        by lia.
      replace (S (Z.to_nat (tot - cl_have s - 1))
               - Z.to_nat (11 + br_bits_of 7 (br_dropbits (c_bits h) b2)))%nat
        with (Z.to_nat (tot - (cl_have s
                + (11 + br_bits_of 7 (br_dropbits (c_bits h) b2))))) by lia.
      reflexivity.
Qed.

Print Assumptions cl_step_agree.

(** The loop: threading [cl_step_agree] through [cl_loop].  Absorbed
    exits carry no payload (the machine goes BAD / leaves / fuels, and
    the chain's endpoint takes those arms wholesale). *)
Lemma cl_loop_agree :
  forall n cl T nb tot s acc,
    zr_codes_fetch_bridge cl T nb ->
    br_wf (cl_br s) ->
    cl_have s = Z.of_nat (length acc) ->
    (forall x, In x acc -> (x <= 15)%nat) ->
    arr_eq_on (cl_lens s) (zlens acc) 0 (cl_have s) ->
    match cl_loop n T nb tot s with
    | Some (ClDone s') =>
        forall f, (Z.to_nat (tot - cl_have s) <= f)%nat ->
        exists ls,
          read_lengths_fuel f cl (Z.to_nat (tot - cl_have s)) acc
            (br_stream (cl_br s))
          = Some (ls, br_stream (cl_br s'))
          /\ cl_have s' = Z.of_nat (length ls)
          /\ tot <= cl_have s'
          /\ arr_eq_on (cl_lens s') (zlens ls) 0 (cl_have s')
          /\ br_wf (cl_br s')
          /\ (forall x, In x ls -> (x <= 15)%nat)
    | _ => True
    end.
Proof.
  induction n as [|n IH]; intros cl T nb tot s acc HB Hwf Hlen Hbnd Hwin;
    cbn [cl_loop]; [exact I|].
  pose proof (cl_step_agree cl T nb tot s acc HB Hwf Hlen Hbnd Hwin) as HS.
  destruct (cl_step T nb tot s) as [s1|s1|s1 m|s1|] eqn:ES; try exact I.
  - (* ClCont: one more trip *)
    destruct HS as (Hlt & Hwf1 & acc1 & Hlen1 & Hwin1 & Hbnd1 & Hmono
                    & Heqn).
    pose proof (IH cl T nb tot s1 acc1 HB Hwf1 Hlen1 Hbnd1 Hwin1) as HR.
    destruct (cl_loop n T nb tot s1) as [[s2|s2|s2 m2|s2|]|]; try exact I.
    intros f Hf.
    destruct f as [|f0]; [lia|].
    assert (Hf0 : (Z.to_nat (tot - cl_have s1) <= f0)%nat) by lia.
    rewrite (Heqn f0).
    exact (HR f0 Hf0).
  - (* ClDone: nothing left to read *)
    destruct HS as (-> & Hle).
    intros f Hf.
    exists acc.
    replace (Z.to_nat (tot - cl_have s)) with 0%nat by lia.
    destruct f as [|f0]; cbn [read_lengths_fuel];
      (split; [reflexivity|]; split; [exact Hlen|]; split; [exact Hle|];
       split; [exact Hwin|]; split; [exact Hwf|]; exact Hbnd).
Qed.

(** The entry wrapper, at CODELENS's own call shape ([have = 0], fuel
    [S (Z.to_nat tot)], fresh accumulator): the machine's ClDone IS
    [read_lengths]. *)
Lemma cl_loop_read_lengths :
  forall cl T nb tot s,
    zr_codes_fetch_bridge cl T nb ->
    br_wf (cl_br s) ->
    cl_have s = 0 ->
    0 <= tot ->
    match cl_loop (S (Z.to_nat tot)) T nb tot s with
    | Some (ClDone s') =>
        exists ls,
          read_lengths cl (Z.to_nat tot) (br_stream (cl_br s))
          = Some (ls, br_stream (cl_br s'))
          /\ cl_have s' = Z.of_nat (length ls)
          /\ tot <= cl_have s'
          /\ arr_eq_on (cl_lens s') (zlens ls) 0 (cl_have s')
          /\ br_wf (cl_br s')
          /\ (forall x, In x ls -> (x <= 15)%nat)
    | _ => True
    end.
Proof.
  intros cl T nb tot s HB Hwf Hh0 Htot.
  pose proof (cl_loop_agree (S (Z.to_nat tot)) cl T nb tot s [] HB Hwf
                ltac:(rewrite Hh0; reflexivity)
                ltac:(intros x [])
                ltac:(intros i Hi; rewrite Hh0 in Hi; lia)) as HL.
  destruct (cl_loop (S (Z.to_nat tot)) T nb tot s)
    as [[s2|s2|s2 m2|s2|]|]; try exact I.
  specialize (HL (Z.to_nat tot) ltac:(rewrite Hh0; lia)).
  unfold read_lengths.
  rewrite Hh0 in HL.
  replace (tot - 0) with tot in HL by lia.
  exact HL.
Qed.

Print Assumptions cl_loop_agree.
Print Assumptions cl_loop_read_lengths.
