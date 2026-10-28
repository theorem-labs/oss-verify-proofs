(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Arith Bool.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzArrD BzCSortF BzCLemmasFs BzCFactsFs BzCPermF
  BzCRebuildF. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCBlock. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzR2Theory BzR3aFs.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzR2D1.
From Stdlib Require Lia.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams BzParamsLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {BZP : BzParams}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma cntP_cnt : forall (P : Z -> bool) k, cntP P k = Z.of_nat (cnt (fun i => P (Z.of_nat i)) k).
Proof.
  induction k as [|k IH]; [reflexivity|]. cbn [cntP]. rewrite cnt_S, IH. destruct (P (Z.of_nat k)); lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Intro.
  Variables (ec fm : zarr) (nb : Z).
  Hypothesis NB : 1 <= nb.
  Hypothesis PM : fm_perm fm nb.
  Hypothesis ECB : forall p, 0 <= p < nb -> 0 <= rd8 ec p < 256.
  Let t := block_of ec nb.
  Let n := Z.to_nat nb.
  Hypothesis SRT : forall i j, 0 <= i -> i <= j -> j < nb -> lexle (rot t (Z.to_nat (rd32 fm i))) (rot t (Z.to_nat (rd32 fm j))).

  Lemma t_length : length t = n. Proof. apply block_of_length. Qed.

  Theorem bwt_intro : bwt t (perm_pi fm) (perm_rho fm nb).
  Proof.
    constructor; rewrite ?t_length.
    - unfold n. lia.
    - apply perm_pi_lt. exact PM.
    - apply perm_rho_lt. exact PM.
    - apply perm_rho_pi. exact PM.
    - apply perm_pi_rho. exact PM.
    - intros i j Hij Hj. unfold perm_pi. apply SRT; unfold n in Hj; lia.
    - unfold t, block_of. apply Forall_map. apply Forall_forall. intros p Hp. apply in_seq in Hp. cbn beta. apply ECB. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma find_orig_spec' : forall k a1 i0, 0 <= i0 ->
    (find_orig k a1 i0 = -1 /\ forall i, i0 <= i < i0 + Z.of_nat k -> rd32 a1 i <> 0) \/
    (i0 <= find_orig k a1 i0 < i0 + Z.of_nat k /\ rd32 a1 (find_orig k a1 i0) = 0).
  Proof.
    induction k as [|k IH]; intros a1 i0 Hi0; cbn [find_orig]; [left; split; [reflexivity| intros; lia]|].
    destruct (Z.eqb_spec (rd32 a1 i0) 0) as [E|NE]; [right; split; [lia| exact E]|].
    destruct (IH a1 (i0 + 1) ltac:(lia)) as [[A B]|[A B]].
    - left. split; [exact A|]. intros i Hi. destruct (Z.eq_dec i i0) as [->|N]; [exact NE| apply B; lia].
    - right. split; [lia| exact B].
  Qed.

  Theorem find_orig_rho : find_orig (Z.to_nat nb) fm 0 = Z.of_nat (origPtr (perm_rho fm nb)).
  Proof.
    unfold origPtr. destruct (perm_rho_spec fm nb PM 0 ltac:(lia)) as [R E].
    destruct (find_orig_spec' (Z.to_nat nb) fm 0 ltac:(lia)) as [[A B]|[A B]].
    - exfalso. apply (B (Z.of_nat (perm_rho fm nb 0))); [lia|]. rewrite E. reflexivity.
    - apply (proj2 PM); [lia|lia|]. rewrite B, E. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Theorem gm_sym_Lc : forall ec' i, (forall p, 0 <= p < nb -> rd8 ec' p = rd8 ec p) -> 0 <= i < nb ->
    rd8 ec' (let j := rd32 fm i - 1 in if j <? 0 then j + nb else j) = Lc t (perm_pi fm) (Z.to_nat i).
  Proof.
    intros ec' i AG Hi. unfold Lc, perm_pi, prv. rewrite t_length, Z2Nat.id by lia.
    pose proof (proj1 PM i Hi) as R.
    destruct (Z.ltb_spec (rd32 fm i - 1) 0).
    - destruct (Nat.eqb_spec (Z.to_nat (rd32 fm i)) 0); [|lia].
      replace (rd32 fm i - 1 + nb) with (nb - 1) by lia. rewrite AG by lia. unfold t. rewrite <- (block_of_nth ec nb (nb - 1)) by lia. f_equal. unfold n. lia.
    - destruct (Nat.eqb_spec (Z.to_nat (rd32 fm i)) 0); [lia|].
      rewrite AG by lia. unfold t. rewrite <- (block_of_nth ec nb (rd32 fm i - 1)) by lia. f_equal. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma Eq_cnt : forall c, Eq ec c n = Z.of_nat (cnt (fun p => nth p t 0 =? c) n).
  Proof.
    intros c. unfold Eq. rewrite cntP_cnt. f_equal. apply cnt_ext. intros k Hk. f_equal.
    unfold t. rewrite <- (Nat2Z.id k) at 2. symmetry. apply block_of_nth. unfold n in Hk. lia.
  Qed.

  Lemma cnt_pos_Fc : forall c, cnt (fun p => nth p t 0 =? c) n = cnt (fun r => Fc t (perm_pi fm) r =? c) n.
  Proof.
    intros c. destruct bwt_intro as [Hn PL RL RP PR _ _]. rewrite t_length in Hn, PL, RL, RP, PR.
    apply Nat.le_antisymm.
    - apply (cnt_inj_le n _ _ (perm_rho fm nb) n).
      + intros p Hp P. split; [apply RL; exact Hp|]. unfold Fc. rewrite PR by exact Hp. exact P.
      + intros k k' Hk Hk' _ _ E. rewrite <- (PR k Hk), <- (PR k' Hk'), E. reflexivity.
    - apply (cnt_inj_le n _ _ (perm_pi fm) n).
      + intros r Hr P. split; [apply PL; exact Hr|]. unfold Fc in P. exact P.
      + intros k k' Hk Hk' _ _ E. rewrite <- (RP k Hk), <- (RP k' Hk'), E. reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
End Intro.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Rebuild.
  Variables (fm ec bh : zarr) (nb : Z).
  Hypothesis ECB : zbok ec.
  Hypothesis BW : bh_w32 bh.
  Hypothesis NB : 1 <= nb <= 900000.
  Let t := block_of ec nb.
  Let n := Z.to_nat nb.
  Let fmF := fh_fm (fp_hsF fm ec bh nb).

  Lemma t_len : length t = n. Proof. apply block_of_length. Qed.

  Lemma sortedF : fm_perm fmF nb /\ rows_sorted t fmF.
  Proof.
    pose proof (fs_rows_sorted t) as S. rewrite t_len in S. unfold n in S. rewrite Z2Nat.id in S by lia.
    apply S; [lia|exact ECB|exact BW|]. intros p Hp. unfold t. apply block_of_nth. exact Hp.
  Qed.

  Let pi := perm_pi fmF.
  Let rho := perm_rho fmF nb.
  Let NB1 : 1 <= nb. Proof. lia. Qed.
  Let PMF : fm_perm fmF nb. Proof. apply sortedF. Qed.
  Let ECB' : forall p, 0 <= p < nb -> 0 <= rd8 ec p < 256. Proof. intros p Hp. unfold rd8. apply ECB. Qed.
  Let SRTF : forall i j, 0 <= i -> i <= j -> j < nb -> lexle (rot t (Z.to_nat (rd32 fmF i))) (rot t (Z.to_nat (rd32 fmF j))).
  Proof. destruct sortedF as [_ SRT]. intros i j Hi Hij Hj. apply SRT; try lia. unfold t. rewrite block_of_length. lia. Qed.
  Let bwtF : bwt t pi rho := bwt_intro ec fmF nb NB1 PMF ECB' SRTF.

  Local Abbreviation Fc := (Fc t pi).
  Local Abbreviation Ccnt := (Ccnt t pi).

  (* [comment removed for export] *)
  Definition RBV (i : nat) (s : zarr * zarr * Z) : Prop :=
    let e := fst (fst s) in let fc := snd (fst s) in let j := snd s in
    (forall c, 0 <= c <= 255 -> zget fc c = Z.of_nat (cnt (fun r => Fc r =? c) n) - Z.of_nat (cnt (fun r => Fc r =? c) i)) /\
    0 <= j /\ ((i < n)%nat -> j <= Fc i) /\
    (forall r, (r < i)%nat -> rd8 e (Z.of_nat (pi r)) = nth (pi r) t 0) /\
    (forall p, nb <= p -> zget e p = zget (fh_ec (fp_hsF fm ec bh nb)) p).

  Lemma RBV0 : RBV 0 (fp_rb fm ec bh nb 0).
  Proof.
    pose proof bwtF as B. unfold RBV, fp_rb. cbn [fs_rebuild fst snd]. split; [|split; [lia|split; [|split; [intros; lia|intros; reflexivity]]]].
    - intros c Hc. rewrite fc0_get. destruct (Z.leb_spec 0 c), (Z.ltb_spec c 256); cbn [andb]; try lia.
      rewrite cnt_0. fold n. rewrite (Eq_cnt ec nb NB1), (cnt_pos_Fc ec fmF nb NB1 PMF ECB' SRTF). fold n t pi. lia.
    - intros Hn. apply (Fc_byte t pi rho B).
  Qed.

  Lemma RBV_step : forall i, (i < n)%nat -> RBV i (fp_rb fm ec bh nb i) -> RBV (S i) (fp_rb fm ec bh nb (S i)).
  Proof.
    intros i Hi R. pose proof bwtF as B. pose proof B as [Hn PL RL RP PR SRT BYT]. rewrite t_len in *.
    rewrite fp_rb_S. cbv zeta.
    set (s := fp_rb fm ec bh nb i) in *. cps_destruct R as (Rc & Rj & Rle & Re & Rhi).
    set (e := fst (fst s)) in *. set (fc := snd (fst s)) in *. set (j := snd s) in *.
    unfold RBV. cbn [fst snd].
    (* [comment removed for export] *)
    assert (ZERO : forall x, 0 <= x < Fc i -> zget fc x = 0).
    { intros x Hx. rewrite Rc by (pose proof (Fc_byte t pi rho B i); lia).
      enough (cnt (fun r => (Fc r =? x)%Z) n <= cnt (fun r => (Fc r =? x)%Z) i)%nat by (pose proof (cnt_le_mono_m (fun r => Fc r =? x) i n ltac:(lia)); lia).
      apply (cnt_inj_le n _ _ (fun r => r) i).
      - intros k Hk P. apply Z.eqb_eq in P. split; [|apply Z.eqb_eq; exact P].
        destruct (Nat.lt_ge_cases k i) as [L|G]; [exact L|exfalso].
        pose proof (Fc_mono t pi rho B i k G ltac:(rewrite t_len; exact Hk)). lia.
      - intros; assumption. }
    assert (POS : zget fc (Fc i) <> 0).
    { rewrite Rc by (pose proof (Fc_byte t pi rho B i); lia).
      enough (cnt (fun r => (Fc r =? Fc i)%Z) i < cnt (fun r => (Fc r =? Fc i)%Z) n)%nat by lia.
      apply (Nat.lt_le_trans _ (cnt (fun r => (Fc r =? Fc i)%Z) (S i))); [|apply cnt_le_mono_m; lia].
      rewrite cnt_S, Z.eqb_refl. lia. }
    cps_destruct (skip0_spec 258 fc j (Fc i) (Rle Hi) ltac:(pose proof (Fc_byte t pi rho B i); cbn; lia) POS) as (A1 & A2 & A3).
    cbv zeta in A1, A2, A3. set (j' := fs_skip0 258 fc j) in *.
    assert (J : j' = Fc i).
    { destruct (Z.lt_ge_cases j' (Fc i)) as [L|G]; [|lia]. exfalso. apply A2. apply ZERO. lia. }
    rewrite J. split; [|split; [pose proof (Fc_byte t pi rho B i); lia|split; [|split]]].
    - intros c Hc. rewrite zget_zset, cnt_S. destruct (Z.eqb_spec c (Fc i)) as [->|NE].
      + rewrite Z.eqb_refl. rewrite Rc by exact Hc. lia.
      + rewrite Rc by exact Hc. destruct (Z.eqb_spec (Fc i) c); [congruence|]. lia.
    - intros HSi. apply (Fc_mono t pi rho B); [lia|rewrite t_len; exact HSi].
    - intros r Hr. unfold rd8, wr8. rewrite zget_zset.
      assert (PI : rd32 fmF (Z.of_nat i) = Z.of_nat (pi i)).
      { unfold pi, perm_pi. rewrite Z2Nat.id; [reflexivity|]. apply (proj1 (proj1 sortedF)). lia. }
      fold fmF. rewrite PI. destruct (Z.eqb_spec (Z.of_nat (pi r)) (Z.of_nat (pi i))) as [E|NE].
      + apply Nat2Z.inj in E. assert (r = i) by (rewrite <- (RP r), <- (RP i), E by lia; reflexivity). subst r.
        unfold BzR2Theory.Fc. apply Z.mod_small. apply (nth_byte t pi rho B).
      + apply Re. destruct (Nat.eq_dec r i) as [->|]; [congruence|lia].
    - intros p Hp. unfold wr8. rewrite zget_zset_other; [apply Rhi; exact Hp|].
      fold fmF. pose proof (proj1 (proj1 sortedF) (Z.of_nat i) ltac:(lia)). lia.
  Qed.

  Lemma RBV_all : forall i, (i <= n)%nat -> RBV i (fp_rb fm ec bh nb i).
  Proof.
    induction i as [|i IH]; intros Hi; [apply RBV0|]. apply RBV_step; [lia|]. apply IH. lia.
  Qed.

  Lemma fallbackSort_ec : fr_ec (fallbackSort fm ec bh znew znew znew znew nb) = fst (fst (fp_rb fm ec bh nb n)).
  Proof.
    unfold fallbackSort, fp_rb, fp_hsF, fp_hs0, fp_bh3, fp_fm1, fp_ft4, fp_dist, fp_ft3, fp_fc0, fp_ft2, fp_ft1, fp_nB.
    destruct (fs_distrib (Z.to_nat nb) (fs_accum 256 (fs_count (Z.to_nat nb) (fs_ftab_zero 257 znew 0) ec 0) 1) fm ec 0) as [ft fm'] eqn:E.
    cbn [fst snd]. fold n. destruct (fs_rebuild _ _ _ _ _ _) as [[ec' fc'] j]. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Theorem fallbackSort_restores :
    (forall q, 0 <= q < nb -> rd8 (fr_ec (fallbackSort fm ec bh znew znew znew znew nb)) q = rd8 ec q) /\
    (forall p, nb <= p -> zget (fr_ec (fallbackSort fm ec bh znew znew znew znew nb)) p = zget (fh_ec (fp_hsF fm ec bh nb)) p).
  Proof.
    rewrite fallbackSort_ec. cps_destruct (RBV_all n ltac:(lia)) as (_ & _ & _ & Re & Rhi). split; [|exact Rhi].
    intros q Hq. pose proof bwtF as [Hn PL RL RP PR SRT BYT]. rewrite t_len in *.
    rewrite <- (Z2Nat.id q) by lia. rewrite <- (PR (Z.to_nat q)) by lia.
    rewrite Re by (apply RL; lia). rewrite PR by lia. rewrite Z2Nat.id by lia. unfold t. apply block_of_nth. lia.
  Qed.

  (* [comment removed for export] *)
  Theorem fallbackSort_bwt :
    let r := fallbackSort fm ec bh znew znew znew znew nb in
    bwt t (perm_pi (fr_fm r)) (perm_rho (fr_fm r) nb) /\
    fm_perm (fr_fm r) nb /\
    find_orig (Z.to_nat nb) (fr_fm r) 0 = Z.of_nat (origPtr (perm_rho (fr_fm r) nb)) /\
    (forall q, 0 <= q < nb -> rd8 (fr_ec r) q = rd8 ec q).
  Proof.
    cbv zeta. rewrite fallbackSort_fm. fold fmF. split; [exact bwtF|]. split; [apply sortedF|].
    split; [apply find_orig_rho; [lia|apply sortedF]|]. apply fallbackSort_restores.
  Qed.
End Rebuild.
End ACeilS1.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzCState. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCSortM BzCSewH.
Section ACeilS2. Context {BZP : BzParams}.


Lemma block_of_ext : forall ec ec' nb, (forall q, 0 <= q < nb -> rd8 ec' q = rd8 ec q) -> block_of ec' nb = block_of ec nb.
Proof.
  intros ec ec' nb AG. unfold block_of. apply map_ext_in. intros p Hp. apply in_seq in Hp. apply AG. lia.
Qed.

(* [comment removed for export] *)
Definition mainSort_hyp (e : est) : Prop :=
  let nb := e_nblock e in
  let qoff := (let i := nb + BZ_N_OVERSHOOT in if Z.land i 1 =? 0 then i else i + 1) in
  let wfact := WORKFACTOR in
  let wfact := if wfact <? 1 then 1 else if 100 <? wfact then 100 else wfact in
  let m := mainSort (e_arr1 e) (e_arr2 e) (e_ftab e) znew znew znew znew znew znew znew qoff nb (nb * ((wfact - 1) / 3)) in
  10000 <= nb ->
  (forall i, 0 <= zget (mr_ftab m) i < 4294967296) /\
  ((mr_budget m <? 0) = false ->
   forall i j, 0 <= i -> i <= j -> j < nb ->
     lexle (rot (block_of (e_arr2 e) nb) (Z.to_nat (rd32 (mr_ptr m) i))) (rot (block_of (e_arr2 e) nb) (Z.to_nat (rd32 (mr_ptr m) j)))).

Theorem blockSort_bwt : forall e,
  zbok (e_arr1 e) -> zbok (e_arr2 e) -> bh_w32 (e_ftab e) -> 1 <= e_nblock e <= 900000 ->
  mainSort_hyp e ->
  let nb := e_nblock e in
  let t := block_of (e_arr2 e) nb in
  let e' := fst (fst (fst (blockSort e znew))) in
  bwt t (perm_pi (e_arr1 e')) (perm_rho (e_arr1 e') nb) /\
  fm_perm (e_arr1 e') nb /\
  e_origPtr e' = Z.of_nat (origPtr (perm_rho (e_arr1 e') nb)) /\
  (forall q, 0 <= q < nb -> rd8 (e_arr2 e') q = rd8 (e_arr2 e) q) /\
  e_nblock e' = nb /\ e_inUse e' = e_inUse e /\ e_unseqToSeq e' = e_unseqToSeq e.
Proof.
  intros e B1 B2 FT NB MSH. cbv zeta. unfold blockSort.
  destruct (Z.ltb_spec (e_nblock e) 10000) as [LT|GE].
  - cbv beta iota zeta. cbn [fst snd e_arr1 e_arr2 e_ftab e_origPtr e_nblock e_inUse e_unseqToSeq].
    pose proof (fallbackSort_bwt (e_arr1 e) (e_arr2 e) (e_ftab e) (e_nblock e) B2 FT NB) as FB. cbv zeta in FB.
    cps_destruct FB as (W & PM & OR & AG).
    split; [exact W|]. split; [exact PM|]. split; [exact OR|]. split; [exact AG|]. split; [reflexivity|]. split; reflexivity.
  - unfold mainSort_hyp in MSH. cbv zeta in MSH. specialize (MSH GE).
    cbv beta iota zeta.
    match goal with |- context [mainSort ?a1 ?a2 ?ft ?l1 ?l2 ?l3 ?l4 ?l5 ?l6 ?l7 ?q ?n ?b] =>
      pose proof (mainSort_post a1 a2 ft l1 l2 l3 l4 l5 l6 l7 q n b B2 B1 ltac:(lia)) as MP;
      set (m := mainSort a1 a2 ft l1 l2 l3 l4 l5 l6 l7 q n b) in * end.
    assert (QO : e_nblock e + 34 <= (if Z.land (e_nblock e + BZ_N_OVERSHOOT) 1 =? 0 then e_nblock e + BZ_N_OVERSHOOT else e_nblock e + BZ_N_OVERSHOOT + 1)).
    { unfold BZ_N_OVERSHOOT. destruct (_ =? 0); lia. }
    specialize (MP QO). cbv zeta in MP. cps_destruct MP as (Z1 & Z2 & AG & PMx). destruct MSH as [MF SRT].
    destruct (Z.ltb_spec (mr_budget m) 0) as [NEG|POS]; cbn [fst snd e_arr1 e_arr2 e_ftab e_origPtr e_nblock e_inUse e_unseqToSeq].
    + pose proof (fallbackSort_bwt (mr_ptr m) (mr_block m) (mr_ftab m) (e_nblock e) Z2 MF NB) as FB. cbv zeta in FB.
      rewrite (block_of_ext (e_arr2 e) (mr_block m)) in FB by exact AG.
      cps_destruct FB as (W & PM & OR & AG').
      split; [exact W|]. split; [exact PM|]. split; [exact OR|]. split; [|split; [reflexivity|]; split; reflexivity].
      intros q Hq. rewrite AG' by exact Hq. apply AG. exact Hq.
    + destruct (PMx eq_refl) as [PM _]. specialize (SRT eq_refl).
      assert (W : bwt (block_of (e_arr2 e) (e_nblock e)) (perm_pi (mr_ptr m)) (perm_rho (mr_ptr m) (e_nblock e))).
      { rewrite <- (block_of_ext (e_arr2 e) (mr_block m) (e_nblock e) AG).
        apply bwt_intro; [lia|exact PM| |rewrite (block_of_ext (e_arr2 e) (mr_block m)) by exact AG; exact SRT].
        intros p Hp. unfold rd8. apply Z2. }
      split; [exact W|]. split; [exact PM|]. split; [apply find_orig_rho; [lia|exact PM]|].
      split; [exact AG|]. split; [reflexivity|]. split; reflexivity.
Qed.

End ACeilS2.
