(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation Znumtheory.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords BnKara BnModel BnTree BnWordsCorrect BnDivWords
  BnKaraCorrect BnInv BnSpecs BnSpecs2 BnAddSpec BnDivSpec BnMulSpec.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BgState BgWords BgLib BgArith BgMont BgExp BgTree BgInv BgSpecs BgFrame BgLibSpec
  BgShiftSpec BgAddSpec BgWordSpec BgDivSpec BgMulSpec BgSqrCorrect BgSqrSpec BgModSpec BgMontCorrect BgNumTheory BgMontSpec BgRecpSpec
  BgInvSpec BgMontSpec2 BgCtxSpec BgExpLoops BgExpSpec BgExpWord.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section Top.
Context {ptr : Type}.
Local Notation ST := (bstate ptr) (only parsing).
Local Notation BN := (bignum ptr) (only parsing).
Local Notation ops := (tree_ops ptr) (only parsing).
Local Notation BMu := (BM (M:=btree ptr) (ptr:=ptr)) (only parsing).

Lemma gwp_stepG : forall {A B} F F' (m : BMu A) (f : A -> BMu B) s X R Q,
  st_wf s -> fl_ok s -> own s F X -> hoareG F F' s m R ->
  (forall a s' X', st_wf s' -> fl_ok s' -> own s' (F' a) X' -> R a s' -> gwp (f a s') X' Q) ->
  gwp (bbind ops m f s) X Q.
Proof.
  intros A B F F' m f s X R Q Hs Hf Ho Hm Hk. unfold bbind. cbn [bind tree_ops]. apply gwp_bind.
  eapply gwp_mono; [apply (Hm X Hs Hf Ho)|]. intros [a s'] X' (A1 & A2 & A3 & A4). cbn [fst snd] in *. apply Hk; assumption.
Qed.

Lemma gwp_step : forall {A B} F (m : BMu A) (f : A -> BMu B) s X R Q,
  st_wf s -> fl_ok s -> own s F X -> hoare F s m R ->
  (forall a s' X', st_wf s' -> fl_ok s' -> own s' F X' -> R a s' -> gwp (f a s') X' Q) ->
  gwp (bbind ops m f s) X Q.
Proof. intros A B F m f s X R Q Hs Hf Ho Hm Hk. eapply gwp_stepG; eassumption. Qed.

Lemma gwp_get : forall {B} r (f : BN -> BMu B) s X Q, gwp (f (getbn r s) s) X Q -> gwp (bbind ops (bget ops r) f s) X Q.
Proof. intros B r f s X Q H. exact H. Qed.

Lemma BN_new_gwp : forall {B} r s X (f : ptr -> BMu B) Q,
  ok_bg X BN_STRUCT_BYTES ->
  (forall p, ~ In p (map fst X) -> gwp (f p (setbn r (bn_nil BN_FLG_MALLOCED) s)) ((p, BN_STRUCT_BYTES) :: X) Q) ->
  gwp (bbind ops (BN_new ops r) f s) X Q.
Proof.
  intros B r s X f Q Hok H. unfold BN_new. cbn. split; [exact Hok|]. split; [reflexivity|]. exact H.
Qed.

Lemma BN_CTX_new_gwp : forall {B} s X (f : ptr -> BMu B) Q,
  ok_bg X BN_CTX_BYTES ->
  (forall p, ~ In p (map fst X) -> gwp (f p (set_ctx gx_nil s)) ((p, BN_CTX_BYTES) :: X) Q) ->
  gwp (bbind ops (BN_CTX_new ops) f s) X Q.
Proof.
  intros B s X f Q Hok H. unfold BN_CTX_new. cbn. split; [exact Hok|]. split; [reflexivity|]. exact H.
Qed.

Lemma ok_bg_structs : forall X n, (length X < BG_NBLK)%nat -> Forall (fun xb : ptr * Z => 0 <= snd xb <= BG_BSZ) X -> 0 <= n <= BG_BSZ -> ok_bg X n.
Proof. intros X n H1 H2 H3. unfold ok_bg. auto. Qed.

Definition st_ready : ST :=
  setbn RB5 (bn_nil BN_FLG_MALLOCED) (setbn RB4 (bn_nil BN_FLG_MALLOCED) (setbn RB3 (bn_nil BN_FLG_MALLOCED)
    (setbn RB2 (bn_nil BN_FLG_MALLOCED) (setbn RB1 (bn_nil BN_FLG_MALLOCED) st_init)))).

Lemma st_ready_eq : st_ready = mkST (repeat (bn_nil BN_FLG_MALLOCED) 5 ++ repeat (bn_nil 0) 6 ++ [bn_const_one]) gx_nil 0 0 0 0.
Proof. reflexivity. Qed.

Lemma st_ready_wf : st_wf st_ready.
Proof.
  rewrite st_ready_eq. unfold st_wf. cbn [st_bns st_ctx gx_items length app repeat Nat.mul Nat.add].
  split; [reflexivity|]. split; [|split; [reflexivity|]].
  - intros r Hr Hn. unfold getbn. cbn [st_bns].
    do 12 (destruct r as [|r]; [first [apply bg_ok_nil; right; reflexivity | apply bg_ok_nil; left; reflexivity | exfalso; apply Hn; reflexivity] |]).
    cbn in Hr. lia.
  - unfold ctx_wf. cbn. repeat split; try reflexivity; try lia. left. repeat split; reflexivity.
Qed.

Lemma st_ready_fl : fl_ok st_ready.
Proof.
  rewrite st_ready_eq. intros r Hr Hn. unfold getbn, std_flags. cbn [st_bns length app repeat] in *.
  do 12 (destruct r as [|r]; [first [reflexivity | exfalso; apply Hn; reflexivity] |]). cbn in Hr. lia.
Qed.

Lemma st_ready_blocks : blocks_of st_ready = [].
Proof. reflexivity. Qed.

Lemma BN_bin2bn_spec : forall bytes r F s,
  live r s -> ndiff r ROne -> (length bytes <= 511)%nat ->
  hoare F s (BN_bin2bn ops bytes r) (upd1 r s (fun b' =>
     bn_norm b' /\ (bn_neg b' = false \/ (bn_top b' = 0%nat /\ bn_neg b' = bn_neg (getbn r s))) /\ (bn_top b' <= 64)%nat)).
Proof.
  intros bytes r F s Lr Nr Hlen. apply hoare_wf. intros Hs. pose proof (live_valid r s Hs Lr) as Vr.
  pose proof (st_wf_ok r s Hs Vr Nr) as Hok. pose proof Hok as (O1 & O2 & O3 & O4). unfold bn_dmax in O2, O3.
  unfold BN_bin2bn. apply hoare_bind_get. set (b := getbn r s) in *.
  destruct bytes as [|x bytes'].
  -
    eapply hoare_set; try assumption; try reflexivity.
    + unfold bg_ok, bn_dmax. cbn [bn_buf bn_top bn_flags]. rewrite repeat_length. split; [apply limbs_repeat; exact limb_0|]. split; [lia|]. split; assumption.
    + cbn [bn_buf]. rewrite repeat_length. reflexivity.
    + eexists. split; [reflexivity|]. cbn [bn_top bn_neg]. split; [left; reflexivity|]. split; [left; reflexivity|lia].
  - set (bs := skip_zero_bytes (x :: bytes')).
    assert (Hbsl : (length bs <= length (x :: bytes'))%nat) by apply skip_zero_bytes_length.
    destruct bs as [|y bs'] eqn:Ebs.
    + eapply hoare_set; try assumption; try reflexivity.
      * unfold bg_ok, bn_with_top, bn_dmax. cbn [bn_buf bn_top bn_flags]. repeat split; try assumption. lia.
      * eexists. split; [reflexivity|]. cbn [bn_with_top bn_top bn_neg]. split; [left; reflexivity|]. split; [right; split; reflexivity|lia].
    + set (n := ((length (y :: bs') - 1) / 8 + 1)%nat).
      assert (Hn : (n <= 64)%nat).
      { subst n. cbn [length] in Hbsl, Hlen |- *. pose proof (Nat.div_mod_eq (length bs') 8). pose proof (Nat.mod_upper_bound (length bs') 8 ltac:(lia)).
        replace (S (length bs') - 1)%nat with (length bs') by lia. lia. }
      eapply hoare_bind; [apply bn_wexpand_spec; [exact Vr|exact Nr|unfold BG_DMAX; lia]|].
      intros [] s1 Hs1 (b1 & -> & Hex). destruct Hex as (E1 & E2 & E3 & E4 & Hb1 & E5 & E6). fold b in E1, E2, E3, E4, E6.
      apply hoare_bind_get. rewrite getbn_setbn_same by exact Vr.
      destruct (bytes_to_limbs_spec n (rev (y :: bs'))) as [L1 L2].
      destruct Hb1 as (R1 & R2 & R3 & R4). unfold bn_dmax in *.
      set (b2 := mkBN (bn_d b1) (splice (bn_buf b1) 0 (bin2bn_limbs (y :: bs'))) n false (bn_flags b1)).
      assert (B2 : length (bn_buf b2) = length (bn_buf b1)).
      { subst b2. cbn [bn_buf]. apply splice_length. unfold bin2bn_limbs. fold n. lia. }
      assert (Hb2 : bg_ok b2).
      { unfold bg_ok, bn_dmax. rewrite B2. subst b2. cbn [bn_buf bn_top bn_flags].
        split; [apply splice_limbs; [exact R1|unfold bin2bn_limbs; fold n; exact L1]|]. repeat split; try assumption; lia. }
      destruct (bg_correct_top_ok b2 Hb2) as (C1 & C2 & C3 & C4 & C5 & C6 & C7).
      eapply hoare_set; try rewrite length_setbn; try rewrite getbn_setbn_same by exact Vr; try assumption; try (rewrite C6; reflexivity); try (rewrite C5; exact B2).
      * rewrite setbn_setbn_same. eexists. split; [reflexivity|]. split; [destruct C2 as [Hn' _]; exact Hn'|].
        split; [left; rewrite C7; reflexivity|]. change (bn_top b2) with n in C4. lia.
      * unfold bn_correct_top_pure. cbn [bn_flags]. reflexivity.
Qed.

Lemma bg_split_lengths : forall d n1 n2 n3 s1 s3, bg_split d = (n1, n2, n3, s1, s3) ->
  (length n1 <= 511 /\ length n2 <= 511 /\ length n3 <= 511)%nat.
Proof.
  intros d n1 n2 n3 s1 s3 E. unfold bg_split in E.
  destruct (2 <? length d)%nat.
  - match type of E with context [(?a mod 512)] => set (l1 := a mod 512) in E end.
    match type of E with context [((?a) mod 512)] => try set (l2 := a mod 512) in E end.
    match type of E with context [((?a) mod 512)] => try set (l3 := a mod 512) in E end.
    assert (H1 : 0 <= l1 < 512) by (unfold l1; apply Z.mod_pos_bound; lia).
    assert (H2 : 0 <= l2 < 512) by (unfold l2; apply Z.mod_pos_bound; lia).
    assert (H3 : 0 <= l3 < 512) by (unfold l3; apply Z.mod_pos_bound; lia).
    injection E; intros _ _ <- <- <-. rewrite !length_firstn. lia.
  - injection E; intros _ _ <- <- <-. cbn. lia.
Qed.

Lemma BN_free_some_gwp : forall r p (s : ST) X R (Qk : unit * ST -> blocks -> Prop),
  bn_flags (getbn r s) = BN_FLG_MALLOCED ->
  Permutation X (bn_blocks (getbn r s) ++ (p, BN_STRUCT_BYTES) :: R) ->
  (forall X', Permutation X' R -> Qk (tt, setbn r (bn_nil 0) s) X') ->
  gwp (BN_free ops r (Some p) s) X Qk.
Proof.
  intros r p s X R Qk Hf HP H. unfold BN_free, bbind. cbn [bind tree_ops tbind bget ret fst snd].
  unfold has_flag. rewrite Hf. change (Z.land BN_FLG_MALLOCED BN_FLG_STATIC_DATA =? 0) with true. change (Z.land BN_FLG_MALLOCED BN_FLG_MALLOCED =? 0) with false.
  cbn [negb]. unfold bn_blocks in HP.
  destruct (bn_d (getbn r s)) as [q|]; cbn [bfree_opt bfree bret bset bind lib_free tree_ops tbind gwp ret fst snd app] in *.
  - exists (8 * Z.of_nat (bn_dmax (getbn r s))), ((p, BN_STRUCT_BYTES) :: R). split; [exact HP|].
    exists BN_STRUCT_BYTES, R. split; [apply Permutation_refl|]. apply H. apply Permutation_refl.
  - exists BN_STRUCT_BYTES, R. split; [exact HP|]. apply H. apply Permutation_refl.
Qed.

Definition pool_blocks (s : ST) (i cnt : nat) : blocks := concat (map (fun j => bn_blocks (getbn (RPool j) s)) (seq i cnt)).

Lemma pool_blocks_ext : forall (s s' : ST) i cnt, (forall j, (i <= j < i + cnt)%nat -> getbn (RPool j) s' = getbn (RPool j) s) ->
  pool_blocks s' i cnt = pool_blocks s i cnt.
Proof.
  intros s s' i cnt H. unfold pool_blocks. f_equal. apply map_ext_in. intros j Hj. apply in_seq in Hj. rewrite H by lia. reflexivity.
Qed.

Lemma pool_blocks_S : forall (s : ST) i cnt, pool_blocks s i (S cnt) = bn_blocks (getbn (RPool i) s) ++ pool_blocks s (S i) cnt.
Proof. intros. unfold pool_blocks. rewrite <- cons_seq. reflexivity. Qed.

Lemma pool_blocks_app : forall (s : ST) i a b, pool_blocks s i (a + b) = pool_blocks s i a ++ pool_blocks s (i + a) b.
Proof. intros. unfold pool_blocks. rewrite seq_app, map_app, concat_app. reflexivity. Qed.

Lemma pool_free_vals_gwp : forall cnt i (l : list BN) (s0 : ST) X R (Qk : unit * ST -> blocks -> Prop),
  let s := set_bns l s0 in
  (forall j, (i <= j < i + cnt)%nat -> bn_flags (getbn (RPool j) s) = 0 /\ (RPool j < length l)%nat) ->
  Permutation X (pool_blocks s i cnt ++ R) ->
  (forall l' X', length l' = length l -> (forall z, (z < RPool i)%nat \/ (RPool (i + cnt) <= z)%nat -> nth z l' (bn_nil 0) = nth z l (bn_nil 0)) ->
                Permutation X' R -> Qk (tt, set_bns l' s0) X') ->
  gwp (pool_free_vals ops i cnt s) X Qk.
Proof.
  induction cnt as [|c IH]; intros i l s0 X R Qk s Hfl HP HK.
  - cbn [pool_free_vals]. cbn. apply HK; [reflexivity|intros; reflexivity|]. unfold pool_blocks in HP. cbn [seq map concat app] in HP. exact HP.
  - cbn [pool_free_vals]. unfold bbind at 1. cbn [bind tree_ops bget ret tbind fst snd].
    rewrite pool_blocks_S, <- app_assoc in HP. destruct (Hfl i ltac:(lia)) as [Fi Li].
    assert (STEP : forall X1 (b : BN), bn_d b = None -> bn_flags b = 0 ->
              Permutation X1 (pool_blocks s (S i) c ++ R) ->
              gwp (pool_free_vals ops (S i) c (set_bns (list_set l (RPool i) b) s0)) X1 Qk).
    { intros X1 b Hb Hfb HP1. apply (IH (S i) (list_set l (RPool i) b) s0 X1 R).
      - intros j Hj. unfold getbn. cbn [set_bns st_bns]. rewrite list_set_length, nth_list_set_other by (unfold RPool; lia).
        destruct (Hfl j ltac:(lia)) as [A B]. split; [exact A|exact B].
      - rewrite (pool_blocks_ext s (set_bns (list_set l (RPool i) b) s0)); [exact HP1|]. intros j Hj. unfold getbn. cbn [set_bns st_bns]. apply nth_list_set_other. unfold RPool. lia.
      - intros l' X' Hl' Hz HP'. apply HK; [rewrite Hl', list_set_length; reflexivity| |exact HP'].
        intros z Hz'. rewrite Hz by (unfold RPool in *; lia). apply nth_list_set_other. unfold RPool in *. lia. }
    destruct (bn_d (getbn (RPool i) s)) as [q|] eqn:Ed.
    +
      unfold BN_clear_free, bbind. cbn [bind tree_ops tbind bget ret fst snd]. unfold has_flag. rewrite Fi. cbn [Z.land Z.eqb negb].
      rewrite Ed. cbn [bfree_opt bfree bret bset bind lib_free tree_ops tbind gwp ret fst snd].
      unfold bn_blocks in HP. rewrite Ed in HP. cbn [app] in HP.
      exists (8 * Z.of_nat (bn_dmax (getbn (RPool i) s))), (pool_blocks s (S i) c ++ R). split; [exact HP|].
      unfold setbn. cbn [set_bns st_bns st_ctx st_ri st_n0 st_rbits st_rshift].
      apply (STEP _ (bn_nil 0)); [reflexivity|reflexivity|apply Permutation_refl].
    + cbn. unfold bn_blocks in HP. rewrite Ed in HP. cbn [app] in HP.
      replace (pool_free_vals ops (S i) c s) with (pool_free_vals ops (S i) c (set_bns (list_set l (RPool i) (nth (RPool i) l (bn_nil 0))) s0))
        by (subst s; rewrite list_set_nth_id; reflexivity).
      apply (STEP X (nth (RPool i) l (bn_nil 0))); [exact Ed|exact Fi|exact HP].
Qed.

Definition item_block (p : ptr) : (ptr * Z) := (p, POOL_ITEM_BYTES).

Lemma pool_finish_gwp : forall items k (l : list BN) (s0 : ST) X R (Qk : unit * ST -> blocks -> Prop),
  let s := set_bns l s0 in
  (forall j, (BN_CTX_POOL_SIZE * k <= j < BN_CTX_POOL_SIZE * (k + length items))%nat -> bn_flags (getbn (RPool j) s) = 0 /\ (RPool j < length l)%nat) ->
  Permutation X (pool_blocks s (BN_CTX_POOL_SIZE * k) (BN_CTX_POOL_SIZE * length items) ++ map item_block items ++ R) ->
  (forall l' X', length l' = length l -> (forall z, (z < RPool (BN_CTX_POOL_SIZE * k))%nat -> nth z l' (bn_nil 0) = nth z l (bn_nil 0)) ->
                Permutation X' R -> Qk (tt, set_bns l' s0) X') ->
  gwp (pool_finish ops items k s) X Qk.
Proof.
  induction items as [|it rest IH]; intros k l s0 X R Qk s Hfl HP HK.
  - cbn [pool_finish]. cbn. apply HK; [reflexivity|intros; reflexivity|]. cbn [length Nat.mul pool_blocks seq map concat app] in HP.
    unfold pool_blocks in HP. rewrite Nat.mul_0_r in HP. cbn [seq map concat app] in HP. exact HP.
  - cbn [pool_finish]. unfold bbind at 1. cbn [bind tree_ops]. apply gwp_bind.
    cbn [length] in Hfl, HP. replace (BN_CTX_POOL_SIZE * S (length rest))%nat with (BN_CTX_POOL_SIZE + BN_CTX_POOL_SIZE * length rest)%nat in HP by lia.
    rewrite pool_blocks_app, <- !app_assoc in HP.
    apply (pool_free_vals_gwp BN_CTX_POOL_SIZE (BN_CTX_POOL_SIZE * k) l s0 X _ _ ltac:(intros j Hj; apply Hfl; lia) HP).
    intros l1 X1 Hl1 Hz1 HP1. cbn [fst snd]. unfold bbind at 1. cbn [bind tree_ops bfree lib_free tbind ret fst snd gwp].
    exists POOL_ITEM_BYTES, (pool_blocks s (BN_CTX_POOL_SIZE * k + BN_CTX_POOL_SIZE) (BN_CTX_POOL_SIZE * length rest) ++ map item_block rest ++ R). split.
    { eapply Permutation_trans; [exact HP1|]. cbn [map app]. apply Permutation_sym. apply Permutation_middle. }
    replace (BN_CTX_POOL_SIZE * k + BN_CTX_POOL_SIZE)%nat with (BN_CTX_POOL_SIZE * S k)%nat by lia.
    apply (IH (S k) l1 s0 _ R).
    + intros j Hj. unfold getbn. cbn [set_bns st_bns]. rewrite Hl1. rewrite Hz1 by (right; unfold RPool; lia).
      destruct (Hfl j ltac:(lia)) as [A B]. split; [exact A|exact B].
    + rewrite (pool_blocks_ext s (set_bns l1 s0)); [apply Permutation_refl|]. intros j Hj. unfold getbn. cbn [set_bns st_bns]. apply Hz1. right. unfold RPool. lia.
    + intros l' X' Hl' Hz' HP'. apply HK; [rewrite Hl'; exact Hl1| |exact HP'].
      intros z Hz. rewrite Hz' by (unfold RPool in *; lia). apply Hz1. left. unfold RPool in *. lia.
Qed.

Lemma BN_CTX_free_gwp : forall pc (s : ST) X R (Qk : unit * ST -> blocks -> Prop),
  let c := st_ctx s in
  length (st_bns s) = (NFIX + BN_CTX_POOL_SIZE * length (gx_items c))%nat ->
  (forall j, (j < BN_CTX_POOL_SIZE * length (gx_items c))%nat -> bn_flags (getbn (RPool j) s) = 0) ->
  Permutation X (opt_block (gx_indexes c) (4 * Z.of_nat BN_CTX_START_FRAMES) ++ pool_blocks s 0 (BN_CTX_POOL_SIZE * length (gx_items c)) ++
                 map item_block (gx_items c) ++ (pc, BN_CTX_BYTES) :: R) ->
  (forall X', Permutation X' R -> Qk (tt, set_ctx gx_nil (set_bns (firstn NFIX (st_bns s)) s)) X') ->
  gwp (BN_CTX_free ops pc s) X Qk.
Proof.
  intros pc s X R Qk c Hlen Hfl HP HK. subst c. destruct s as [l0 c0 ri n0 rb rs]. cbn [st_ctx st_bns] in *.
  unfold BN_CTX_free. unfold bbind at 1. cbn [bind tree_ops bgetctx ret tbind fst snd st_ctx].
  unfold bbind at 1. cbn [bind tree_ops].
  assert (REST : forall X1, Permutation X1 (pool_blocks (mkST l0 c0 ri n0 rb rs) 0 (BN_CTX_POOL_SIZE * length (gx_items c0)) ++ map item_block (gx_items c0) ++ (pc, BN_CTX_BYTES) :: R) ->
    gwp (tbind (ret (tree_ops ptr) (tt, mkST l0 c0 ri n0 rb rs)) (fun p : unit * ST =>
       bbind ops (pool_finish ops (gx_items c0) 0) (fun _ => bbind ops (bfree ops pc) (fun _ =>
         bbind ops (bgetst ops) (fun s1 => bbind ops (bsetbns ops (firstn NFIX (st_bns s1))) (fun _ => bsetctx ops gx_nil)))) (snd p))) X1 Qk).
  { intros X1 HP1. cbn [ret tree_ops tbind snd]. unfold bbind at 1. cbn [bind tree_ops]. apply gwp_bind.
    apply (pool_finish_gwp (gx_items c0) 0 l0 (mkST l0 c0 ri n0 rb rs) X1 ((pc, BN_CTX_BYTES) :: R)).
    - intros j Hj. split; [apply Hfl; lia|rewrite Hlen; unfold RPool; lia].
    - rewrite Nat.mul_0_r. exact HP1.
    - intros l' X' Hl' Hz' HP'. unfold bbind, bfree, bgetst, bsetbns, bsetctx. cbn [bind tree_ops ret tbind fst snd st_bns set_bns gwp].
      exists BN_CTX_BYTES, R. split; [exact HP'|]. cbn [tbind set_bns st_bns snd set_ctx st_ri st_n0 st_rbits st_rshift].
      replace (firstn NFIX l') with (firstn NFIX l0); [apply HK; apply Permutation_refl|].
      apply nth_ext with (d := bn_nil 0) (d' := bn_nil 0); [rewrite !length_firstn, Hl'; reflexivity|].
      intros n Hn. rewrite length_firstn in Hn. rewrite !nth_firstn. destruct (Nat.ltb_spec n NFIX); [|lia]. symmetry. apply Hz'. unfold RPool. lia. }
  destruct (gx_indexes c0) as [q|]; cbn [bfree_opt bfree bret bind lib_free tree_ops tbind gwp opt_block app] in HP |- *.
  - exists (4 * Z.of_nat BN_CTX_START_FRAMES), (pool_blocks (mkST l0 c0 ri n0 rb rs) 0 (BN_CTX_POOL_SIZE * length (gx_items c0)) ++ map item_block (gx_items c0) ++ (pc, BN_CTX_BYTES) :: R).
    split; [exact HP|]. apply REST. apply Permutation_refl.
  - apply REST. exact HP.
Qed.

Lemma seq_add : forall k a n, seq (k + a) n = map (fun j => (k + j)%nat) (seq a n).
Proof.
  intros k a n. revert a. induction n as [|n IH]; intros a; [reflexivity|].
  rewrite <- !cons_seq. cbn [map]. f_equal. rewrite <- IH. f_equal. lia.
Qed.

Lemma map_nth_seq : forall (l : list BN) k n, (k + n <= length l)%nat ->
  map (fun j => nth j l (bn_nil 0)) (seq k n) = firstn n (skipn k l).
Proof.
  induction l as [|x l IH]; intros k n H; cbn [length] in H.
  - assert (n = 0)%nat as -> by lia. reflexivity.
  - destruct k as [|k].
    + destruct n as [|n]; [reflexivity|]. rewrite <- cons_seq. cbn [map skipn firstn nth]. f_equal.
      rewrite <- seq_shift, map_map. cbn [nth]. rewrite (IH 0%nat n) by lia. reflexivity.
    + rewrite <- seq_shift, map_map. cbn [skipn nth]. rewrite (IH k n) by lia. reflexivity.
Qed.

Lemma blocks_of_split : forall (s : ST), st_wf s -> exp_pristine s ->
  blocks_of s = bn_blocks (getbn RB1 s) ++ bn_blocks (getbn RB2 s) ++ bn_blocks (getbn RB3 s) ++ bn_blocks (getbn RB4 s) ++ bn_blocks (getbn RB5 s) ++
                pool_blocks s 0 (BN_CTX_POOL_SIZE * length (gx_items (st_ctx s))) ++
                map item_block (gx_items (st_ctx s)) ++ opt_block (gx_indexes (st_ctx s)) (4 * Z.of_nat BN_CTX_START_FRAMES).
Proof.
  intros s Hs ((P1 & P2 & P3 & _ & _) & (P4 & P5 & _ & _) & P6). pose proof Hs as (E & _ & EOne & _).
  unfold blocks_of. rewrite !app_assoc. f_equal. f_equal. rewrite <- !app_assoc.
  set (n := (BN_CTX_POOL_SIZE * length (gx_items (st_ctx s)))%nat) in *.
  rewrite <- (firstn_skipn NFIX (st_bns s)) at 1. rewrite map_app, concat_app.
  replace (firstn NFIX (st_bns s)) with (firstn NFIX (skipn 0 (st_bns s))) by reflexivity.
  rewrite <- (map_nth_seq (st_bns s) 0 NFIX) by (rewrite E; lia).
  rewrite <- (firstn_all2 (skipn NFIX (st_bns s)) (n := n)) by (rewrite length_skipn, E; lia).
  rewrite <- (map_nth_seq (st_bns s) NFIX n) by (rewrite E; lia).
  change (getbn RB1 s) with (nth 0 (st_bns s) (bn_nil 0)). change (getbn RB2 s) with (nth 1 (st_bns s) (bn_nil 0)).
  change (getbn RB3 s) with (nth 2 (st_bns s) (bn_nil 0)). change (getbn RB4 s) with (nth 3 (st_bns s) (bn_nil 0)).
  change (getbn RB5 s) with (nth 4 (st_bns s) (bn_nil 0)).
  unfold getbn, RMontRR, RMontN, RMontNi, RRecpN, RRecpNr, RTmod, ROne in P1, P2, P3, P4, P5, P6, EOne.
  cbn [seq map concat app NFIX Nat.add]. rewrite P1, P2, P3, P4, P5, P6, EOne. cbn [bn_blocks bn_nil bn_const_one bn_d app].
  rewrite <- !app_assoc. do 5 f_equal.
  unfold pool_blocks, getbn, RPool. cbn [app]. replace (seq NFIX n) with (seq (NFIX + 0) n) by (f_equal; lia). rewrite seq_add, !map_map. reflexivity.
Qed.

Local Notation "m ;;; k" := (bbind ops m (fun _ => k)) (at level 61, right associativity).

Definition frame6 (p1 p2 p3 p4 p5 pc : ptr) : blocks :=
  [(pc, BN_CTX_BYTES); (p5, BN_STRUCT_BYTES); (p4, BN_STRUCT_BYTES); (p3, BN_STRUCT_BYTES); (p2, BN_STRUCT_BYTES); (p1, BN_STRUCT_BYTES)].

Lemma suffix_gwp : forall (s : ST) X p1 p2 p3 p4 p5 pc (Q : Z * ST -> blocks -> Prop),
  st_wf s -> fl_ok s -> own s (frame6 p1 p2 p3 p4 p5 pc) X -> exp_pristine s ->
  (forall sf, Q (0, sf) []) ->
  gwp ((BN_free ops RB1 (Some p1) ;;; BN_free ops RB2 (Some p2) ;;; BN_free ops RB3 (Some p3) ;;; BN_free ops RB4 (Some p4) ;;;
        BN_free ops RB5 (Some p5) ;;; BN_CTX_free_g ops pc ;;; bret ops 0) s) X Q.
Proof.
  intros s X p1 p2 p3 p4 p5 pc Q Hs Hf (HP & _ & _) Hpr HQ.
  rewrite (blocks_of_split s Hs Hpr) in HP. unfold frame6 in HP.
  set (B1 := bn_blocks (getbn RB1 s)) in *. set (B2 := bn_blocks (getbn RB2 s)) in *. set (B3 := bn_blocks (getbn RB3 s)) in *.
  set (B4 := bn_blocks (getbn RB4 s)) in *. set (B5 := bn_blocks (getbn RB5 s)) in *.
  set (PP := pool_blocks s 0 (BN_CTX_POOL_SIZE * length (gx_items (st_ctx s))) ++ map item_block (gx_items (st_ctx s)) ++
             opt_block (gx_indexes (st_ctx s)) (4 * Z.of_nat BN_CTX_START_FRAMES)) in *.
  pose proof Hs as (E & _). assert (L5 : (5 <= length (st_bns s))%nat) by (rewrite E; unfold NFIX; lia).
  assert (Fl : forall r, (r < 5)%nat -> bn_flags (getbn r s) = BN_FLG_MALLOCED) by (intros r Hr; apply (fl_ok_flags1 r s Hf Hr); lia).

  assert (Gs : forall r r' (b : BN) (s0 : ST), r <> r' -> getbn r' (setbn r b s0) = getbn r' s0) by (intros; apply getbn_setbn_other; assumption).

  unfold bbind at 1. cbn [bind tree_ops]. apply gwp_bind.
  apply (BN_free_some_gwp RB1 p1 s X (B2 ++ B3 ++ B4 ++ B5 ++ PP ++ [(pc, BN_CTX_BYTES); (p5, BN_STRUCT_BYTES); (p4, BN_STRUCT_BYTES); (p3, BN_STRUCT_BYTES); (p2, BN_STRUCT_BYTES)])).
  { apply Fl. unfold RB1. lia. }
  { eapply Permutation_trans; [exact HP|]. fold B1. rewrite <- !app_assoc.
    change ([(pc, BN_CTX_BYTES); (p5, BN_STRUCT_BYTES); (p4, BN_STRUCT_BYTES); (p3, BN_STRUCT_BYTES); (p2, BN_STRUCT_BYTES); (p1, BN_STRUCT_BYTES)])
      with ([(pc, BN_CTX_BYTES); (p5, BN_STRUCT_BYTES); (p4, BN_STRUCT_BYTES); (p3, BN_STRUCT_BYTES); (p2, BN_STRUCT_BYTES)] ++ [(p1, BN_STRUCT_BYTES)]).
    rewrite <- ?app_assoc. apply Permutation_app_head. rewrite !app_assoc. symmetry. apply Permutation_cons_append. }
  intros X1 HP1. cbn [fst snd]. set (s1 := setbn RB1 (bn_nil 0) s).

  unfold bbind at 1. cbn [bind tree_ops]. apply gwp_bind.
  apply (BN_free_some_gwp RB2 p2 s1 X1 (B3 ++ B4 ++ B5 ++ PP ++ [(pc, BN_CTX_BYTES); (p5, BN_STRUCT_BYTES); (p4, BN_STRUCT_BYTES); (p3, BN_STRUCT_BYTES)])).
  { unfold s1. rewrite Gs by (unfold RB1, RB2; lia). apply Fl. unfold RB2. lia. }
  { eapply Permutation_trans; [exact HP1|]. unfold s1. rewrite Gs by (unfold RB1, RB2; lia). fold B2.
    change ([(pc, BN_CTX_BYTES); (p5, BN_STRUCT_BYTES); (p4, BN_STRUCT_BYTES); (p3, BN_STRUCT_BYTES); (p2, BN_STRUCT_BYTES)])
      with ([(pc, BN_CTX_BYTES); (p5, BN_STRUCT_BYTES); (p4, BN_STRUCT_BYTES); (p3, BN_STRUCT_BYTES)] ++ [(p2, BN_STRUCT_BYTES)]).
    rewrite <- ?app_assoc. apply Permutation_app_head. rewrite !app_assoc. symmetry. apply Permutation_cons_append. }
  intros X2 HP2. cbn [fst snd]. set (s2 := setbn RB2 (bn_nil 0) s1).

  unfold bbind at 1. cbn [bind tree_ops]. apply gwp_bind.
  apply (BN_free_some_gwp RB3 p3 s2 X2 (B4 ++ B5 ++ PP ++ [(pc, BN_CTX_BYTES); (p5, BN_STRUCT_BYTES); (p4, BN_STRUCT_BYTES)])).
  { unfold s2, s1. rewrite !Gs by (unfold RB1, RB2, RB3; lia). apply Fl. unfold RB3. lia. }
  { eapply Permutation_trans; [exact HP2|]. unfold s2, s1. rewrite !Gs by (unfold RB1, RB2, RB3; lia). fold B3.
    change ([(pc, BN_CTX_BYTES); (p5, BN_STRUCT_BYTES); (p4, BN_STRUCT_BYTES); (p3, BN_STRUCT_BYTES)])
      with ([(pc, BN_CTX_BYTES); (p5, BN_STRUCT_BYTES); (p4, BN_STRUCT_BYTES)] ++ [(p3, BN_STRUCT_BYTES)]).
    rewrite <- ?app_assoc. apply Permutation_app_head. rewrite !app_assoc. symmetry. apply Permutation_cons_append. }
  intros X3 HP3. cbn [fst snd]. set (s3 := setbn RB3 (bn_nil 0) s2).

  unfold bbind at 1. cbn [bind tree_ops]. apply gwp_bind.
  apply (BN_free_some_gwp RB4 p4 s3 X3 (B5 ++ PP ++ [(pc, BN_CTX_BYTES); (p5, BN_STRUCT_BYTES)])).
  { unfold s3, s2, s1. rewrite !Gs by (unfold RB1, RB2, RB3, RB4; lia). apply Fl. unfold RB4. lia. }
  { eapply Permutation_trans; [exact HP3|]. unfold s3, s2, s1. rewrite !Gs by (unfold RB1, RB2, RB3, RB4; lia). fold B4.
    change ([(pc, BN_CTX_BYTES); (p5, BN_STRUCT_BYTES); (p4, BN_STRUCT_BYTES)]) with ([(pc, BN_CTX_BYTES); (p5, BN_STRUCT_BYTES)] ++ [(p4, BN_STRUCT_BYTES)]).
    rewrite <- ?app_assoc. apply Permutation_app_head. rewrite !app_assoc. symmetry. apply Permutation_cons_append. }
  intros X4 HP4. cbn [fst snd]. set (s4 := setbn RB4 (bn_nil 0) s3).

  unfold bbind at 1. cbn [bind tree_ops]. apply gwp_bind.
  apply (BN_free_some_gwp RB5 p5 s4 X4 (PP ++ [(pc, BN_CTX_BYTES)])).
  { unfold s4, s3, s2, s1. rewrite !Gs by (unfold RB1, RB2, RB3, RB4, RB5; lia). apply Fl. unfold RB5. lia. }
  { eapply Permutation_trans; [exact HP4|]. unfold s4, s3, s2, s1. rewrite !Gs by (unfold RB1, RB2, RB3, RB4, RB5; lia). fold B5.
    change ([(pc, BN_CTX_BYTES); (p5, BN_STRUCT_BYTES)]) with ([(pc, BN_CTX_BYTES)] ++ [(p5, BN_STRUCT_BYTES)]).
    rewrite <- ?app_assoc. apply Permutation_app_head. rewrite !app_assoc. symmetry. apply Permutation_cons_append. }
  intros X5 HP5. cbn [fst snd]. set (s5 := setbn RB5 (bn_nil 0) s4).

  unfold bbind at 1. cbn [bind tree_ops]. apply gwp_bind.
  assert (Gp : forall z, (5 <= z)%nat -> getbn z s5 = getbn z s).
  { intros z Hz; unfold s5, s4, s3, s2, s1. rewrite !Gs by (unfold RB1, RB2, RB3, RB4, RB5; lia). reflexivity. }
  assert (Ec : st_ctx s5 = st_ctx s) by reflexivity.
  assert (El : length (st_bns s5) = length (st_bns s)) by (unfold s5, s4, s3, s2, s1; rewrite !length_setbn; reflexivity).
  assert (PF5 : forall j, (j < BN_CTX_POOL_SIZE * length (gx_items (st_ctx s)))%nat -> bn_flags (getbn (RPool j) s5) = 0).
  { intros j Hj. rewrite Gp by (unfold RPool, NFIX; lia).
    apply (fl_ok_flags0 (RPool j) s Hf); [unfold RPool, NFIX; lia|rewrite E; unfold RPool, NFIX, BN_CTX_POOL_SIZE in *; lia|unfold RPool, ROne, NFIX; lia]. }

  unfold BN_CTX_free_g.
  replace (pool_fl0 s5) with true.
  2:{ symmetry. unfold pool_fl0. apply forallb_forall. intros b Hb. apply Z.eqb_eq.
      destruct (In_nth _ _ (bn_nil 0) Hb) as (j & Hj & Ej). rewrite length_skipn, El, E in Hj.
      rewrite <- Ej. rewrite nth_skipn. apply (PF5 j). lia. }
  apply (BN_CTX_free_gwp pc s5 X5 []); rewrite ?Ec, ?El.
  - exact E.
  - intros j Hj. rewrite Gp by (unfold RPool, NFIX; lia).
    apply (fl_ok_flags0 (RPool j) s Hf); [unfold RPool, NFIX; lia|rewrite E; unfold RPool, NFIX, BN_CTX_POOL_SIZE in *; lia|unfold RPool, ROne, NFIX; lia].
  - eapply Permutation_trans; [exact HP5|]. unfold PP. rewrite (pool_blocks_ext s s5) by (intros j Hj; apply Gp; unfold RPool, NFIX; lia).
    rewrite <- !app_assoc.
    set (P0 := pool_blocks s 0 _). set (I0 := map item_block _). set (O0 := opt_block _ _). set (C0 := [(pc, BN_CTX_BYTES)]).
    apply (Permutation_trans (l' := ((P0 ++ I0) ++ O0) ++ C0)); [rewrite <- !app_assoc; apply Permutation_refl|].
    apply (Permutation_trans (l' := (O0 ++ (P0 ++ I0)) ++ C0)); [apply Permutation_app_tail; apply Permutation_app_comm|].
    rewrite <- !app_assoc. apply Permutation_refl.
  - intros X' HP'. cbn. apply Permutation_sym, Permutation_nil in HP'. subst X'. apply HQ.
Qed.

Lemma setneg_canon : forall (b : BN) sg, bn_norm b -> (bn_neg b = false \/ (bn_top b = 0%nat /\ True)) \/ True ->
  let b' := bn_with_neg b (sg && negb (bn_top b =? 0)%nat) in bn_norm b' /\ bn_canon b' /\ bn_top b' = bn_top b /\ bn_mag b' = bn_mag b.
Proof.
  intros b sg Hn _. cbv zeta. unfold bn_canon, bn_norm, bn_mag in *. cbn [bn_with_neg bn_top bn_neg bn_buf].
  split; [exact Hn|]. split; [|split; reflexivity]. split; [exact Hn|]. intros E. rewrite E. cbn. apply andb_false_r.
Qed.

Theorem fuzz_one_gwp : forall d, gwp (bg_one (ptr := ptr) d) [] (fun rc X' => X' = [] /\ rc = 0).
Proof.
  intros d. unfold bg_one. apply gwp_bind. unfold fuzz_one_g.
  destruct (bg_split d) as [[[[n1 n2] n3] s1] s3] eqn:Esplit.
  pose proof (bg_split_lengths d n1 n2 n3 s1 s3 Esplit) as (Ln1 & Ln2 & Ln3).
  assert (OK : forall X n, (length X < 6)%nat -> Forall (fun xb : ptr * Z => 0 <= snd xb <= BG_BSZ) X -> (n = BN_STRUCT_BYTES \/ n = BN_CTX_BYTES) -> ok_bg X n).
  { intros X n H1 H2 H3. apply ok_bg_structs; [unfold BG_NBLK; lia|exact H2|unfold BN_STRUCT_BYTES, BN_CTX_BYTES, BG_BSZ in *; lia]. }
  assert (SZ : forall (p : ptr) n X, (n = BN_STRUCT_BYTES \/ n = BN_CTX_BYTES) -> Forall (fun xb : ptr * Z => 0 <= snd xb <= BG_BSZ) X ->
               Forall (fun xb : ptr * Z => 0 <= snd xb <= BG_BSZ) ((p, n) :: X)).
  { intros p n X Hn HX. constructor; [cbn [snd]; unfold BN_STRUCT_BYTES, BN_CTX_BYTES, BG_BSZ in *; lia|exact HX]. }

  apply BN_new_gwp; [apply OK; [cbn; lia|constructor|left; reflexivity]|]. intros p1 _.
  apply BN_new_gwp; [apply OK; [cbn; lia|auto|left; reflexivity]|]. intros p2 _.
  apply BN_new_gwp; [apply OK; [cbn; lia|auto 6|left; reflexivity]|]. intros p3 _.
  apply BN_new_gwp; [apply OK; [cbn; lia|auto 8|left; reflexivity]|]. intros p4 _.
  apply BN_new_gwp; [apply OK; [cbn; lia|auto 10|left; reflexivity]|]. intros p5 _.
  apply BN_CTX_new_gwp; [apply OK; [cbn; lia|auto 12|right; reflexivity]|]. intros pc _.
  change (set_ctx gx_nil _) with (st_ready).
  set (F6 := frame6 p1 p2 p3 p4 p5 pc).
  assert (Ho : own st_ready F6 F6).
  { split; [rewrite st_ready_blocks; apply Permutation_refl|]. split; [cbn; unfold BG_NF; lia|].
    unfold F6, frame6. repeat (apply SZ; [auto|]). constructor. }
  change ((pc, BN_CTX_BYTES) :: (p5, BN_STRUCT_BYTES) :: (p4, BN_STRUCT_BYTES) :: (p3, BN_STRUCT_BYTES) :: (p2, BN_STRUCT_BYTES) :: (p1, BN_STRUCT_BYTES) :: [])
    with F6.

  eapply (gwp_step F6); [apply st_ready_wf|apply st_ready_fl|exact Ho|apply BN_bin2bn_spec; [unfold live, RB1, NFIX; cbn; lia|unfold ndiff, RB1, ROne; lia|exact Ln1]|].
  intros [] sa Xa Hsa Hfa Hoa (b1 & -> & N1 & G1 & T1).
  assert (LEN : forall (b : BN) r, length (st_bns (setbn r b st_ready)) = 12%nat) by (intros; rewrite length_setbn; reflexivity).
  eapply (@gwp_step unit _ F6 (BN_set_negative ops RB1 s1)); [exact Hsa|exact Hfa|exact Hoa|apply BN_set_negative_spec; [rewrite length_setbn; unfold RB1; cbn; lia|unfold RB1, ROne; lia]|].
  intros [] sb Xb Hsb Hfb Hob (b1' & -> & Eb1'). rewrite getbn_setbn_same in Eb1' by (unfold RB1; cbn; lia). rewrite setbn_setbn_same in *.
  pose proof (setneg_canon b1 s1 N1 ltac:(right; exact I)) as (Na & Ca & Ta & Ma). rewrite <- Eb1' in Na, Ca, Ta, Ma. clear Eb1'.

  eapply (@gwp_step unit _ F6 (BN_bin2bn ops n2 RB2)); [exact Hsb|exact Hfb|exact Hob|apply BN_bin2bn_spec; [unfold live, RB2, NFIX; cbn; lia|unfold ndiff, RB2, ROne; lia|exact Ln2]|].
  intros [] sc Xc Hsc Hfc Hoc (b2 & -> & N2 & G2 & T2).

  eapply (@gwp_step unit _ F6 (BN_bin2bn ops n3 RB3)); [exact Hsc|exact Hfc|exact Hoc|apply BN_bin2bn_spec; [unfold live, RB3, NFIX; cbn; lia|unfold ndiff, RB3, ROne; lia|exact Ln3]|].
  intros [] sd Xd Hsd Hfd Hod (b3 & -> & N3 & G3 & T3).
  eapply (@gwp_step unit _ F6 (BN_set_negative ops RB3 s3)); [exact Hsd|exact Hfd|exact Hod|apply BN_set_negative_spec; [rewrite !length_setbn; cbn; unfold RB3; lia|unfold RB3, ROne; lia]|].
  intros [] se Xe Hse Hfe Hoe (b3' & -> & Eb3'). rewrite getbn_setbn_same in Eb3' by (rewrite !length_setbn; cbn; unfold RB3; lia). rewrite setbn_setbn_same in *.
  pose proof (setneg_canon b3 s3 N3 ltac:(right; exact I)) as (Nm & Cm & Tm & Mm). rewrite <- Eb3' in Nm, Cm, Tm, Mm. clear Eb3'.
  set (sm := setbn RB3 b3' (setbn RB2 b2 (setbn RB1 b1' st_ready))) in *.
  assert (Em : getbn RB3 sm = b3') by (unfold sm; apply getbn_setbn_same; rewrite !length_setbn; cbn; unfold RB3; lia).
  assert (Ep : getbn RB2 sm = b2) by (unfold sm; rewrite getbn_setbn_other by (unfold RB3, RB2; lia); apply getbn_setbn_same; rewrite !length_setbn; cbn; unfold RB2; lia).
  assert (Ea : getbn RB1 sm = b1') by (unfold sm; rewrite !getbn_setbn_other by (unfold RB3, RB2, RB1; lia); apply getbn_setbn_same; cbn; unfold RB1; lia).
  assert (Eo : forall z, (3 <= z)%nat -> getbn z sm = getbn z st_ready) by (intros z Hz; unfold sm; rewrite !getbn_setbn_other by (unfold RB1, RB2, RB3; lia); reflexivity).
  assert (PRm : exp_pristine sm).
  { unfold exp_pristine, mont_pristine, recp_pristine. rewrite !Eo by (unfold RMontRR, RMontN, RMontNi, RRecpN, RRecpNr, RTmod; lia). repeat split; reflexivity. }
  assert (Ecm : st_ctx sm = gx_nil) by reflexivity.
  apply gwp_get. rewrite Em.

  unfold bbind at 1. cbn [bind tree_ops]. apply gwp_bind.
  assert (SUF : forall s' X', st_wf s' -> fl_ok s' -> own s' F6 X' -> exp_pristine s' ->
    gwp ((BN_free ops RB1 (Some p1) ;;; BN_free ops RB2 (Some p2) ;;; BN_free ops RB3 (Some p3) ;;; BN_free ops RB4 (Some p4) ;;;
          BN_free ops RB5 (Some p5) ;;; BN_CTX_free_g ops pc ;;; bret ops 0) s') X'
        (fun (a : Z * ST) (X'0 : blocks) => gwp (TRet (fst a)) X'0 (fun (rc : Z) (X'1 : blocks) => X'1 = [] /\ rc = 0))).
  { intros s' X' H1 H2 H3 H4. apply (suffix_gwp s' X' p1 p2 p3 p4 p5 pc _ H1 H2 H3 H4). intros sf. cbn. split; reflexivity. }
  unfold is_zero_pure. destruct (Nat.eqb_spec (bn_top b3') 0) as [Z3|Z3].
  {   cbn. apply (SUF sm Xe Hse Hfe Hoe PRm). }

  assert (PRE : modexp_pre RB4 RB1 RB2 RB3 sm 5 42 /\ modexp_pre RB5 RB1 RB2 RB3 sm 3 38).
  { unfold modexp_pre, live, ndiff. rewrite Ecm, Em, Ep, Ea. cbn [gx_used gx_frames gx_nil length]. unfold RB1, RB2, RB3, RB4, RB5, ROne, NFIX, BG_DEPTH, BG_POOL.
    repeat split; try lia; assumption. }
  destruct PRE as [PRE4 PRE5].
  eapply (@gwp_step unit _ F6 (BN_mod_exp ops RB4 RB1 RB2 RB3)); [exact Hse|exact Hfe|exact Hoe|apply (BN_mod_exp_spec RB4 RB1 RB2 RB3 F6 sm PRE4); [unfold refs5, RB1, RB2, RB3, RB4; lia|exact PRm|rewrite Ea; exact Na|unfold F6, frame6, BG_NF; cbn; lia]|].
  intros [] s7 X7 Hs7 Hf7 Ho7 (K7 & X4 & T4 & PR7). rewrite Ea, Ep, Em in X4. rewrite Em in T4. rewrite Ecm in K7. cbn [gx_used gx_nil] in K7.
  assert (G7 : forall z, (z < NFIX)%nat -> z <> RB4 -> getbn z s7 = getbn z sm).
  { intros z Hz Hz4. apply (keeps_get _ _ _ _ z K7); [lia|]. intros [E|[]]. apply Hz4. rewrite E. reflexivity. }

  eapply (@gwp_step unit _ F6 (BN_mod_exp_simple ops RB5 RB1 RB2 RB3)); [exact Hs7|exact Hf7|exact Ho7|apply (BN_mod_exp_simple_spec RB5 RB1 RB2 RB3 F6 s7); [|unfold RB3, NFIX; lia]|].
  { unfold modexp_pre, live, ndiff in PRE5 |- *. rewrite (keeps_used _ _ _ _ K7), (keeps_frames _ _ _ _ K7), !G7 by (unfold RB1, RB2, RB3, RB4, NFIX; lia). exact PRE5. }
  intros [] s8 X8 Hs8 Hf8 Ho8 (K8 & X5 & T5). rewrite !G7 in X5 by (unfold RB1, RB2, RB3, RB4, NFIX; lia). rewrite !G7 in T5 by (unfold RB1, RB2, RB3, RB4, NFIX; lia). rewrite Ea, Ep, Em in X5. rewrite Em in T5.
  rewrite (keeps_used _ _ _ _ K7) in K8.
  assert (G8 : forall z, (z < NFIX)%nat -> z <> RB5 -> getbn z s8 = getbn z s7).
  { intros z Hz Hz5. apply (keeps_get _ _ _ _ z K8); [lia|]. intros [E|[]]. apply Hz5. rewrite E. reflexivity. }
  apply gwp_get. apply gwp_get. rewrite (G8 RB4) by (unfold RB4, RB5, NFIX; lia).

  destruct X4 as (C4 & Ng4 & M4). destruct X5 as (C5 & Ng5 & M5).
  rewrite (cmp_pure_eq (getbn RB4 s7) (getbn RB5 s8)).
  2:{ apply bg_ok_bn_ok. apply (st_wf_ok RB4 s7 Hs7); [apply live_valid; [exact Hs7|unfold live; rewrite (keeps_used _ _ _ _ K7); unfold RB4, NFIX; lia]|unfold RB4, ROne; lia]. }
  2:{ apply bg_ok_bn_ok. apply (st_wf_ok RB5 s8 Hs8); [apply live_valid; [exact Hs8|unfold live; rewrite (keeps_used _ _ _ _ K8); unfold RB5, NFIX; lia]|unfold RB5, ROne; lia]. }
  2:{ exact C4. } 2:{ exact C5. }
  2:{ unfold bn_val. rewrite Ng4, Ng5, M4, M5. reflexivity. }
  cbn [Z.eqb]. cbn.

  assert (PR8 : exp_pristine s8).
  { destruct PR7 as (M7 & R7 & E7). unfold exp_pristine, mont_pristine, recp_pristine in *.
    destruct K8 as [[_ Sl8] (S1 & S2 & S3 & S4)]. rewrite S1, S2, S3, S4.
    rewrite !Sl8 by (first [unfold RMontRR, RMontN, RMontNi, RRecpN, RRecpNr, RTmod, NFIX; lia | unfold RMontRR, RMontN, RMontNi, RRecpN, RRecpNr, RTmod, RB5; intros [E|[]]; lia]).
    split; [exact M7|]. split; [exact R7|exact E7]. }
  apply (SUF s8 X8 Hs8 Hf8 Ho8 PR8).
Qed.

Lemma leaves_bbind : forall {A B} (m : BMu A) (f : A -> BMu B) (s : ST) (phi : B * ST -> Prop),
  (forall a s', leaves (f a s') phi) -> leaves (bbind ops m f s) phi.
Proof. intros A B m f s phi H. unfold bbind. cbn [bind tree_ops]. apply leaves_bind. intros [a s']. apply H. Qed.

Theorem fuzz_one_leaves : forall d, leaves (bg_one (ptr := ptr) d) (fun rc => rc = 0).
Proof.
  intros d. unfold bg_one. apply leaves_bind'. unfold fuzz_one_g.
  destruct (bg_split d) as [[[[n1 n2] n3] s1] s3].
  repeat (apply leaves_bbind; intros). cbn. reflexivity.
Qed.

End Top.
