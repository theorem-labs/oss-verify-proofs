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

From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BgTop.

Section FuzzA.
Context {M : Type -> Type} {ptr : Type}.
Variable ops : bn_ops M ptr.

Local Notation BM := (BM (M:=M) (ptr:=ptr)) (only parsing).
Local Notation "x <- m ;; k" := (bbind ops m (fun x => k)) (at level 61, m at next level, right associativity).
Local Notation "m ;;; k" := (bbind ops m (fun _ => k)) (at level 61, right associativity).

Definition BN_free_gA (r : bnref) (p : ptr) : BM unit :=
  fun s => if bn_flags (getbn r s) =? BN_FLG_MALLOCED then BN_free ops r (Some p) s else bunr ops s.

Definition fuzz_one_gA (data : list Z) : BM Z :=
  p1 <- BN_new ops RB1 ;;
  p2 <- BN_new ops RB2 ;;
  p3 <- BN_new ops RB3 ;;
  p4 <- BN_new ops RB4 ;;
  p5 <- BN_new ops RB5 ;;
  pc <- BN_CTX_new ops ;;
  let '(n1, n2, n3, s1, s3) := bg_split data in
  BN_bin2bn ops n1 RB1 ;;;
  BN_set_negative ops RB1 s1 ;;;
  BN_bin2bn ops n2 RB2 ;;;
  BN_bin2bn ops n3 RB3 ;;;
  BN_set_negative ops RB3 s3 ;;;
  b3 <- bget ops RB3 ;;
  (if is_zero_pure b3 then bret ops tt
   else
     BN_mod_exp ops RB4 RB1 RB2 RB3 ;;;
     BN_mod_exp_simple ops RB5 RB1 RB2 RB3 ;;;
     b4 <- bget ops RB4 ;;
     b5 <- bget ops RB5 ;;
     if cmp_pure b4 b5 =? 0 then bret ops tt
     else bunr ops) ;;;

  BN_free_gA RB1 p1 ;;;
  BN_free_gA RB2 p2 ;;;
  BN_free_gA RB3 p3 ;;;
  BN_free_gA RB4 p4 ;;;
  BN_free_gA RB5 p5 ;;;
  BN_CTX_free_g ops pc ;;;

  bret ops 0.

End FuzzA.

Definition bg_oneA {ptr} (d : list Z) : btree ptr Z :=
  tbind (fuzz_one_gA (tree_ops ptr) d st_init) (fun p => TRet (fst p)).

Section TopA.
Context {ptr : Type}.
Local Notation ST := (bstate ptr) (only parsing).
Local Notation BN := (bignum ptr) (only parsing).
Local Notation ops := (tree_ops ptr) (only parsing).
Local Notation BMu := (BM (M:=btree ptr) (ptr:=ptr)) (only parsing).
Local Notation "x <- m ;; k" := (bbind ops m (fun x => k)) (at level 61, m at next level, right associativity).
Local Notation "m ;;; k" := (bbind ops m (fun _ => k)) (at level 61, right associativity).

Lemma BN_free_gA_gwp : forall r p (s : ST) X R (Qk : unit * ST -> blocks -> Prop),
  bn_flags (getbn r s) = BN_FLG_MALLOCED ->
  Permutation X (bn_blocks (getbn r s) ++ (p, BN_STRUCT_BYTES) :: R) ->
  (forall X', Permutation X' R -> Qk (tt, setbn r (bn_nil 0) s) X') ->
  gwp (BN_free_gA ops r p s) X Qk.
Proof.
  intros r p s X R Qk Hf HP H. unfold BN_free_gA. rewrite Hf. change (BN_FLG_MALLOCED =? BN_FLG_MALLOCED) with true. cbv iota.
  exact (BN_free_some_gwp r p s X R Qk Hf HP H).
Qed.

Lemma suffix_gwpA : forall (s : ST) X p1 p2 p3 p4 p5 pc (Q : Z * ST -> blocks -> Prop),
  st_wf s -> fl_ok s -> own s (frame6 p1 p2 p3 p4 p5 pc) X -> exp_pristine s ->
  (forall sf, Q (0, sf) []) ->
  gwp ((BN_free_gA ops RB1 p1 ;;; BN_free_gA ops RB2 p2 ;;; BN_free_gA ops RB3 p3 ;;; BN_free_gA ops RB4 p4 ;;;
        BN_free_gA ops RB5 p5 ;;; BN_CTX_free_g ops pc ;;; bret ops 0) s) X Q.
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
  apply (BN_free_gA_gwp RB1 p1 s X (B2 ++ B3 ++ B4 ++ B5 ++ PP ++ [(pc, BN_CTX_BYTES); (p5, BN_STRUCT_BYTES); (p4, BN_STRUCT_BYTES); (p3, BN_STRUCT_BYTES); (p2, BN_STRUCT_BYTES)])).
  { apply Fl. unfold RB1. lia. }
  { eapply Permutation_trans; [exact HP|]. fold B1. rewrite <- !app_assoc.
    change ([(pc, BN_CTX_BYTES); (p5, BN_STRUCT_BYTES); (p4, BN_STRUCT_BYTES); (p3, BN_STRUCT_BYTES); (p2, BN_STRUCT_BYTES); (p1, BN_STRUCT_BYTES)])
      with ([(pc, BN_CTX_BYTES); (p5, BN_STRUCT_BYTES); (p4, BN_STRUCT_BYTES); (p3, BN_STRUCT_BYTES); (p2, BN_STRUCT_BYTES)] ++ [(p1, BN_STRUCT_BYTES)]).
    rewrite <- ?app_assoc. apply Permutation_app_head. rewrite !app_assoc. symmetry. apply Permutation_cons_append. }
  intros X1 HP1. cbn [fst snd]. set (s1 := setbn RB1 (bn_nil 0) s).

  unfold bbind at 1. cbn [bind tree_ops]. apply gwp_bind.
  apply (BN_free_gA_gwp RB2 p2 s1 X1 (B3 ++ B4 ++ B5 ++ PP ++ [(pc, BN_CTX_BYTES); (p5, BN_STRUCT_BYTES); (p4, BN_STRUCT_BYTES); (p3, BN_STRUCT_BYTES)])).
  { unfold s1. rewrite Gs by (unfold RB1, RB2; lia). apply Fl. unfold RB2. lia. }
  { eapply Permutation_trans; [exact HP1|]. unfold s1. rewrite Gs by (unfold RB1, RB2; lia). fold B2.
    change ([(pc, BN_CTX_BYTES); (p5, BN_STRUCT_BYTES); (p4, BN_STRUCT_BYTES); (p3, BN_STRUCT_BYTES); (p2, BN_STRUCT_BYTES)])
      with ([(pc, BN_CTX_BYTES); (p5, BN_STRUCT_BYTES); (p4, BN_STRUCT_BYTES); (p3, BN_STRUCT_BYTES)] ++ [(p2, BN_STRUCT_BYTES)]).
    rewrite <- ?app_assoc. apply Permutation_app_head. rewrite !app_assoc. symmetry. apply Permutation_cons_append. }
  intros X2 HP2. cbn [fst snd]. set (s2 := setbn RB2 (bn_nil 0) s1).

  unfold bbind at 1. cbn [bind tree_ops]. apply gwp_bind.
  apply (BN_free_gA_gwp RB3 p3 s2 X2 (B4 ++ B5 ++ PP ++ [(pc, BN_CTX_BYTES); (p5, BN_STRUCT_BYTES); (p4, BN_STRUCT_BYTES)])).
  { unfold s2, s1. rewrite !Gs by (unfold RB1, RB2, RB3; lia). apply Fl. unfold RB3. lia. }
  { eapply Permutation_trans; [exact HP2|]. unfold s2, s1. rewrite !Gs by (unfold RB1, RB2, RB3; lia). fold B3.
    change ([(pc, BN_CTX_BYTES); (p5, BN_STRUCT_BYTES); (p4, BN_STRUCT_BYTES); (p3, BN_STRUCT_BYTES)])
      with ([(pc, BN_CTX_BYTES); (p5, BN_STRUCT_BYTES); (p4, BN_STRUCT_BYTES)] ++ [(p3, BN_STRUCT_BYTES)]).
    rewrite <- ?app_assoc. apply Permutation_app_head. rewrite !app_assoc. symmetry. apply Permutation_cons_append. }
  intros X3 HP3. cbn [fst snd]. set (s3 := setbn RB3 (bn_nil 0) s2).

  unfold bbind at 1. cbn [bind tree_ops]. apply gwp_bind.
  apply (BN_free_gA_gwp RB4 p4 s3 X3 (B5 ++ PP ++ [(pc, BN_CTX_BYTES); (p5, BN_STRUCT_BYTES)])).
  { unfold s3, s2, s1. rewrite !Gs by (unfold RB1, RB2, RB3, RB4; lia). apply Fl. unfold RB4. lia. }
  { eapply Permutation_trans; [exact HP3|]. unfold s3, s2, s1. rewrite !Gs by (unfold RB1, RB2, RB3, RB4; lia). fold B4.
    change ([(pc, BN_CTX_BYTES); (p5, BN_STRUCT_BYTES); (p4, BN_STRUCT_BYTES)]) with ([(pc, BN_CTX_BYTES); (p5, BN_STRUCT_BYTES)] ++ [(p4, BN_STRUCT_BYTES)]).
    rewrite <- ?app_assoc. apply Permutation_app_head. rewrite !app_assoc. symmetry. apply Permutation_cons_append. }
  intros X4 HP4. cbn [fst snd]. set (s4 := setbn RB4 (bn_nil 0) s3).

  unfold bbind at 1. cbn [bind tree_ops]. apply gwp_bind.
  apply (BN_free_gA_gwp RB5 p5 s4 X4 (PP ++ [(pc, BN_CTX_BYTES)])).
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

Theorem fuzz_one_gwpA : forall d, gwp (bg_oneA (ptr := ptr) d) [] (fun rc X' => X' = [] /\ rc = 0).
Proof.
  intros d. unfold bg_oneA. apply gwp_bind. unfold fuzz_one_gA.
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
  change (set_ctx gx_nil _) with (@st_ready ptr).
  set (F6 := frame6 p1 p2 p3 p4 p5 pc).
  assert (Ho : own st_ready F6 F6).
  { split; [rewrite st_ready_blocks; apply Permutation_refl|]. split; [cbn; unfold BG_NF; lia|].
    unfold F6, frame6. repeat (apply SZ; [auto|]). constructor. }
  change ((pc, BN_CTX_BYTES) :: (p5, BN_STRUCT_BYTES) :: (p4, BN_STRUCT_BYTES) :: (p3, BN_STRUCT_BYTES) :: (p2, BN_STRUCT_BYTES) :: (p1, BN_STRUCT_BYTES) :: [])
    with F6.

  eapply (gwp_step F6); [apply st_ready_wf|apply st_ready_fl|exact Ho|apply BN_bin2bn_spec; [unfold live, RB1, NFIX; cbn; lia|unfold ndiff, RB1, ROne; lia|exact Ln1]|].
  intros [] sa Xa Hsa Hfa Hoa (b1 & -> & N1 & G1 & T1).
  assert (LEN : forall (b : BN) r, length (st_bns (setbn r b st_ready)) = 12%nat) by (intros; rewrite length_setbn; reflexivity).
  eapply (@gwp_step ptr unit _ F6 (BN_set_negative ops RB1 s1)); [exact Hsa|exact Hfa|exact Hoa|apply BN_set_negative_spec; [rewrite length_setbn; unfold RB1; cbn; lia|unfold RB1, ROne; lia]|].
  intros [] sb Xb Hsb Hfb Hob (b1' & -> & Eb1'). rewrite getbn_setbn_same in Eb1' by (unfold RB1; cbn; lia). rewrite setbn_setbn_same in *.
  pose proof (setneg_canon b1 s1 N1 ltac:(right; exact I)) as (Na & Ca & Ta & Ma). rewrite <- Eb1' in Na, Ca, Ta, Ma. clear Eb1'.

  eapply (@gwp_step ptr unit _ F6 (BN_bin2bn ops n2 RB2)); [exact Hsb|exact Hfb|exact Hob|apply BN_bin2bn_spec; [unfold live, RB2, NFIX; cbn; lia|unfold ndiff, RB2, ROne; lia|exact Ln2]|].
  intros [] sc Xc Hsc Hfc Hoc (b2 & -> & N2 & G2 & T2).

  eapply (@gwp_step ptr unit _ F6 (BN_bin2bn ops n3 RB3)); [exact Hsc|exact Hfc|exact Hoc|apply BN_bin2bn_spec; [unfold live, RB3, NFIX; cbn; lia|unfold ndiff, RB3, ROne; lia|exact Ln3]|].
  intros [] sd Xd Hsd Hfd Hod (b3 & -> & N3 & G3 & T3).
  eapply (@gwp_step ptr unit _ F6 (BN_set_negative ops RB3 s3)); [exact Hsd|exact Hfd|exact Hod|apply BN_set_negative_spec; [rewrite !length_setbn; cbn; unfold RB3; lia|unfold RB3, ROne; lia]|].
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
    gwp ((BN_free_gA ops RB1 p1 ;;; BN_free_gA ops RB2 p2 ;;; BN_free_gA ops RB3 p3 ;;; BN_free_gA ops RB4 p4 ;;;
          BN_free_gA ops RB5 p5 ;;; BN_CTX_free_g ops pc ;;; bret ops 0) s') X'
        (fun (a : Z * ST) (X'0 : blocks) => gwp (TRet (fst a)) X'0 (fun (rc : Z) (X'1 : blocks) => X'1 = [] /\ rc = 0))).
  { intros s' X' H1 H2 H3 H4. apply (suffix_gwpA s' X' p1 p2 p3 p4 p5 pc _ H1 H2 H3 H4). intros sf. cbn. split; reflexivity. }
  unfold is_zero_pure. destruct (Nat.eqb_spec (bn_top b3') 0) as [Z3|Z3].
  {   cbn. apply (SUF sm Xe Hse Hfe Hoe PRm). }

  assert (PRE : modexp_pre RB4 RB1 RB2 RB3 sm 5 42 /\ modexp_pre RB5 RB1 RB2 RB3 sm 3 38).
  { unfold modexp_pre, live, ndiff. rewrite Ecm, Em, Ep, Ea. cbn [gx_used gx_frames gx_nil length]. unfold RB1, RB2, RB3, RB4, RB5, ROne, NFIX, BG_DEPTH, BG_POOL.
    repeat split; try lia; assumption. }
  destruct PRE as [PRE4 PRE5].
  eapply (@gwp_step ptr unit _ F6 (BN_mod_exp ops RB4 RB1 RB2 RB3)); [exact Hse|exact Hfe|exact Hoe|apply (BN_mod_exp_spec RB4 RB1 RB2 RB3 F6 sm PRE4); [unfold refs5, RB1, RB2, RB3, RB4; lia|exact PRm|rewrite Ea; exact Na|unfold F6, frame6, BG_NF; cbn; lia]|].
  intros [] s7 X7 Hs7 Hf7 Ho7 (K7 & X4 & T4 & PR7). rewrite Ea, Ep, Em in X4. rewrite Em in T4. rewrite Ecm in K7. cbn [gx_used gx_nil] in K7.
  assert (G7 : forall z, (z < NFIX)%nat -> z <> RB4 -> getbn z s7 = getbn z sm).
  { intros z Hz Hz4. apply (keeps_get _ _ _ _ z K7); [lia|]. intros [E|[]]. apply Hz4. rewrite E. reflexivity. }

  eapply (@gwp_step ptr unit _ F6 (BN_mod_exp_simple ops RB5 RB1 RB2 RB3)); [exact Hs7|exact Hf7|exact Ho7|apply (BN_mod_exp_simple_spec RB5 RB1 RB2 RB3 F6 s7); [|unfold RB3, NFIX; lia]|].
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

End TopA.
