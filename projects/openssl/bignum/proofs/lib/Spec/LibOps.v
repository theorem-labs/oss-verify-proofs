(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import ITree Nodes Decode Ceiling.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import Prelim Monad MSafe STree Malloc MallocCtrl Driver Prog
  MI_Inv MI_Cnt LB_Tables LB_Inv LB_Sum LB_Logic LB_StmtA LB_Raw LB_Alloc LB_PTarget LibProg LibSafe.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition LRs (T : list Z) (c : Z) : Z := zcount (fun n => negb (MMAP_THRESHOLD <=? n) && (size_to_class n =? c)) T.
Definition n63s (T : list Z) : Z := zcount (fun n => MMAP_THRESHOLD <=? n) T.
Definition R63s (T : list Z) : Z := zsum (map (fun n => if MMAP_THRESHOLD <=? n then round_up_pg (n + IB + UNIT) else 0) T).

Lemma zcount_map' {A B} (f : A -> B) (p : B -> bool) l : zcount p (map f l) = zcount (fun x => p (f x)) l.
Proof. induction l as [|x l IH]; [reflexivity|]. cbn [map]. rewrite !zcount_cons, IH. reflexivity. Qed.

Lemma LRX_sizes (X : list (bptr * Z)) c : LRX X c = LRs (map snd X) c.
Proof. unfold LRX, LRs. rewrite zcount_map'. reflexivity. Qed.
Lemma n63X_sizes (X : list (bptr * Z)) : n63X X = n63s (map snd X).
Proof. unfold n63X, n63s. rewrite zcount_map'. reflexivity. Qed.
Lemma R63X_sizes (X : list (bptr * Z)) : R63X X = R63s (map snd X).
Proof. unfold R63X, R63s. rewrite map_map. reflexivity. Qed.

Definition subms (A B : list Z) : Prop := exists R, Permutation (A ++ R) B.

Lemma subms_nil B : subms [] B.
Proof. exists B. apply Permutation_refl. Qed.
Lemma subms_perm_l A A' B : Permutation A A' -> subms A B -> subms A' B.
Proof. intros HP [R HR]. exists R. etransitivity; [|exact HR]. apply Permutation_app_tail. apply Permutation_sym. exact HP. Qed.
Lemma subms_drop a A B : subms (a :: A) B -> subms A B.
Proof. intros [R HR]. exists (a :: R). etransitivity; [|exact HR]. apply Permutation_sym. apply Permutation_middle. Qed.
Lemma subms_app_r A B C : subms A B -> subms A (B ++ C).
Proof. intros [R HR]. exists (R ++ C). rewrite app_assoc. apply Permutation_app_tail. exact HR. Qed.
Lemma subms_snoc A B n : subms A B -> subms (n :: A) (B ++ [n]).
Proof.
  intros [R HR]. exists R. cbn [app]. etransitivity; [|apply Permutation_cons_append]. apply perm_skip. exact HR.
Qed.

Lemma R63s_term_nonneg n : 0 <= (if MMAP_THRESHOLD <=? n then round_up_pg (n + IB + UNIT) else 0).
Proof.
  destruct (Z.leb_spec MMAP_THRESHOLD n); [|lia]. pose proof (round_up_pg_spec (n + IB + UNIT)). unfold MMAP_THRESHOLD, IB, UNIT in *. lia.
Qed.

Lemma subms_LRs A B c : subms A B -> LRs A c <= LRs B c.
Proof. intros [R HR]. unfold LRs. rewrite <- (zcount_perm _ _ _ HR), zcount_app. pose proof (zcount_nonneg (fun n => negb (MMAP_THRESHOLD <=? n) && (size_to_class n =? c)) R). lia. Qed.
Lemma subms_n63s A B : subms A B -> n63s A <= n63s B.
Proof. intros [R HR]. unfold n63s. rewrite <- (zcount_perm _ _ _ HR), zcount_app. pose proof (zcount_nonneg (fun n => MMAP_THRESHOLD <=? n) R). lia. Qed.
Lemma subms_R63s A B : subms A B -> R63s A <= R63s B.
Proof.
  intros [R HR]. unfold R63s. rewrite <- (zsum_map_perm _ _ _ HR), map_app, zsum_app.
  assert (0 <= zsum (map (fun n => if MMAP_THRESHOLD <=? n then round_up_pg (n + IB + UNIT) else 0) R)); [|lia].
  apply zsum_map_nonneg. intros x _. apply R63s_term_nonneg.
Qed.

Definition DRV_BIG : Z := MAX_INPUT + 1 + IB + UNIT + 4096.

Section Caps.
Context {CE__ : Ceiling}.
Variable P : Z -> Z.

Definition libfit (L : list (bptr * Z)) : Prop :=
  (forall c, 0 <= c < 48 -> LRX L c + 5 <= P c) /\ n63X L + 5 <= P 63 /\ PHI P + R63X L + 5 * DRV_BIG <= LBUDGET.

Lemma LRX_app X Y c : LRX (X ++ Y) c = LRX X c + LRX Y c.
Proof. unfold LRX. apply zcount_app. Qed.
Lemma n63X_app X Y : n63X (X ++ Y) = n63X X + n63X Y.
Proof. unfold n63X. apply zcount_app. Qed.
Lemma R63X_app X Y : R63X (X ++ Y) = R63X X + R63X Y.
Proof. unfold R63X. rewrite map_app. apply zsum_app. Qed.
Lemma LRX_le_zlen (X : list (bptr * Z)) c : LRX X c <= zlen X.
Proof. unfold LRX. apply zcount_le_len. Qed.
Lemma n63X_le_zlen (X : list (bptr * Z)) : n63X X <= zlen X.
Proof. unfold n63X. apply zcount_le_len. Qed.

Lemma bigb_le' n : 0 <= n -> bigb n <= n + IB + UNIT + 4096.
Proof.
  intros Hn. unfold bigb. destruct (MMAP_THRESHOLD <=? n); [| unfold IB, UNIT; lia].
  pose proof (round_up_pg_spec (n + IB + UNIT)) as [[_ H] _]. lia.
Qed.

Definition szle (B : Z) (X : list (bptr * Z)) : Prop := Forall (fun xb => 0 <= snd xb <= B) X.

Lemma R63X_szle B X : 0 <= B -> szle B X -> R63X X <= zlen X * (B + IB + UNIT + 4096).
Proof.
  intros HB. induction X as [|[p n] X IH]; intros SX.
  - unfold R63X, zsum, zlen. cbn. lia.
  - rewrite R63X_cons. inversion SX as [|x l Hx HX]; subst. cbn [snd] in Hx. specialize (IH HX).
    pose proof (bigb_le' n ltac:(lia)). unfold zlen in *. cbn [length]. rewrite Nat2Z.inj_succ. unfold IB, UNIT in *. nia.
Qed.

Lemma libfit_drv : forall L D n, libfit L -> (length D <= 4)%nat -> szle (MAX_INPUT + 1) D -> 0 <= n <= MAX_INPUT + 1 ->
  mal_okP P (L ++ D) n.
Proof.
  intros L D n (F1 & F2 & F3) HD SD Hn. assert (HzD : zlen D <= 4) by (unfold zlen; lia).
  split; [split|].
  - intros Hsm. destruct (size_to_class_ok n ltac:(lia)) as [Hc _]. rewrite LRX_app.
    pose proof (F1 _ Hc). pose proof (LRX_le_zlen D (size_to_class n)). lia.
  - intros _. rewrite n63X_app. pose proof (n63X_le_zlen D). lia.
  - rewrite R63X_app. pose proof (R63X_szle (MAX_INPUT + 1) D ltac:(unfold MAX_INPUT; lia) SD) as HR.
    pose proof (bigb_le' n ltac:(lia)). unfold DRV_BIG in *. unfold IB, UNIT, MAX_INPUT in *. nia.
Qed.

Lemma libfit_lib : forall L D q n, libfit ((q, n) :: L) -> (length D <= 4)%nat -> szle (MAX_INPUT + 1) D -> 0 <= n ->
  mal_okP P (L ++ D) n.
Proof.
  intros L D q n (F1 & F2 & F3) HD SD Hn. assert (HzD : zlen D <= 4) by (unfold zlen; lia).
  rewrite R63X_cons in F3.
  split; [split|].
  - intros Hsm. destruct (size_to_class_ok n ltac:(lia)) as [Hc _]. rewrite LRX_app.
    pose proof (F1 _ Hc) as F1c. unfold LRX in F1c. rewrite zcount_cons in F1c. cbn [snd] in F1c.
    destruct (Z.leb_spec MMAP_THRESHOLD n); [lia|]. rewrite Z.eqb_refl in F1c. cbn [negb andb] in F1c.
    pose proof (LRX_le_zlen D (size_to_class n)). unfold LRX in *. lia.
  - intros Hbig. rewrite n63X_app. unfold n63X in F2. rewrite zcount_cons in F2. cbn [snd] in F2.
    destruct (Z.leb_spec MMAP_THRESHOLD n); [|lia]. pose proof (n63X_le_zlen D). unfold n63X in *. lia.
  - rewrite R63X_app. pose proof (R63X_szle (MAX_INPUT + 1) D ltac:(unfold MAX_INPUT; lia) SD) as HR.
    unfold DRV_BIG in *. unfold IB, UNIT, MAX_INPUT in *. nia.
Qed.

Lemma libfit_perm : forall L L', Permutation L L' -> libfit L -> libfit L'.
Proof.
  intros L L' HP (F1 & F2 & F3). unfold libfit, LRX, n63X, R63X in *.
  split; [|split].
  - intros c Hc. rewrite <- (zcount_perm _ _ _ HP). apply F1. exact Hc.
  - rewrite <- (zcount_perm _ _ _ HP). exact F2.
  - rewrite <- (zsum_map_perm _ _ _ HP). exact F3.
Qed.

Variable T : list Z.
Variables NBLK BSZ : Z.

Definition caps_ok : Prop :=
  0 <= NBLK /\ 0 <= BSZ
  /\ (forall c, 0 <= c < 48 -> LRs T c + NBLK + 5 <= P c) /\ n63s T + NBLK + 5 <= P 63
  /\ PHI P + R63s T + NBLK * (BSZ + IB + UNIT + 4096) + 5 * DRV_BIG <= LBUDGET.

Definition caps_ok_b : bool :=
  (0 <=? NBLK) && (0 <=? BSZ)
  && forallb (fun c => LRs T c + NBLK + 5 <=? P c) (zrange 0 48)
  && (n63s T + NBLK + 5 <=? P 63)
  && (PHI P + R63s T + NBLK * (BSZ + IB + UNIT + 4096) + 5 * DRV_BIG <=? LBUDGET).

Lemma caps_ok_b_ok : caps_ok_b = true -> caps_ok.
Proof.
  unfold caps_ok_b, caps_ok. intros H.
  apply andb_prop in H as [H H5]. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.leb_le in H1, H2, H4, H5. repeat (split; [assumption|]). split; [|split; assumption].
  intros c Hc. pose proof (forallb_zrange _ 0 48 c H3 ltac:(lia) ltac:(lia)) as Hf. cbn beta in Hf. apply Z.leb_le in Hf. exact Hf.
Qed.

Hypothesis HC : caps_ok.

Lemma libfit_of_prof : forall L Xb Li,
  Permutation L (Xb ++ Li) -> zlen Xb <= NBLK -> szle BSZ Xb -> subms (map snd Li) T -> libfit L.
Proof.
  intros L Xb Li HP HL SX HS. apply (libfit_perm (Xb ++ Li) L (Permutation_sym HP)).
  destruct HC as (HN & HB & C1 & C2 & C3).
  split; [|split].
  - intros c Hc. rewrite LRX_app, (LRX_sizes Li). pose proof (subms_LRs _ _ c HS). pose proof (LRX_le_zlen Xb c). specialize (C1 c Hc). lia.
  - rewrite n63X_app, (n63X_sizes Li). pose proof (subms_n63s _ _ HS). pose proof (n63X_le_zlen Xb). lia.
  - rewrite R63X_app, (R63X_sizes Li). pose proof (subms_R63s _ _ HS). pose proof (R63X_szle BSZ Xb HB SX).
    assert (zlen Xb * (BSZ + IB + UNIT + 4096) <= NBLK * (BSZ + IB + UNIT + 4096)) by (apply Z.mul_le_mono_nonneg_r; unfold IB, UNIT; lia).
    lia.
Qed.

Lemma libfit_nil : libfit [].
Proof.
  apply (libfit_of_prof [] [] []); [apply Permutation_refl| unfold zlen; cbn; destruct HC; lia| constructor| apply subms_nil].
Qed.

Definition okT (X : list (bptr * Z)) (n : Z) : Prop := subms (n :: map snd X) T.

Definition okB (X : list (bptr * Z)) (n : Z) : Prop := zlen X < NBLK /\ 0 <= n <= BSZ /\ szle BSZ X.

Lemma okT_mal_ok : forall D X n, (length D <= 4)%nat -> szle (MAX_INPUT + 1) D -> 0 <= n -> okT X n ->
  mal_okP P (X ++ D) n.
Proof.
  intros D X n HD SD Hn Hok. apply (libfit_lib X D ((0%N, 0), 0) n); [|exact HD| exact SD| exact Hn].
  apply (libfit_of_prof _ [] (((0%N, 0), 0, n) :: X)); [apply Permutation_refl| unfold zlen; cbn; destruct HC; lia| constructor| exact Hok].
Qed.

Lemma okB_mal_ok : forall D Li X n, (length D <= 4)%nat -> szle (MAX_INPUT + 1) D -> subms (map snd Li) T -> okB X n ->
  mal_okP P (X ++ (Li ++ D)) n.
Proof.
  intros D Li X n HD SD HS (HL & Hn & SX). rewrite app_assoc.
  apply (libfit_lib (X ++ Li) D ((0%N, 0), 0) n); [|exact HD| exact SD| lia].
  apply (libfit_of_prof _ (((0%N, 0), 0, n) :: X) Li); [apply Permutation_refl| | |exact HS].
  - unfold zlen in *. cbn [length]. lia.
  - constructor; [cbn [snd]; lia| exact SX].
Qed.

End Caps.

Definition sizes_of (ops : list lop) : list Z :=
  concat (map (fun o => match o with OpMalloc n => [n] | OpFree _ => [] | OpRealloc _ n => [n] end) ops).

Definition senv : Type := list (option Z).
Definition senv_of (env : lenv) : senv := map (option_map snd) env.

Definition size_in_range (n : Z) : bool := (0 <=? n) && (n <? 2^62).

Fixpoint ops_wf (ops : list lop) (se : senv) : bool :=
  match ops with
  | [] => true
  | OpMalloc n :: ops' => size_in_range n && ops_wf ops' (se ++ [Some n])
  | OpFree k :: ops' => match nth k se None with Some _ => ops_wf ops' (set_nth k None se) | None => false end
  | OpRealloc k n :: ops' =>
      match nth k se None with
      | Some m => size_in_range n && realloc_crit_b m n && ops_wf ops' (set_nth k None se ++ [Some n])
      | None => false
      end
  end.

Lemma size_in_range_ok n : size_in_range n = true -> 0 <= n < 2^62.
Proof. unfold size_in_range. intros H. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia. Qed.

Lemma senv_of_app env x : senv_of (env ++ [x]) = senv_of env ++ [option_map snd x].
Proof. unfold senv_of. rewrite map_app. reflexivity. Qed.

Lemma set_nth_map {A B} (f : A -> B) k x (l : list A) : map f (set_nth k x l) = set_nth k (f x) (map f l).
Proof. revert k. induction l as [|y l IH]; intros [|k]; cbn; try reflexivity. rewrite IH. reflexivity. Qed.

Lemma senv_of_set_nth env k : senv_of (set_nth k None env) = set_nth k None (senv_of env).
Proof. unfold senv_of. rewrite set_nth_map. reflexivity. Qed.

Lemma nth_senv_of env k : nth k (senv_of env) None = option_map snd (nth k env None).
Proof. unfold senv_of. change (@None Z) with (option_map (@snd bptr Z) None). apply map_nth. Qed.

Lemma live_env_app env env' : live_env (env ++ env') = live_env env ++ live_env env'.
Proof. induction env as [|[b|] env IH]; cbn [live_env app]; [reflexivity| rewrite IH; reflexivity| exact IH]. Qed.

Lemma live_env_set_nth : forall env k b, nth k env None = Some b ->
  Permutation (live_env env) (b :: live_env (set_nth k None env)).
Proof.
  induction env as [|x env IH]; intros [|k] b H; cbn [nth] in H; try discriminate.
  - subst x. cbn [set_nth live_env]. apply Permutation_refl.
  - cbn [set_nth]. destruct x as [b'|]; cbn [live_env].
    + etransitivity; [apply perm_skip; apply (IH k b H)| apply perm_swap].
    + apply (IH k b H).
Qed.

Section OpsLwf.
Theorem run_ops_lwf : forall ops env Tpre X,
  ops_wf ops (senv_of env) = true ->
  Permutation X (live_env env) ->
  subms (map snd X) Tpre ->
  lwf (okT (Tpre ++ sizes_of ops)) (run_ops ops env) X
      (fun env' X' => Permutation X' (live_env env') /\ subms (map snd X') (Tpre ++ sizes_of ops)).
Proof.
  induction ops as [|o ops IH]; intros env Tpre X Hwf HX HS.
  - cbn [run_ops lwf sizes_of map concat]. rewrite app_nil_r. split; assumption.
  - destruct o as [n|k|k n]; cbn [ops_wf] in Hwf.
    +
      apply andb_prop in Hwf as [Hn Hwf]. apply size_in_range_ok in Hn.
      assert (ET : Tpre ++ sizes_of (OpMalloc n :: ops) = (Tpre ++ [n]) ++ sizes_of ops).
      { unfold sizes_of. cbn [map concat]. rewrite <- app_assoc. reflexivity. }
      cbn [run_ops lwf]. split; [exact Hn|]. split; [|split; [reflexivity|]].
      * unfold okT. rewrite ET. apply subms_app_r. apply subms_snoc. exact HS.
      * intros p Hp. rewrite ET. apply IH.
        -- rewrite senv_of_app. exact Hwf.
        -- rewrite live_env_app. cbn [live_env]. etransitivity; [apply perm_skip; exact HX| apply Permutation_cons_append].
        -- cbn [map snd]. apply subms_snoc. exact HS.
    +
      rewrite nth_senv_of in Hwf. cbn [run_ops]. destruct (nth k env None) as [[p m]|] eqn:Ek; cbn [option_map] in Hwf; [|discriminate].
      cbn [lwf]. exists m, (live_env (set_nth k None env)). split.
      * etransitivity; [exact HX| apply (live_env_set_nth env k _ Ek)].
      * assert (ET : Tpre ++ sizes_of (OpFree k :: ops) = Tpre ++ sizes_of ops) by (unfold sizes_of; cbn [map concat app]; reflexivity).
        rewrite ET. apply IH; [rewrite senv_of_set_nth; exact Hwf| apply Permutation_refl|].
        apply (subms_drop m). apply (subms_perm_l (map snd X)); [|exact HS].
        change (m :: map snd (live_env (set_nth k None env))) with (map snd ((p, m) :: live_env (set_nth k None env))).
        apply Permutation_map. etransitivity; [exact HX| apply (live_env_set_nth env k _ Ek)].
    +
      rewrite nth_senv_of in Hwf. cbn [run_ops]. destruct (nth k env None) as [[p m]|] eqn:Ek; cbn [option_map snd] in Hwf; [|discriminate].
      apply andb_prop in Hwf as [Hwf Hwf3]. apply andb_prop in Hwf as [Hn Hc]. apply size_in_range_ok in Hn. apply realloc_crit_b_ok in Hc.
      assert (ET : Tpre ++ sizes_of (OpRealloc k n :: ops) = (Tpre ++ [n]) ++ sizes_of ops).
      { unfold sizes_of. cbn [map concat]. rewrite <- app_assoc. reflexivity. }
      assert (HXp : Permutation X ((p, m) :: live_env (set_nth k None env))).
      { etransitivity; [exact HX| apply (live_env_set_nth env k _ Ek)]. }
      cbn [lwf]. exists m, (live_env (set_nth k None env)).
      split; [exact HXp|]. split; [exact Hn|]. split; [exact Hc|]. split; [|split; [reflexivity|]].
      * unfold okT. rewrite ET. apply subms_app_r. apply subms_snoc. exact HS.
      * intros q Hq. rewrite ET. apply IH.
        -- rewrite senv_of_app, senv_of_set_nth. exact Hwf3.
        -- rewrite live_env_app. cbn [live_env]. apply Permutation_cons_append.
        -- cbn [map snd]. apply subms_snoc. apply (subms_drop m). apply (subms_perm_l (map snd X)); [|exact HS].
           change (m :: map snd (live_env (set_nth k None env))) with (map snd ((p, m) :: live_env (set_nth k None env))).
           apply Permutation_map. exact HXp.
Qed.

Corollary run_ops_lwf0 : forall ops,
  ops_wf ops [] = true ->
  lwf (okT (sizes_of ops)) (run_ops ops []) []
      (fun env' X' => Permutation X' (live_env env') /\ subms (map snd X') (sizes_of ops)).
Proof.
  intros ops H. apply (run_ops_lwf ops [] [] []); [exact H| apply Permutation_refl| apply subms_nil].
Qed.
End OpsLwf.

Definition init_of_ops {LSt : Type} (ops : list lop) (ls0 : LSt) : lprog LSt :=
  lbind (run_ops ops []) (fun _ => LRet ls0).

Lemma init_of_ops_lwf : forall {LSt : Type} (ops : list lop) (ls0 : LSt),
  ops_wf ops [] = true ->
  lwf (okT (sizes_of ops)) (init_of_ops ops ls0) []
      (fun ls Li => ls = ls0 /\ subms (map snd Li) (sizes_of ops)).
Proof.
  intros LSt ops ls0 H. unfold init_of_ops. apply lwf_bind.
  eapply lwf_mono; [apply (run_ops_lwf0 ops H)|]. intros env X' [_ HS]. cbn [lwf]. split; [reflexivity| exact HS].
Qed.
