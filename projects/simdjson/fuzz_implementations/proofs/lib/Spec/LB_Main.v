(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import ITree Nodes Decode Image.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim Monad MSafe Stdio Malloc STree SjModel ImpModel Target Driver Prog KInv KStep Relim ModelInv
  MI_Inv MI_Cnt LB_Tables LB_Inv LB_Sum LB_Logic LB_StmtA LB_Raw LB_Init LB_WMalloc LB_Alloc LB_PDriver LB_PTarget.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Unforced.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).

From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Ceiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section WithCeiling. Context {CE__ : Ceiling}.

Definition Pstat (c : Z) : Z := 13.

Lemma Pstat_nonneg : forall c, 0 <= Pstat c.
Proof. intros; unfold Pstat; lia. Qed.

Lemma PHI_Pstat_val : PHI Pstat = ltac:(let v := eval vm_compute in (PHI Pstat) in exact v).
Proof. vm_compute. reflexivity. Qed.

Lemma PHI_Pstat : PHI Pstat + 5 * (MAX_INPUT + 1 + IB + UNIT + 4096) <= LBUDGET.
Proof. rewrite PHI_Pstat_val. vm_compute. discriminate. Qed.

Definition mal_okQ (X : list (bptr * Z)) (n : Z) : Prop :=
  ROOMX X Pstat n /\ PHI Pstat + R63X X + bigb n <= LBUDGET.

Lemma bigb_le n : 0 <= n -> bigb n <= n + IB + UNIT + 4096.
Proof.
  intros Hn. unfold bigb. destruct (MMAP_THRESHOLD <=? n); [| unfold IB, UNIT; lia].
  pose proof (round_up_pg_spec (n + IB + UNIT)) as [[_ H] _]. lia.
Qed.

Lemma R63X_small X : smallX X -> R63X X <= zlen X * (MAX_INPUT + 1 + IB + UNIT + 4096).
Proof.
  induction X as [|[p n] X IH]; intros SX.
  - unfold R63X, zsum, zlen. cbn. lia.
  - rewrite R63X_cons. inversion SX as [|x l Hx HX]; subst. cbn [snd] in Hx. specialize (IH HX).
    pose proof (bigb_le n ltac:(lia)). unfold zlen in *. cbn [length]. rewrite Nat2Z.inj_succ. unfold IB, UNIT in *. lia.
Qed.

Lemma LRX_le_len X c : LRX X c <= zlen X.
Proof. unfold LRX. apply zcount_le_len. Qed.
Lemma n63X_le_len X : n63X X <= zlen X.
Proof. unfold n63X. apply zcount_le_len. Qed.

Lemma OK_small : forall X n, (length X <= 4)%nat -> smallX X -> 0 <= n <= MAX_INPUT + 1 -> mal_okQ X n.
Proof.
  intros X n HL SX Hn. assert (HzL : zlen X <= 4) by (unfold zlen; lia).
  pose proof (LRX_le_len X (size_to_class n)). pose proof (n63X_le_len X).
  split.
  - split; intros _; unfold Pstat; lia.
  - pose proof (R63X_small X SX). pose proof (bigb_le n ltac:(lia)). pose proof PHI_Pstat.
    pose proof (R63X_nonneg X). unfold IB, UNIT, MAX_INPUT in *. nia.
Qed.

Lemma R63X_sum X : nonnegX X -> R63X X <= sumX X + zlen X * (IB + UNIT + 4096).
Proof.
  induction X as [|[p n] X IH]; intros NX.
  - unfold R63X, zsum, zlen. cbn. lia.
  - rewrite R63X_cons. inversion NX as [|x l Hx HX]; subst. cbn [snd] in Hx. specialize (IH HX).
    pose proof (bigb_le n Hx). unfold zlen in *. cbn [length sumX snd]. rewrite Nat2Z.inj_succ. unfold IB, UNIT in *. lia.
Qed.

Lemma OK_sj : forall X n, (length X <= 12)%nat -> nonnegX X -> 0 <= n -> sumX X + n <= TGT_TOTAL -> mal_okQ X n.
Proof.
  intros X n HL NX Hn HS. assert (HzL : zlen X <= 12) by (unfold zlen; lia).
  pose proof (LRX_le_len X (size_to_class n)). pose proof (n63X_le_len X).
  split.
  - split; intros _; unfold Pstat; lia.
  - pose proof (R63X_sum X NX). pose proof (bigb_le n Hn). pose proof PHI_Pstat_val as HV. rewrite HV.
    pose proof (R63X_nonneg X). unfold IB, UNIT, TGT_TOTAL, LBUDGET in *. lia.
Qed.

Lemma OK_first : mal_okQ [] 65536.
Proof. apply OK_small; [cbn; lia| constructor| unfold MAX_INPUT; lia]. Qed.

Lemma OK_grow : forall b k, (k <= 9)%nat -> mal_okQ [(b, 65536 * 2 ^ Z.of_nat k)] (65536 * 2 ^ Z.of_nat k * 2).
Proof.
  intros b k Hk. assert (Hp1 : 0 < 2 ^ Z.of_nat k) by (apply Z.pow_pos_nonneg; lia).
  assert (Hp2 : 2 ^ Z.of_nat k <= 2 ^ 9) by (apply Z.pow_le_mono_r; lia). change (2 ^ 9) with 512 in Hp2.
  apply OK_small; [cbn; lia| |unfold MAX_INPUT; lia].
  constructor; [cbn [snd]; unfold MAX_INPUT; lia| constructor].
Qed.

Local Notation QIX := (fun X => QI X Pstat).

Lemma QI_minv' : forall X s mo, QI X Pstat s mo -> minv mo /\ m_halted mo = None.
Proof. intros X s mo H. exact (QI_minv _ _ _ _ H). Qed.
Lemma QI_fds' : forall X s mo mo', QI X Pstat s mo -> m_vmmaps mo' = m_vmmaps mo -> minv mo' -> m_halted mo' = None -> QI X Pstat s mo'.
Proof. intros X s mo mo' H. exact (QI_fds _ _ _ _ _ H). Qed.
Lemma QI_live' : forall X s mo, QI X Pstat s mo -> live mo <= LBUDGET.
Proof. intros X s mo H. exact (QI_live _ _ _ _ H). Qed.

Lemma writev_LQ X fd bufs (dec : resp -> option Z) : mspecL LBUDGET (QI X Pstat) (msys (NWritev fd bufs) dec) (fun _ => QI X Pstat).
Proof. apply (writev_L LBUDGET (QI X Pstat) (QI_live' X)). Qed.
Lemma ioctl_LQ X fd req : mspecL LBUDGET (QI X Pstat) (msys (NIoctl fd req) dec_ioctl) (fun _ => QI X Pstat).
Proof. apply (ioctl_L LBUDGET (QI X Pstat) (QI_live' X)). Qed.
Lemma QI_set_so' X : forall s mo v, QI X Pstat s mo -> QI X Pstat (set_so_ps v s) mo.
Proof. intros s mo v H. apply QI_set_so. exact H. Qed.

Lemma err_LQ : forall X ps, mspecL LBUDGET (QI X Pstat) (stderr_fprintf ps) (fun _ => QI X Pstat).
Proof. intros X ps. apply (stderr_fprintf_L LBUDGET (QI X Pstat) (writev_LQ X)). Qed.
Lemma out_LQ : forall X ps, mspecL LBUDGET (QI X Pstat) (stdout_vprintf ps_so set_so_ps ps) (fun _ => QI X Pstat).
Proof. intros X ps. apply (stdout_vprintf_L ps_so set_so_ps LBUDGET (QI X Pstat) (QI_set_so' X) (writev_LQ X) (ioctl_LQ X)). Qed.
Lemma diag_LQ : forall X d, mspecL LBUDGET (QI X Pstat) (io_diag io d) (fun _ => QI X Pstat).
Proof. intros X d. unfold io, io_S. cbn [io_diag]. apply (s_diag_L LBUDGET (QI X Pstat) (writev_LQ X)). Qed.
Lemma exitio_LQ : forall X, mspecL LBUDGET (QI X Pstat) (io_exit io) (fun _ => QI X Pstat).
Proof. intros X. unfold io, io_S. cbn [io_exit]. apply (stdout_exit_flush_L ps_so set_so_ps LBUDGET (QI X Pstat) (QI_set_so' X) (writev_LQ X) (ioctl_LQ X)). Qed.

Lemma raw_malloc_LQ' : forall X n, 0 <= n ->
  mspecL LBUDGET (fun s mo => QI X Pstat s mo /\ mal_okQ X n) (raw_malloc n)
         (fun r s mo => match r with Some p => QI ((p, n) :: X) Pstat s mo /\ n < 2^63 | None => QI X Pstat s mo end).
Proof. intros X n Hn. exact (raw_malloc_LQ X Pstat n Hn). Qed.
Lemma raw_free_LQ' : forall X p n, mspecL LBUDGET (QI ((p, n) :: X) Pstat) (raw_free p) (fun _ => QI X Pstat).
Proof. intros X p n. exact (raw_free_LQ X Pstat p n). Qed.
Lemma QI_perm' : forall X Y s mo, Permutation X Y -> QI X Pstat s mo -> QI Y Pstat s mo.
Proof. intros X Y s mo HP. apply QI_perm. exact HP. Qed.

Fixpoint tall {R} (P : R -> Prop) (t : itree node (exc R)) : Prop :=
  match t with
  | Ret Unr => True
  | Ret (Ok r) => P r
  | Vis _ k => forall rsp, tall P (k rsp)
  | Cho k => forall z, tall P (k z)
  end.
Lemma tall_mono : forall {R} (P P' : R -> Prop) t, tall P t -> (forall r, P r -> P' r) -> tall P' t.
Proof.
  induction t as [[|r]|n k IH|kc IHc]; cbn; intros H HP.
  - exact I.
  - apply HP. exact H.
  - intros rsp. eapply IH; [apply H| exact HP].
  - intros z. eapply IHc; [apply H| exact HP].
Qed.
Lemma tall_ebind : forall {A B} (P : A -> Prop) (Q : B -> Prop) (t : itree node (exc A)) (f : A -> itree node (exc B)),
  tall P t -> (forall a, P a -> tall Q (f a)) -> tall Q (ebind t f).
Proof.
  induction t as [[|a]|n k IH|kc IHc]; cbn; intros f H HF; [exact I| apply HF; exact H| |intros z; apply IHc; [apply H| exact HF]].
  intros rsp. apply IH; [apply H| exact HF].
Qed.
Lemma twl_tall : forall {R} B (t : itree node (exc R)) mo (P : exc R -> Model -> Prop) (T : R -> Prop),
  twl B t mo P -> tall T t -> twl B t mo (fun r mo1 => P r mo1 /\ match r with Ok a => T a | _ => True end).
Proof.
  intros R B t. induction t as [[|r]|n k IH|kc IHc]; cbn; intros mo P T H HT.
  - split; [exact H| exact I].
  - split; [exact H| exact HT].
  - destruct H as [Hs Hk]. split; [exact Hs|]. intros rsp mo' evs Hst. destruct (Hk rsp mo' evs Hst) as [HB Hk']. split; [exact HB|].
    apply IH; [exact Hk'| apply HT].
  - intros z. apply IHc; [apply H| apply HT].
Qed.
Section Keeps.
  Context {B : Type} (f : PState -> B).
  Definition keeps {A} (c : Monad.M PState A) : Prop := forall s, tall (fun p => f (snd p) = f s) (c s).
  Lemma keeps_ret : forall {A} (a : A), keeps (mret a).
  Proof. intros A a s. reflexivity. Qed.
  Lemma keeps_unr : forall {A}, keeps (munr (A:=A)).
  Proof. intros A s. exact I. Qed.
  Lemma keeps_get : keeps mget.
  Proof. intros s. reflexivity. Qed.
  Lemma keeps_upd : forall g, (forall s, f (g s) = f s) -> keeps (mupd g).
  Proof. intros g Hg s. cbn. apply Hg. Qed.
  Lemma keeps_sys : forall {A} n (dec : resp -> option A), keeps (msys n dec).
  Proof. intros A n dec s. cbn. intros rsp. destruct (dec rsp); cbn; [reflexivity| exact I]. Qed.
  Lemma keeps_bind : forall {A C} (m : Monad.M PState A) (k : A -> Monad.M PState C), keeps m -> (forall a, keeps (k a)) -> keeps (mbind m k).
  Proof.
    intros A C m k Hm Hk s. unfold mbind. eapply tall_ebind; [apply Hm|]. cbn. intros [a s1] E. cbn in E.
    eapply tall_mono; [apply Hk|]. cbn. intros [c s2] E2. cbn in E2 |- *. congruence.
  Qed.
  Lemma keeps_getk : forall {C} (k : PState -> Monad.M PState C), (forall s0, keeps (k s0)) -> keeps (mbind mget k).
  Proof. intros C k Hk s. unfold mbind, mget. cbn. apply Hk. Qed.
  Lemma keeps_if : forall {A} (b : bool) (m1 m2 : Monad.M PState A), keeps m1 -> keeps m2 -> keeps (if b then m1 else m2).
  Proof. intros A [|] m1 m2 H1 H2; assumption. Qed.
  Lemma keeps_loop : forall {X R} fuel (body : X -> Monad.M PState (X + R)),
    (forall x, keeps (body x)) -> forall x, keeps (mloop fuel body x).
  Proof.
    induction fuel as [|fuel IH]; intros body HB x; cbn; [apply keeps_unr|].
    apply keeps_bind; [apply HB|]. intros [x'|r]; [apply IH; exact HB| apply keeps_ret].
  Qed.
End Keeps.
Arguments keeps {B} f {A} c.

Lemma keeps_x_ev_step : forall e, keeps ps_x (ev_step e).
Proof.
  intros e. destruct e; cbn [ev_step].
  - apply keeps_if.
    + apply keeps_bind; [apply keeps_sys|]. intros r. apply keeps_bind; [apply keeps_upd; intros [? ? ? ? ?]; reflexivity|]. intros _. apply keeps_ret.
    + apply keeps_getk. intros s0. apply keeps_bind; [apply keeps_sys|]. intros [|]; [| apply keeps_ret].
      apply keeps_bind; [apply keeps_upd; intros [? ? ? ? ?]; reflexivity|]. intros _. apply keeps_ret.
  - apply keeps_if; [| apply keeps_if]; (apply keeps_bind; [apply keeps_sys|]; intros a; apply keeps_ret).
  - apply keeps_bind; [apply keeps_sys|]. intros a. apply keeps_ret.
  - apply keeps_bind; [apply keeps_sys|]. intros a. apply keeps_ret.
  - apply keeps_unr.
  - apply keeps_unr.
Qed.
Lemma keeps_x_membed : forall {R} (t : stree ev Z R), keeps ps_x (membed t).
Proof.
  intros R t. induction t as [r|e k IH]; cbn [membed]; [apply keeps_ret|].
  apply keeps_bind; [apply keeps_x_ev_step| intros z; apply IH].
Qed.
Lemma keeps_x_raw_free : forall p, keeps ps_x (raw_free p).
Proof.
  intros p. unfold raw_free. apply keeps_getk. intros s0. apply keeps_bind; [apply keeps_x_membed|]. intros st'.
  apply keeps_upd. intros [? ? ? ? ?]; reflexivity.
Qed.
Lemma keeps_x_raw_malloc : forall n, keeps ps_x (raw_malloc n).
Proof.
  intros n. unfold raw_malloc. apply keeps_getk. intros s0. apply keeps_bind; [apply keeps_x_membed|]. intros [st' p].
  apply keeps_bind; [apply keeps_upd; intros [? ? ? ? ?]; reflexivity|]. intros _. apply keeps_ret.
Qed.
Lemma keeps_x_stdio_writev : forall fd buf bs, keeps ps_x (stdio_writev (St:=PState) fd buf bs).
Proof.
  intros fd buf bs. unfold stdio_writev. apply keeps_loop. intros x. unfold wv_body.
  apply keeps_bind; [apply keeps_sys|]. intros k. apply keeps_if; apply keeps_ret.
Qed.
Lemma keeps_x_stderr_pieces : forall ps buf, keeps ps_x (stderr_pieces (St:=PState) buf ps).
Proof.
  induction ps as [|p ps IH]; intros buf; cbn [stderr_pieces]; [apply keeps_ret|].
  apply keeps_if; [| apply IH]. apply keeps_bind; [apply keeps_x_stdio_writev|]. intros _. apply IH.
Qed.
Lemma keeps_x_s_diag : forall d, keeps ps_x (s_diag (St:=PState) d).
Proof.
  intros d. unfold s_diag. destruct d; unfold stderr_fprintf, stderr_fwrite;
  try (apply keeps_bind; [apply keeps_x_stderr_pieces| intros buf; apply keeps_x_stdio_writev]);
  (apply keeps_if; [apply keeps_x_stdio_writev| apply keeps_ret]).
Qed.
Lemma keeps_x_startup : keeps ps_x startup.
Proof. unfold startup. apply keeps_bind; [apply keeps_sys|]. intros _. apply keeps_ret. Qed.

Lemma mspecL_keeps : forall {A C} (f : PState -> C) (c : Monad.M PState A) (P : assn PState) (Q : A -> assn PState) (v : C),
  keeps f c -> mspecL LBUDGET P c Q -> mspecL LBUDGET (fun s mo => P s mo /\ f s = v) c (fun r s mo => Q r s mo /\ f s = v).
Proof.
  intros A C f c P Q v K H s mo [HP Hf]. unfold mspecL, etwl in *.
  eapply twl_mono; [apply (twl_tall _ _ _ _ _ (H s mo HP) (K s))|].
  intros [|[a s']] mo1; cbn; [tauto|]. intros [HQ E]. split; [exact HQ|]. congruence.
Qed.

Definition QI0 (X : list (bptr * Z)) : assn PState := fun s mo => QI X Pstat s mo /\ ps_x s = None.
Definition xsl (s : PState) : list (bptr * Z) := match ps_x s with Some p => [(p, IMP_VEC)] | None => [] end.
Definition QIx (X : list (bptr * Z)) : assn PState := fun s mo => QI (xsl s ++ X) Pstat s mo.

Lemma QI0_of_keeps : forall {A} (c : Monad.M PState A) X (Q : A -> list (bptr * Z)),
  keeps ps_x c -> mspecL LBUDGET (QI X Pstat) c (fun r s mo => QI (Q r) Pstat s mo) -> mspecL LBUDGET (QI0 X) c (fun r s mo => QI0 (Q r) s mo).
Proof.
  intros A c X Q K H. unfold QI0. eapply mspecL_conseq; [apply (mspecL_keeps ps_x c (QI X Pstat) (fun r s mo => QI (Q r) Pstat s mo) None K H)| |];
  cbn beta; intros; tauto.
Qed.
Lemma raw_malloc_LQ0 : forall X n, 0 <= n ->
  mspecL LBUDGET (fun s mo => QI0 X s mo /\ mal_okQ X n) (raw_malloc n)
         (fun r s mo => match r with Some p => QI0 ((p, n) :: X) s mo /\ n < 2^63 | None => QI0 X s mo end).
Proof.
  intros X n Hn. unfold QI0.
  eapply mspecL_conseq;
    [apply (mspecL_keeps ps_x (raw_malloc n) (fun s mo => QI X Pstat s mo /\ mal_okQ X n)
              (fun r s mo => match r with Some p => QI ((p, n) :: X) Pstat s mo /\ n < 2^63 | None => QI X Pstat s mo end) None);
     [apply keeps_x_raw_malloc| apply raw_malloc_LQ'; exact Hn]| |].
  - cbn beta. intros; tauto.
  - cbn beta. intros [p|] s mo [H E]; tauto.
Qed.
Lemma raw_free_LQ0 : forall X p n, mspecL LBUDGET (QI0 ((p, n) :: X)) (raw_free p) (fun _ => QI0 X).
Proof. intros X p n. apply (QI0_of_keeps (raw_free p) ((p, n) :: X) (fun _ => X)); [apply keeps_x_raw_free| apply raw_free_LQ']. Qed.
Lemma QI0_perm : forall X Y s mo, Permutation X Y -> QI0 X s mo -> QI0 Y s mo.
Proof. intros X Y s mo HP [H E]. split; [eapply QI_perm'; eauto| exact E]. Qed.
Lemma diag_LQ0 : forall X d, mspecL LBUDGET (QI0 X) (io_diag io d) (fun _ => QI0 X).
Proof. intros X d. unfold io, io_S. cbn [io_diag]. apply (QI0_of_keeps _ X (fun _ => X)); [apply keeps_x_s_diag| apply diag_LQ]. Qed.
Lemma alloc_init_LQ0 : forall X bm, mspecL LBUDGET (QI0 X) (alloc_init bm) (fun _ => QI0 X).
Proof. intros X bm. unfold alloc_init. apply mspecL_ret. auto. Qed.
Lemma QI0_minv : forall X s mo, QI0 X s mo -> minv mo /\ m_halted mo = None.
Proof. intros X s mo [H _]. eapply QI_minv'; exact H. Qed.
Lemma QI0_fds : forall X s mo mo', QI0 X s mo -> m_vmmaps mo' = m_vmmaps mo -> minv mo' -> m_halted mo' = None -> QI0 X s mo'.
Proof. intros X s mo mo' [H E] Hv Hm Hh. split; [eapply QI_fds'; eauto| exact E]. Qed.
Lemma QI0_live : forall X s mo, QI0 X s mo -> live mo <= LBUDGET.
Proof. intros X s mo [H _]. eapply QI_live'; exact H. Qed.
Lemma startup_LQ0 : mspecL LBUDGET (QI0 []) startup (fun _ => QI0 []).
Proof.
  apply (QI0_of_keeps startup [] (fun _ => [])); [apply keeps_x_startup|].
  apply (startup_L LBUDGET (QI [] Pstat)); [apply QI_minv'| apply QI_fds'| apply QI_live'].
Qed.
Lemma QI_set_x : forall X v s mo, QI X Pstat s mo -> QI X Pstat (set_x_ps v s) mo.
Proof. intros X v s mo H. destruct s. exact H. Qed.
Lemma raw_free_LQx : forall X p n, mspecL LBUDGET (QIx ((p, n) :: X)) (raw_free p) (fun _ => QIx X).
Proof.
  intros X p n. apply mspecL_pointwise. intros s0 mo0 H0.
  eapply mspecL_conseq; [apply (mspecL_keeps ps_x (raw_free p) (QI ((p, n) :: (xsl s0 ++ X)) Pstat) (fun _ => QI (xsl s0 ++ X) Pstat) (ps_x s0));
                         [apply keeps_x_raw_free| apply raw_free_LQ']| |].
  - intros s mo [-> ->]. split; [|reflexivity]. eapply QI_perm'; [| exact H0]. apply Permutation_sym. apply Permutation_middle.
  - intros u s mo [H E]. unfold QIx, xsl in *. rewrite E. exact H.
Qed.
Lemma alloc_count_LQx : forall X, mspecL LBUDGET (QIx X) alloc_count (fun _ => QIx X).
Proof. intros X. unfold alloc_count. apply mspecL_ret. auto. Qed.

Lemma run_LQ0 : forall b cap cfg payload, 65536 <= cap <= MAX_INPUT -> zlength payload <= MAX_INPUT ->
  mspecL LBUDGET (QI0 [(b, cap)]) (run cfg payload) (fun _ => QIx [(b, cap)]).
Proof.
  intros b cap cfg payload Hcap Hpl. unfold run.
  eapply mspecL_bind.
  - eapply mspecL_pre; [apply (target_run_L LBUDGET raw_malloc raw_free ps_so set_so_ps QIX mal_okQ
           raw_malloc_LQ' raw_free_LQ' QI_perm' out_LQ OK_sj [(b, cap)] cfg payload);
      [cbn; lia| constructor; [cbn [snd]; lia| constructor]| cbn [sumX snd]; lia| exact Hpl]|].
    intros s mo [H _]. exact H.
  - intros r. cbn beta. eapply mspecL_seq with (R := QIx [(b, cap)]).
    + apply mspecL_upd'. intros s mo H. unfold QIx.
      replace (xsl (set_x_ps (snd r) s)) with (LB_PTarget.oX (snd r) IMP_VEC) by (destruct s; destruct (snd r); reflexivity).
      apply QI_set_x. exact H.
    + intros _. apply mspecL_ret. intros s mo H. exact H.
Qed.

Lemma xfree_L : mspecL LBUDGET (fun s mo => (exists X, QI0 X s mo) \/ (exists X, QIx X s mo)) xfree (fun _ s mo => exists X, QI X Pstat s mo).
Proof.
  unfold xfree. eapply mspecL_bind; [apply mspecL_get|]. intros s0. cbn beta.
  apply mspecL_pointwise. intros s mo [<- H].
  destruct (ps_x s0) as [p|] eqn:E.
  - destruct H as [[X [H E']]|[X H]]; [congruence|].
    eapply mspecL_conseq; [apply (raw_free_LQ' X p IMP_VEC)| |].
    + intros s' mo' [-> ->]. unfold QIx, xsl in H. rewrite E in H. exact H.
    + intros u s' mo' H'. exists X. exact H'.
  - apply mspecL_ret. intros s' mo' [-> ->].
    destruct H as [[X [H _]]|[X H]]; exists X; [exact H|]. unfold QIx, xsl in H. rewrite E in H. exact H.
Qed.

Lemma prog_with_L : forall rstage argv,
  Forall (fun a => zlength a < 2^32) argv -> Forall path_okZ (tl argv) ->
  mspecL LBUDGET (QI0 []) (prog_with rstage argv) (fun _ _ _ => False).
Proof.
  intros rstage argv Hargv Hpaths. unfold prog_with.
  eapply mspecL_seq; [apply startup_LQ0|]. intros u.
  eapply mspecL_bind.
  - apply (main_model_L LBUDGET io raw_malloc raw_free rstage alloc_init run alloc_count QI0 mal_okQ
             raw_malloc_LQ0 raw_free_LQ0 QI0_perm diag_LQ0 alloc_init_LQ0 QIx run_LQ0 raw_free_LQx alloc_count_LQx QI0_minv QI0_fds QI0_live
             OK_first OK_grow argv Hargv Hpaths).
  - intros code. unfold exit_imp. eapply mspecL_seq; [apply xfree_L|]. intros _.
    eapply mspecL_pre; [eapply (exit_model_L LBUDGET io QIX); apply exitio_LQ|]. intros s mo H. exact H.
Qed.

Lemma low_psegs : reserved_top (segments_reserved psegs) + brk_aslr_max <= 2 ^ 33.
Proof. vm_compute. discriminate. Qed.

Lemma low_usegs : reserved_top (segments_reserved usegs) + brk_aslr_max <= 2 ^ 33.
Proof. vm_compute. discriminate. Qed.

Lemma low_pu : forall segs, segs_pu segs -> reserved_top (segments_reserved segs) + brk_aslr_max <= 2 ^ 33.
Proof. intros segs [H|H]; rewrite H; [apply low_psegs| apply low_usegs]. Qed.

Theorem prog_noerr_gen : forall segs rstage pc ph lim en inp,
  segs_pu segs -> KLIM + SMALLREQ <= lim ->
  valid_entry (mkImage segs pc ph) en inp -> valid_input_either inp ->
  bv_unsigned (en_sp en) - stack_max_size = alloc_ceiling ->
  tsafe nstep node_noerr (prog segs rstage (in_argv inp))
        (init_model (segments_reserved segs) (en_brk en) (en_mmap_base en) (en_sp en) lim inp).
Proof.
  intros segs rstage pc ph lim [sp brk0 mbase] inp Hsegs Hlim Hve Hvi Htop.
  destruct Hve as (_ & Hbrk & _). destruct Hvi as (Hargv & _).
  unfold prog. cbn [en_brk en_mmap_base en_sp] in *.
  apply (mspecL_program_noerr LBUDGET (QI0 []) (prog_with rstage (argv_Z (in_argv inp))) (fun _ _ _ => False)).
  - apply prog_with_L; [apply argv_Z_short| apply argv_Z_paths]; exact Hargv.
  - cbn [img_segments] in Hbrk. split; [| reflexivity].
    apply QI_init; [exact Hbrk| apply reserved_top_pu; exact Hsegs| apply ceil_pu; exact Hsegs| exact Htop| exact Pstat_nonneg| | apply low_pu; exact Hsegs| exact Hlim].
    pose proof PHI_Pstat. unfold MAX_INPUT, IB, UNIT in *. lia.
  - intros [].
Qed.

End WithCeiling.

Definition noerr_stmt (segs : list Segment) (rstage : Z) (pc : N) (ph : PhdrInfo) (lim : Z) : Prop :=
  forall en inp, valid_entry (mkImage segs pc ph) en inp -> valid_input_either inp ->
    tsafe nstep node_noerr (@Prog.prog (ceiling_of_sp (bv_unsigned (en_sp en))) segs rstage (in_argv inp))
          (init_model (segments_reserved segs) (en_brk en) (en_mmap_base en) (en_sp en) lim inp).

Theorem prog_noerr : forall segs rstage pc ph lim,
  segs_pu segs -> KLIM + SMALLREQ <= lim ->
  noerr_stmt segs rstage pc ph lim.
Proof.
  intros segs rstage pc ph lim Hsegs Hlim en inp Hve Hvi.
  apply (@prog_noerr_gen (ceiling_of_sp (bv_unsigned (en_sp en))) segs rstage pc ph lim en inp Hsegs Hlim Hve Hvi).
  rewrite <- (TopLevel.mo0_alloc_top_ceiling segs pc ph lim en inp (TopLevel.vie_va_size _ Hvi) Hve). reflexivity.
Qed.

