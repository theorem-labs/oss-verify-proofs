(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import PropExec MState ITree Nodes Decode.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import Prelim Monad MSafe Sim MPaths STree Malloc KInv KStep PState KLink KEv JLedger Relim StepB EquivK_iface EKPlace.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Malloc Require Import ProgDeps.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).
Local Notation MP := (Monad.M PState).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma dec_mmap_err_errno : forall atop len avoid rsp e,
  dec_mmap atop len avoid rsp = Some (MmErr e) -> errno_of (eff_ret rsp) = Some e.
Proof.
  intros atop len avoid [r ws zs us cs ci] e H. unfold dec_mmap in H. cbn [eff_ret].
  destruct ws; [|discriminate]. destruct zs as [|[a n] [|]].
  - destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct (errno_of r); congruence.
  - destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct (_ && _); discriminate.
  - discriminate.
Qed.

Lemma dec_mmap_none_err_errno : forall atop len avoid rsp e,
  dec_mmap_none atop len avoid rsp = Some (MmErr e) -> errno_of (eff_ret rsp) = Some e.
Proof.
  intros atop len avoid [r ws zs us cs ci] e H. unfold dec_mmap_none in H. cbn [eff_ret].
  destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us as [|[a n] [|]].
  - destruct cs; [|discriminate]. destruct (errno_of r); congruence.
  - destruct cs; [|discriminate]. destruct (_ && _); discriminate.
  - discriminate.
Qed.

Lemma dec_mmap_fixed_err_errno : forall addr len rsp x,
  dec_mmap_fixed addr len rsp = Some x -> match x with FxKept e | FxLost e => errno_of (eff_ret rsp) = Some e | FxDone => True end.
Proof.
  intros addr len [r ws zs us cs ci] x H. unfold dec_mmap_fixed in H. cbn [eff_ret].
  destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us as [|[a n] [|]].
  - destruct cs; [|discriminate]. destruct (errno_of r); [|discriminate]. injection H as <-. reflexivity.
  - destruct cs; [|discriminate]. destruct (_ && _); [|discriminate].
    destruct (errno_of r); [injection H as <-; reflexivity|]. destruct (bv_eqb r _); [|discriminate]. injection H as <-. exact I.
  - discriminate.
Qed.

Lemma dec_mprotect_err_errno : forall addr len rsp e,
  dec_mprotect addr len rsp = Some (RgErr e) -> errno_of (eff_ret rsp) = Some e.
Proof.
  intros addr len [r ws zs us cs ci] e H. unfold dec_mprotect in H. cbn [eff_ret].
  destruct ws; [|discriminate]. destruct zs as [|[a n] [|]].
  - destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct (errno_of r); [congruence|]. destruct (_ =? _); discriminate.
  - destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct (_ && _); discriminate.
  - discriminate.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section EvPaths.
Context {stp : node -> Model -> resp -> Model -> list event -> Prop}.
Context (atop : Z).     (* [comment removed for export] *)

#[using="Type"] Lemma ev_step_no_exit : forall e s mo tr, ~ texit stp nexit (ev_step atop e s) mo tr.
Proof.
  intros e s mo tr Hx. destruct e; cbn -[msys mbind mret mupd mget munr Z.eqb] in Hx.
  - destruct (addr =? 0).
    + apply texit_mbind in Hx as [Hx|(? & ? & ? & ? & ? & _ & Hx & _)]; [eapply texit_msys_nonexit; [| exact Hx]; exact I|].
      apply texit_mbind in Hx as [Hx|(? & ? & ? & ? & ? & _ & Hx & _)]; cbn in Hx; exact Hx.
    + apply texit_mbind in Hx as [Hx|(? & ? & ? & ? & ? & _ & Hx & _)]; [cbn in Hx; exact Hx|].
      apply texit_mbind in Hx as [Hx|(? & a & ? & ? & ? & _ & Hx & _)]; [eapply texit_msys_nonexit; [| exact Hx]; exact I|].
      destruct a; [apply texit_mbind in Hx as [Hx|(? & ? & ? & ? & ? & _ & Hx & _)]|]; cbn in Hx; exact Hx.
  - destruct (negb (Z.land flags MAP_FIXED_Z =? 0)); [|destruct (prot =? 0)];
      (apply texit_mbind in Hx as [Hx|(? & ? & ? & ? & ? & _ & Hx & _)]; [eapply texit_msys_nonexit; [| exact Hx]; exact I| cbn in Hx; exact Hx]).
  - apply texit_mbind in Hx as [Hx|(? & ? & ? & ? & ? & _ & Hx & _)]; [eapply texit_msys_nonexit; [| exact Hx]; exact I| cbn in Hx; exact Hx].
  - apply texit_mbind in Hx as [Hx|(? & ? & ? & ? & ? & _ & Hx & _)]; [eapply texit_msys_nonexit; [| exact Hx]; exact I| cbn in Hx; exact Hx].
  - cbn in Hx. exact Hx.
  - cbn in Hx. exact Hx.
Qed.

#[using="Type"] Lemma path_brk0 : forall s mo tr z s' mo',
  tpath stp (ev_step atop (EBrk 0) s) mo tr (Ok (z, s')) mo' <->
  exists rsp, stp (NBrk 0) mo rsp mo' tr /\ dec_brk0 rsp = Some z /\ s' = set_brk_ps z s.
Proof.
  intros s mo tr z s' mo'. unfold ev_step. cbn [Z.eqb]. rewrite tpath_mbind_ok. split.
  - intros (tr1 & a & s1 & mo1 & tr2 & H1 & H2 & ->). apply tpath_msys_ok in H1 as (rsp & Hst & Hd & ->).
    apply tpath_mbind_ok in H2 as (tr3 & u & s2 & mo2 & tr4 & H3 & H4 & ->). apply tpath_mupd in H3 as (E & -> & ->). inversion E; subst; clear E.
    apply (tpath_mret (st:=stp)) in H4 as (E & -> & ->). inversion E; subst; clear E. exists rsp. rewrite !app_nil_r. auto.
  - intros (rsp & Hst & Hd & ->). exists tr, z, s, mo', []. rewrite app_nil_r. split; [apply tpath_msys_ok; exists rsp; auto|]. split; [|reflexivity].
    apply tpath_mbind_ok. exists [], tt, (set_brk_ps z s), mo', []. split; [apply tpath_mupd; auto|]. split; [apply (tpath_mret (st:=stp)); auto| reflexivity].
Qed.

#[using="Type"] Lemma path_brk_grow : forall req s mo tr z s' mo', req <> 0 ->
  tpath stp (ev_step atop (EBrk req) s) mo tr (Ok (z, s')) mo' <->
  exists rsp a, stp (NBrk req) mo rsp mo' tr /\ dec_brk (ps_brk s) req rsp = Some a /\
    match a with BrkGrown => z = req /\ s' = set_brk_ps req s | BrkSame => z = ps_brk s /\ s' = s end.
Proof.
  intros req s mo tr z s' mo' Hne. unfold ev_step. rewrite (proj2 (Z.eqb_neq req 0) Hne).
  rewrite tpath_mbind_ok. split.
  - intros (tr1 & s0 & s1 & mo1 & tr2 & H1 & H2 & ->). apply (tpath_mget (st:=stp)) in H1 as (E & -> & ->). inversion E; subst; clear E.
    apply tpath_mbind_ok in H2 as (tr3 & a & s2 & mo2 & tr4 & H3 & H4 & ->). apply tpath_msys_ok in H3 as (rsp & Hst & Hd & ->).
    exists rsp, a. cbn [app]. destruct a.
    + apply tpath_mbind_ok in H4 as (tr5 & u & s3 & mo3 & tr6 & H5 & H6 & ->). apply tpath_mupd in H5 as (E & -> & ->). inversion E; subst; clear E.
      apply (tpath_mret (st:=stp)) in H6 as (E & -> & ->). inversion E; subst; clear E. rewrite !app_nil_r. auto.
    + apply (tpath_mret (st:=stp)) in H4 as (E & -> & ->). inversion E; subst; clear E. rewrite !app_nil_r. auto.
  - intros (rsp & a & Hst & Hd & Ha). exists [], s, s, mo, tr. split; [apply (tpath_mget (st:=stp)); auto|]. split; [|reflexivity].
    apply tpath_mbind_ok. exists tr, a, s, mo', []. rewrite app_nil_r. split; [apply tpath_msys_ok; exists rsp; auto|]. split; [|reflexivity].
    destruct a; destruct Ha as [-> ->].
    + apply tpath_mbind_ok. exists [], tt, (set_brk_ps req s), mo', []. split; [apply tpath_mupd; auto|]. split; [apply (tpath_mret (st:=stp)); auto| reflexivity].
    + apply tpath_mret. auto.
Qed.

Definition mval (a : mmap_ans) : Z := match a with MmErr e => neg_errno e | MmOk x => x end.

#[using="Type"] Lemma path_mmap_anon : forall addr len prot flags s mo tr z s',
  forall mo', Z.land flags MAP_FIXED_Z =? 0 = true ->
  tpath stp (ev_step atop (EMmap addr len prot flags) s) mo tr (Ok (z, s')) mo' <->
  exists rsp a, stp (NMmap addr len prot flags) mo rsp mo' tr
    /\ (if prot =? 0 then dec_mmap_none atop len [] rsp else dec_mmap atop len [] rsp) = Some a /\ z = mval a /\ s' = s.
Proof.
  intros addr len prot flags s mo tr z s' mo' Hf. unfold ev_step. rewrite Hf. cbn [negb].
  destruct (prot =? 0); rewrite tpath_mbind_ok; split.
  - intros (tr1 & a & s1 & mo1 & tr2 & H1 & H2 & ->). apply tpath_msys_ok in H1 as (rsp & Hst & Hd & ->).
    apply (tpath_mret (st:=stp)) in H2 as (E & -> & ->). inversion E; subst; clear E. exists rsp, a. rewrite app_nil_r. auto.
  - intros (rsp & a & Hst & Hd & -> & ->). exists tr, a, s, mo', []. rewrite app_nil_r. split; [apply tpath_msys_ok; exists rsp; auto|]. split; [apply (tpath_mret (st:=stp)); auto| reflexivity].
  - intros (tr1 & a & s1 & mo1 & tr2 & H1 & H2 & ->). apply tpath_msys_ok in H1 as (rsp & Hst & Hd & ->).
    apply (tpath_mret (st:=stp)) in H2 as (E & -> & ->). inversion E; subst; clear E. exists rsp, a. rewrite app_nil_r. auto.
  - intros (rsp & a & Hst & Hd & -> & ->). exists tr, a, s, mo', []. rewrite app_nil_r. split; [apply tpath_msys_ok; exists rsp; auto|]. split; [apply (tpath_mret (st:=stp)); auto| reflexivity].
Qed.

Definition fval (addr : Z) (x : fixed_ans) : Z := match x with FxKept e => neg_errno e | FxDone => addr | FxLost e => neg_errno e end.

#[using="Type"] Lemma path_mmap_fixed : forall addr len prot flags s mo tr z s' mo',
  Z.land flags MAP_FIXED_Z =? 0 = false ->
  tpath stp (ev_step atop (EMmap addr len prot flags) s) mo tr (Ok (z, s')) mo' <->
  exists rsp x, stp (NMmap addr len prot flags) mo rsp mo' tr /\ dec_mmap_fixed addr len rsp = Some x /\ z = fval addr x /\ s' = s.
Proof.
  intros addr len prot flags s mo tr z s' mo' Hf. unfold ev_step. rewrite Hf. cbn [negb]. rewrite tpath_mbind_ok. split.
  - intros (tr1 & a & s1 & mo1 & tr2 & H1 & H2 & ->). apply tpath_msys_ok in H1 as (rsp & Hst & Hd & ->).
    apply (tpath_mret (st:=stp)) in H2 as (E & -> & ->). inversion E; subst; clear E. exists rsp, a. rewrite app_nil_r. auto.
  - intros (rsp & a & Hst & Hd & -> & ->). exists tr, a, s, mo', []. rewrite app_nil_r. split; [apply tpath_msys_ok; exists rsp; auto|]. split; [apply (tpath_mret (st:=stp)); auto| reflexivity].
Qed.

Definition rval (x : range_ans) : Z := match x with RgErr e => neg_errno e | RgDone _ => 0 end.

#[using="Type"] Lemma path_munmap : forall addr len s mo tr z s' mo',
  tpath stp (ev_step atop (EMunmap addr len) s) mo tr (Ok (z, s')) mo' <->
  exists rsp x, stp (NMunmap addr len) mo rsp mo' tr /\ dec_munmap addr len rsp = Some x /\ z = rval x /\ s' = s.
Proof.
  intros addr len s mo tr z s' mo'. unfold ev_step. rewrite tpath_mbind_ok. split.
  - intros (tr1 & a & s1 & mo1 & tr2 & H1 & H2 & ->). apply tpath_msys_ok in H1 as (rsp & Hst & Hd & ->).
    apply (tpath_mret (st:=stp)) in H2 as (E & -> & ->). inversion E; subst; clear E. exists rsp, a. rewrite app_nil_r. auto.
  - intros (rsp & a & Hst & Hd & -> & ->). exists tr, a, s, mo', []. rewrite app_nil_r. split; [apply tpath_msys_ok; exists rsp; auto|]. split; [apply (tpath_mret (st:=stp)); auto| reflexivity].
Qed.

#[using="Type"] Lemma path_mprotect : forall addr len prot s mo tr z s' mo',
  tpath stp (ev_step atop (EMprotect addr len prot) s) mo tr (Ok (z, s')) mo' <->
  exists rsp x, stp (NMprotect addr len prot) mo rsp mo' tr /\ dec_mprotect_rw addr len rsp = Some x /\ z = rval x /\ s' = s.
Proof.
  intros addr len prot s mo tr z s' mo'. unfold ev_step. rewrite tpath_mbind_ok. split.
  - intros (tr1 & a & s1 & mo1 & tr2 & H1 & H2 & ->). apply tpath_msys_ok in H1 as (rsp & Hst & Hd & ->).
    apply (tpath_mret (st:=stp)) in H2 as (E & -> & ->). inversion E; subst; clear E. exists rsp, a. rewrite app_nil_r. auto.
  - intros (rsp & a & Hst & Hd & -> & ->). exists tr, a, s, mo', []. rewrite app_nil_r. split; [apply tpath_msys_ok; exists rsp; auto|]. split; [apply (tpath_mret (st:=stp)); auto| reflexivity].
Qed.
End EvPaths.

(* [comment removed for export] *)
Lemma mspec_tpath {St A} : forall (P : assn St) (m : Monad.M St A) Q s mo tr a s' mo',
  mspec P m Q -> P s mo -> tpath nstep (m s) mo tr (Ok (a, s')) mo' -> Q a s' mo'.
Proof.
  intros P m Q s mo tr a s' mo' Hm HP Hp. pose proof (twf_tpath _ _ _ _ _ _ (Hm s mo HP) Hp) as H. cbn in H. exact H.
Qed.

Lemma frame_ok_true : frame_ok (fun _ _ => True).
Proof. intros ? ? ? ? ? ? ? ?. exact I. Qed.

(* [comment removed for export] *)
Lemma ev_step_path_post : forall (stp : node -> Model -> resp -> Model -> list event -> Prop) L e s mo tr z s' mo',
  (forall (t : itree node (exc (Z * PState))) mo0 tr0 r mo1, tpath stp t mo0 tr0 r mo1 -> tpath nstep t mo0 tr0 r mo1) ->
  event_pre L e -> KL L (ps_brk s) mo ->
  tpath stp (ev_step (ld_atop L) e s) mo tr (Ok (z, s')) mo' ->
  answer_ok L e z = true /\ KL (event_post L e z) (ps_brk s') mo'
  /\ ps_m s' = ps_m s /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s.
Proof.
  intros stp L e s mo tr z s' mo' Hsub Hpre HK Hp. apply Hsub in Hp.
  pose proof (mspec_tpath _ _ _ s mo tr z s' mo' (ev_step_spec L e (fun _ _ => True) s frame_ok_true Hpre) ltac:(cbn; auto) Hp) as H.
  unfold ev_step_post in H. tauto.
Qed.

Lemma tpath_sub_nstep : forall t mo tr (r : exc (Z * PState)) mo', tpath nstep t mo tr r mo' -> tpath nstep t mo tr r mo'.
Proof. auto. Qed.
Lemma tpath_sub_stepB : forall t mo tr (r : exc (Z * PState)) mo', tpath stepB t mo tr r mo' -> tpath nstep t mo tr r mo'.
Proof. intros. eapply tpath_nstep_of_nstepB. exact H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition XMC (h : VmMaps) (BE RE : list (word * word)) : Prop :=
  let b0 := bv_unsigned (vm_start_brk h) in
  Permutation (vm_maps h) (BE ++ RE)
  /\ (forall e, In e BE -> b0 <= elo e /\ ehi e <= bv_unsigned (vm_brk h))
  /\ (forall e, In e RE -> slab_entry e)
  /\ bv_unsigned (vm_brk h) <= b0 + live_bytes BE + PGSZ
  /\ 0 < b0 /\ b0 + CORR <= 2^40.

(* [comment removed for export] *)
Definition GB40 (L : mled) : Prop :=
  forall b l, (In (b, l) (ld_groups L) \/ exists k, In (b, l, k) (ld_metas L)) -> 2^40 <= b.

Lemma GB40_post : forall L e z, GB40 L ->
  (forall a len prot flags, e = EMmap a len prot flags -> Z.land flags MAP_FIXED =? 0 = true -> is_err z = false -> 2^40 <= z) ->
  GB40 (event_post L e z).
Proof.
  intros L e z HB Hm. intros b l Hin.
  assert (HBbl : (In (b, l) (ld_groups L) \/ exists k, In (b, l, k) (ld_metas L)) -> 2^40 <= b) by (apply HB).
  destruct e; cbn [event_post] in Hin.
  - revert Hin. destruct (addr =? 0); [intros Hin; exact (HBbl Hin)|]. destruct (z =? addr); [|intros Hin; exact (HBbl Hin)].
    destruct (ld_brk L); try (intros Hin; exact (HBbl Hin)); destruct (ld_brkreg L) as [[? ?]|]; intros Hin; exact (HBbl Hin).
  - revert Hin. destruct (Z.land flags MAP_FIXED =? 0) eqn:Ef; [|intros Hin; exact (HBbl Hin)]. destruct (is_err z) eqn:Ee; [intros Hin; exact (HBbl Hin)|].
    destruct (prot =? PROT_NONE); cbn; intros Hin.
    + destruct Hin as [Hin|[k [E|Hin]]]; [apply HBbl; left; exact Hin| injection E as <- <- <-; eapply Hm; eauto| apply HBbl; right; exists k; exact Hin].
    + destruct Hin as [[E|Hin]|[k Hin]]; [injection E as <- <-; eapply Hm; eauto| apply HBbl; left; exact Hin| apply HBbl; right; exists k; exact Hin].
  - cbn in Hin. apply HBbl. destruct Hin as [Hin|Hin]; [left| right; exact Hin].
    revert Hin. generalize (ld_groups L) as gs. induction gs as [|g gs IH]; cbn; intros Hin; [exact Hin|].
    destruct (fst g =? addr); [right; exact Hin|]. destruct Hin as [->|Hin]; [left; reflexivity| right; apply IH; exact Hin].
  - revert Hin. destruct ((z =? 0) || (z =? TWO64 - ENOSYS)); [|intros Hin; exact (HBbl Hin)]. cbn. intros Hin. apply HBbl. destruct Hin as [Hin|[k Hin]]; [left; exact Hin| right].
    apply in_map_iff in Hin as ([[b' l'] k'] & E & Hin). unfold bump_meta in E. destruct (b' + (1 + k') * PGSZ =? addr); injection E as -> -> E3; eexists; exact Hin.
  - exact (HBbl Hin).
  - exact (HBbl Hin).
Qed.

Definition KR (J : jled) (sG : PState) (moG : Model) (sC : PState) (moC : Model) : Prop :=
  KL (projG J) (ps_brk sG) moG /\ KL (projC J) (ps_brk sC) moC
  /\ vm_live_bytes (m_vmmaps moG) = vm_live_bytes (m_vmmaps moC)
  /\ vm_live_bytes (m_vmmaps moG) <= LBND
  /\ LBND + PGSZ <= vm_limit (m_vmmaps moC)
  /\ (exists BE RE, XMC (m_vmmaps moC) BE RE)
  /\ m_fds moG = m_fds moC /\ m_fs moG = m_fs moC
  /\ GB40 (projC J).

Definition ev_post (J : jled) (eG eC : ev) (sG0 sC0 : PState) (zG zC : Z) : rel PState PState :=
  fun sG moG sC moC =>
    jans_ok J eG eC zG zC = true /\ KR (jevent_post J eG eC zG zC) sG moG sC moC
    /\ ps_m sG = ps_m sG0 /\ ps_fa sG = ps_fa sG0 /\ ps_so sG = ps_so sG0
    /\ ps_m sC = ps_m sC0 /\ ps_fa sC = ps_fa sC0 /\ ps_so sC = ps_so sC0.

(* [comment removed for export] *)
Lemma ev_post_intro : forall J eG eC sG0 moG sC0 moC trG trC zG zC sG' moG' sC' moC',
  jev_rel J eG eC -> KR J sG0 moG sC0 moC ->
  tpath stepB (ev_step (j_atopG J) eG sG0) moG trG (Ok (zG, sG')) moG' ->
  tpath nstep (ev_step (j_atopC J) eC sC0) moC trC (Ok (zC, sC')) moC' ->
  same_class eG eC zG zC = true ->
  (forall aG aC len len', eG = EMunmap aG len -> eC = EMunmap aC len' -> jg_coherent aG aC (j_groups J)) ->
  (forall aG aC len len' p p', eG = EMprotect aG len p -> eC = EMprotect aC len' p' -> jm_coherent aG aC (j_metas J)) ->
  vm_live_bytes (m_vmmaps moG') = vm_live_bytes (m_vmmaps moC') ->
  vm_live_bytes (m_vmmaps moG') <= LBND ->
  LBND + PGSZ <= vm_limit (m_vmmaps moC') ->
  (exists BE RE, XMC (m_vmmaps moC') BE RE) ->
  m_fds moG' = m_fds moC' -> m_fs moG' = m_fs moC' ->
  GB40 (event_post (projC J) eC zC) ->
  ev_post J eG eC sG0 sC0 zG zC sG' moG' sC' moC'.
Proof.
  intros J eG eC sG0 moG sC0 moC trG trC zG zC sG' moG' sC' moC' Hrel (KG & KC & _) HpG HpC Hcl Hcoh1 Hcoh2 Hl1 Hl2 Hl3 Hx Hf1 Hf2 HB.
  destruct (jev_rel_pre _ _ _ Hrel) as [HpreG HpreC].
  destruct (ev_step_path_post stepB _ _ _ _ _ _ _ _ tpath_sub_stepB HpreG KG HpG) as (AG & KG' & EG1 & EG2 & EG3).
  destruct (ev_step_path_post nstep _ _ _ _ _ _ _ _ tpath_sub_nstep HpreC KC HpC) as (AC & KC' & EC1 & EC2 & EC3).
  unfold ev_post, KR. rewrite (projG_post J eG eC zG zC Hrel Hcl), (projC_post J eG eC zG zC Hrel Hcl Hcoh1 Hcoh2).
  unfold jans_ok. rewrite AG, AC, Hcl. splits; auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition KRJ (J : jled) : rel PState PState := fun sG moG sC moC => KR J sG moG sC moC.

Lemma brk_model_next_limit : forall h req r, vm_limit (brk_model_next h req r) = vm_limit h.
Proof. reflexivity. Qed.

Lemma XMC_same : forall h h' BE RE, XMC h BE RE ->
  vm_maps h' = vm_maps h -> vm_start_brk h' = vm_start_brk h -> vm_brk h' = vm_brk h -> XMC h' BE RE.
Proof. intros h h' BE RE HX E1 E2 E3. unfold XMC in *. rewrite E1, E2, E3. exact HX. Qed.

Lemma live_bytes_bound_BE : forall h BE RE, XMC h BE RE -> live_bytes BE <= vm_live_bytes h.
Proof.
  intros h BE RE (HP & _). unfold vm_live_bytes. rewrite (live_bytes_perm _ _ HP), live_bytes_app. pose proof (live_bytes_nonneg RE). Local Ltac2 Set LiaHints.tbl := fun () => "0010=45518764950.5000003S1H".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

Lemma tables_after : forall moG moG' moC moC',
  vm_only moG moG' -> vm_only moC moC' -> m_fds moG = m_fds moC -> m_fs moG = m_fs moC ->
  m_fds moG' = m_fds moC' /\ m_fs moG' = m_fs moC'.
Proof.
  intros moG moG' moC moC' HvG HvC Hf Hs. destruct (vm_only_tables _ _ HvG) as [F1 F2]. destruct (vm_only_tables _ _ HvC) as [F3 F4].
  rewrite F1, F2, F3, F4. auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma sim_brk0 : forall J sG0 sC0, j_brk J = JUntried ->
  fsim debt0 debt0 stepB (pin (KRJ J) sG0 sC0) (ev_step (j_atopG J) (EBrk 0)) (ev_step (j_atopC J) (EBrk 0)) (ev_post J (EBrk 0) (EBrk 0) sG0 sC0).
Proof.
  intros J sG0 sC0 Hph sG moG sC moC (-> & -> & HKR). split; [| intros trG Hx; exfalso; eapply ev_step_no_exit; exact Hx].
  intros trG zG sG' moG' HpG. pose proof HpG as HpG0. apply path_brk0 in HpG as (rspG & [HstG [HbG HnfG]] & HdG & ->).
  destruct HKR as (KG & KC & Hlive & Hbnd & HlimC & (BE & RE & HX) & Hfds & Hfs & HB40).
  pose proof (nstep_dec_brk0 _ _ _ _ HstG) as (-> & HdG' & HvoG & HbrkG).
  pose proof (nstep_brk_inv _ _ _ _ _ HstG) as (rG & HrG & EmoG & _ & _). apply brk_r_ok_query in HrG. subst rG.
  Local Ltac2 Set LiaHints.tbl := fun () => "0020>22364850745.2926240379929.36000001002SS".
rewrite with_brk_next_noshrink in EmoG by lia.
  pose proof (brk_model_next_query (m_vmmaps moG)) as (QG1 & QG2 & QG3 & QG4 & QG5).
  (* [comment removed for export] *)
  set (hC := m_vmmaps moC).
  pose proof (nstep_brk_intro 0 moC (vm_brk hC) (brk_r_ok_refuse moC (Z_to_bv 64 0)) (brk_refusal_query moC (vm_brk hC))) as HstC. fold hC in HstC.
  rewrite with_brk_next_noshrink in HstC by (fold hC; lia).
  pose proof (nstep_dec_brk0 _ _ _ _ HstC) as (_ & HdC & HvoC & HbrkC).
  pose proof (brk_model_next_query hC) as (QC1 & QC2 & QC3 & QC4 & QC5).
  set (moC' := with_vmmaps (brk_model_next hC (Z_to_bv 64 0) (vm_brk hC)) moC) in *.
  set (zC := bv_unsigned (vm_brk (m_vmmaps moC))) in *.
  assert (HpC : tpath nstep (ev_step (j_atopC J) (EBrk 0) sC0) moC [] (Ok (zC, set_brk_ps zC sC0)) moC').
  { apply path_brk0. eexists. split; [exact HstC|]. auto. }
  exists [], zC, (set_brk_ps zC sC0), moC', []. split; [exact HpC|].
  unfold debt0. rewrite !app_nil_r. split; [reflexivity|]. split; [reflexivity|].
  destruct (tables_after _ _ _ _ HvoG HvoC Hfds Hfs) as [Hfds' Hfs'].
  apply (ev_post_intro J (EBrk 0) (EBrk 0) sG0 moG sC0 moC [] [] zG zC _ moG' _ moC').
  - cbn. left. auto.
  - unfold KR. splits; eauto.
  - exact HpG0.
  - exact HpC.
  - reflexivity.
  - intros; discriminate.
  - intros; discriminate.
  - rewrite EmoG. subst moC'. rewrite !m_vmmaps_with_vmmaps. unfold vm_live_bytes. rewrite QG2, QC2. exact Hlive.
  - rewrite EmoG. rewrite m_vmmaps_with_vmmaps. unfold vm_live_bytes. rewrite QG2. exact Hbnd.
  - subst moC'. rewrite m_vmmaps_with_vmmaps, brk_model_next_limit. exact HlimC.
  - exists BE, RE. subst moC'. rewrite m_vmmaps_with_vmmaps. eapply XMC_same; [exact HX| exact QC2| exact QC4| exact QC5].
  - exact Hfds'.
  - exact Hfs'.
  - apply (GB40_post _ _ _ HB40). intros ? ? ? ? E; discriminate.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
Lemma brk_grow_facts : forall J rG rC sG moG sC moC,
  jev_rel J (EBrk rG) (EBrk rC) -> rG <> 0 -> KR J sG moG sC moC ->
  exists d, (d = PGSZ \/ d = 2 * PGSZ) /\
    let bG := bv_unsigned (vm_brk (m_vmmaps moG)) in let bC := bv_unsigned (vm_brk (m_vmmaps moC)) in
    rG = bG + d /\ rC = bC + d /\ ps_brk sG = bG /\ ps_brk sC = bC
    /\ bG mod 4096 = 0 /\ bC mod 4096 = 0 /\ 0 < bG /\ 0 < bC
    /\ bv_unsigned (vm_start_brk (m_vmmaps moG)) <= bG /\ bv_unsigned (vm_start_brk (m_vmmaps moC)) <= bC
    /\ rG <= alloc_ceiling + PGSZ /\ rC <= alloc_ceiling + PGSZ.
Proof.
  intros J rG rC sG moG sC moC Hrel Hne (KG & KC & _). cbn in Hrel.
  pose proof (kl_phase _ _ _ KG) as PG. pose proof (kl_phase _ _ _ KC) as PC.
  pose proof (kl_start _ _ _ KG) as (SG1 & SG2 & SG3 & SG4). pose proof (kl_start _ _ _ KC) as (SC1 & SC2 & SC3 & SC4).
  pose proof (KL_atop_range _ _ _ KG) as ATG. pose proof (KL_atop_range _ _ _ KC) as ATC. cbn [ld_atop projG projC] in ATG, ATC, SG4, SC4.
  unfold projG, projC in PG, PC. cbn [ld_brk ld_brkreg] in PG, PC.
  destruct Hrel as [(-> & _ & _)|[(cG & cC & Hph & -> & -> & _)|(bG & bC & l & Hph & Hreg & -> & -> & _)]]; [contradiction| |].
  - rewrite Hph in PG, PC. cbn in PG, PC. destruct PG as (EG1 & EG2 & EG3 & _). destruct PC as (EC1 & EC2 & EC3 & _).
    exists (2 * PGSZ). split; [right; reflexivity|]. unfold PGSZ in *.
    rewrite !round_up_pg_aligned by (subst; assumption). Local Ltac2 Set LiaHints.tbl := fun () => "00B0>11438884227.271187595689.37 22379319303.3722379600053.2727854590851.3729307341477.3730533940800.2730776768904.2730777078074.3735576276357.2735576491319.3747479060977.2747479271747.3751666023824.3751666238754.2751938018711.2753346817652.2758490040815.3700000=00B00K00T00]00b00g01@01U01^01g02002902f03G03T03Y03bS3EG13SG43ATGS3EC2S3SG33SC3S3SG33SC3S3ATC3RC5S3EG2S3EC2S3EG13EG23SG13EC13EC23SC1S3EG23RG13RC33EC23RC1S3EG23EG3S3EG33EG2S3EC23EC3S3EC33EC2S3EG23SG13SC13RG13RG23RG33RC13RC33RC43EC23RC2S3EG13EG23SG13SG23SC13EC13EC23SC2S3EC13SC43ATCS3EG2S3ATG3RG5".
splits; lia.
  - rewrite Hph, Hreg in PG, PC. cbn in PG, PC. destruct PG as (bG' & l' & E1 & EG2 & EG3). injection E1 as <- <-.
    destruct PC as (bC' & l'' & E2 & EC2 & EC3). injection E2 as <- <-.
    pose proof (kl_brkreg _ _ _ KG bG l) as RG. pose proof (kl_brkreg _ _ _ KC bC l) as RC. cbn [projG projC ld_brkreg option_map rG rC] in RG, RC.
    rewrite Hreg in RG, RC. cbn in RG, RC. specialize (RG eq_refl). specialize (RC eq_refl).
    destruct RG as (RG1 & RG2 & RG3 & RG4 & RG5 & _). destruct RC as (RC1 & RC2 & RC3 & RC4 & RC5 & _).
    exists PGSZ. split; [left; reflexivity|]. unfold PGSZ in *. splits; try lia.
    all: try (rewrite EG2; rewrite Z.add_mod, RG2, RG4 by lia; reflexivity).
    all: try (rewrite EC2; rewrite Z.add_mod, RC2, RC4 by lia; reflexivity).
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma nstep_mmap_anon_inv : forall atop len prot mo rsp mo' evs,
  let h := m_vmmaps mo in let n := mmap_len len in
  0 < len < 2^63 -> (prot = PROT_NONE \/ prot = PROT_RW) ->
  atop = alloc_top h ->                      (* [comment removed for export] *)
  nstep (NMmap 0 len prot MAPF) mo rsp mo' evs ->
  evs = [] /\ vm_only mo mo' /\
  exists x, (if prot =? 0 then dec_mmap_none atop len [] rsp else dec_mmap atop len [] rsp) = Some x /\
  match x with
  | MmErr e => e = ENOMEM /\ mo' = mo
  | MmOk a => 0 < a /\ a mod 4096 = 0 /\ a + n <= atop
      /\ region_free (vm_reserved h ++ vm_maps h) (Z_to_bv 64 a) (Z_to_bv 64 n) = true
      /\ m_vmmaps mo' = mkVmMapsFull (vm_reserved h) ((Z_to_bv 64 a, Z_to_bv 64 n) :: vm_maps h)
                         (if prot =? 0 then (Z_to_bv 64 a, Z_to_bv 64 n) :: vm_noaccess h else vm_noaccess h)
                         (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)
  end.
Proof.
  intros atop len prot mo rsp mo' evs h n Hlen Hp Hat H. Local Ltac2 Set LiaHints.tbl := fun () => "0040>18761080636.1318765269464.1337310135028.1340207240639.1300000600<00A00JS4HlenS4HlenS3HatS4Hlen2Hn".
pose proof (mmap_len_ge len ltac:(lia)) as Hn. fold n in Hn.
  pose proof (alloc_top_lt h) as Hcl. unfold two_pow_64 in Hcl.
  destruct Hp as [-> | ->].
  - change (PROT_NONE =? 0) with true. cbv iota.
    pose proof (nstep_dec_mmap_none atop len [] mo rsp mo' evs ltac:(lia) ltac:(fold n; lia) (Forall_nil _) ltac:(fold h; lia) H) as (-> & Hvo & x & Hd & Hx).
    split; [reflexivity|]. split; [exact Hvo|]. exists x. split; [exact Hd|]. destruct x as [e|a]; [exact Hx|].
    destruct Hx as (Hok & Hrf & Evm). apply mmap_addr_ok_true in Hok as [(A1 & A2 & A3) _]. rewrite page_size_eq in A1.
    fold n in A3, Hrf, Evm. splits; auto.
  - change (PROT_RW =? 0) with false. cbv iota.
    pose proof (nstep_dec_mmap atop len [] mo rsp mo' evs ltac:(lia) ltac:(fold n; lia) (Forall_nil _) ltac:(fold h; lia) H) as (-> & Hvo & x & Hd & Hx).
    split; [reflexivity|]. split; [exact Hvo|]. exists x. split; [exact Hd|]. destruct x as [e|a]; [exact Hx|].
    destruct Hx as (Hok & Hrf & Evm). apply mmap_addr_ok_true in Hok as [(A1 & A2 & A3) _]. rewrite page_size_eq in A1.
    fold n in A3, Hrf, Evm. splits; auto.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

Lemma NICE_of_XMC : forall h BE RE, XMC h BE RE -> vm_live_bytes h <= LBND -> NICE (bv_unsigned (vm_start_brk h)) (vm_maps h).
Proof.
  intros h BE RE HX Hlim. pose proof (live_bytes_perm _ _ (proj1 HX)) as HPl. destruct HX as (XP & XBE & XRE & Xbrk & Xb0 & X40).
  unfold vm_live_bytes in Hlim. rewrite HPl, live_bytes_app in Hlim. pose proof (live_bytes_nonneg RE).
  split; [|split; [exact Xb0| exact X40]]. intros e He. apply (Permutation_in _ XP) in He. apply in_app_or in He as [He|He].
  - left. specialize (XBE e He). unfold in_corr, CORR, LBND, PGSZ in *. Local Ltac2 Set LiaHints.tbl := fun () => "0010=9907928309.1400000AS3XBE4Xbrk4Hlim1H".
lia.
  - right. apply XRE. exact He.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

Lemma sim_mmap_anon : forall J len prot sG0 sC0,
  jev_rel J (EMmap 0 len prot MAPF) (EMmap 0 len prot MAPF) ->
  fsim debt0 debt0 stepB (pin (KRJ J) sG0 sC0)
       (ev_step (j_atopG J) (EMmap 0 len prot MAPF)) (ev_step (j_atopC J) (EMmap 0 len prot MAPF)) (ev_post J (EMmap 0 len prot MAPF) (EMmap 0 len prot MAPF) sG0 sC0).
Proof.
  intros J len prot sG0 sC0 Hrel sG moG sC moC (-> & -> & HKR). split; [| intros trG Hx; exfalso; eapply ev_step_no_exit; exact Hx].
  intros trG zG sG' moG' HpG. pose proof HpG as HpG0. pose proof alloc_ceiling_lt as Hcl.
  assert (Hpl : (prot = PROT_NONE \/ prot = PROT_RW) /\ 0 < len < LEN_MAX).
  { cbn in Hrel. destruct Hrel as (_ & _ & _ & [(_ & _ & _ & _ & Hp & Hl)|(cG & cC & _ & _ & _ & _ & _ & E)]); [auto| discriminate]. }
  destruct Hpl as [Hp Hlen]. unfold LEN_MAX in Hlen.
  assert (Hf : Z.land MAPF MAP_FIXED_Z =? 0 = true) by reflexivity.
  apply (path_mmap_anon _ 0 len prot MAPF sG0) in HpG as (rspG & x & [HstG [HbG HnfG]] & HdG & -> & ->); [|exact Hf].
  destruct HKR as (KG & KC & Hlive & Hbnd & HlimC & (BE & RE & HX) & Hfds & Hfs & HB40).
  set (hG := m_vmmaps moG) in *. set (hC := m_vmmaps moC) in *. set (n := mmap_len len).
  Local Ltac2 Set LiaHints.tbl := fun () => "00_0>10357883337.6410359985988.6710364182376.7510364182468.6912217444581.6512291486129.6813016931423.4616682053794.5518509043169.7018758982334.3618764716734.3519334884097.6319336981330.7519336981502.6919341173630.6719612766780.7620890573598.4721990067913.7523252981666.7526445807723.4527530304463.6531102787792.523194594059.68 35790790815.7535794987473.7035797082843.7136411706135.6837581063772.7537594080453.6741415991886.6541422282358.644252372432.76 48846841881.6849283017102.6851426792568.6853028094078.5061929757509.7061931851943.7261934034731.4562378204190.6862465920981.8365037560242.7065041752370.686702166331.75 68057091018.7168390435239.658064927053.75 00000400800<00@00A00E00U00j01?01E01K01O01S01W01[01k02@02D02I02J02N02Q02R02l03F03`03f03j04104204304H04I04S04m05:05M05`06306M06]06m07=07D07Z07^07cS2HiS2HiS2HiS2HiSS2H2S3HbG4Hlen2Hn2A1S5Hlive3Hnp5Hbnd'3HnnS3ATC2A12Hc3HaC5HAtopS4HlenS4HlenS2HcS2HcS2HcS2HcS4Hlen2Hn3ATG2A3S5Hlive4Hlen2Hn5Hbnd'S2HiS3HszSS2HcS1HFS2A12Hc3Hsz3HaC4HA405HAtopS2A12Hc3Hsz3HaC4HA405HAtopS2A12Hc3Hsz3HaC4HA405HAtopS4HlenS2HcS2Hc2n0SSS2A12Hc3Hsz3HaC5HAtopFS2Hp2A12HcS3ATC4ATCe2A12Hc3HaC5HAtopS5Hlive5Hbnd'S4Hlen2Hn3ATG2A12A3S4Hlen2Hn3ATG2A12A3S4Hlen2Hn3ATG2A12A3S5Hlive5HlimC5Hbnd'6HbackCS2A12Hc3HaC4HA40S2A12Hc3HaC4HA40S2A12Hc3HaC4HA40S5HliveS3X402A12Hc3HaC4HA401HS2HcS3Hsz".
pose proof (mmap_len_ge len ltac:(lia)) as Hn. pose proof (mmap_len_pos_pg len ltac:(lia)) as Hnp. fold n in Hn, Hnp.
  pose proof (KL_atop_range _ _ _ KC) as ATC. cbn [ld_atop projC] in ATC. rewrite alloc_ceiling_lo_val, alloc_ceiling_val in ATC.
  pose proof (KL_atop_range _ _ _ KG) as ATG. cbn [ld_atop projG] in ATG. rewrite alloc_ceiling_lo_val, alloc_ceiling_val in ATG.
  pose proof (kl_atop _ _ _ KC) as ATCe. cbn [ld_atop projC] in ATCe. fold hC in ATCe.
  pose proof (nstep_mmap_anon_inv (j_atopG J) len prot moG rspG moG' trG Hlen Hp (kl_atop _ _ _ KG) HstG) as (-> & HvoG & x' & HdG' & Hx). fold hG n in Hx.
  rewrite HdG in HdG'. injection HdG' as <-.
  destruct x as [e|aG].
  - (* [comment removed for export] *)
    exfalso. assert (He : errno_of (eff_ret rspG) = Some e).
    { destruct (prot =? 0); [eapply dec_mmap_none_err_errno| eapply dec_mmap_err_errno]; exact HdG. }
    rewrite (HnfG _ _ _ HstG) in He. discriminate.
  - (* [comment removed for export] *)
    destruct Hx as (A1 & A2 & A3 & A4 & EvmG).
    assert (HliveG' : vm_live_bytes (m_vmmaps moG') = vm_live_bytes hG + n).
    { rewrite EvmG. unfold vm_live_bytes. cbn [vm_maps]. rewrite live_bytes_cons. unfold esz; cbn [snd]. rewrite unsigned_lit by lia. fold hG. lia. }
    assert (Hbnd' : vm_live_bytes hG + n <= LBND) by (rewrite HliveG' in HbG; fold hG in HbG; lia).
    fold hC in Hlive.
    pose proof (NICE_of_XMC hC BE RE HX ltac:(lia)) as HN. pose proof HX as HX0.
    assert (Hwf : forall e, In e (vm_maps hC) -> elo e < ehi e) by (intros e He; pose proof (proj1 (kl_wf _ _ _ KC) e He); lia).
    assert (Hbud : live_bytes (vm_maps hC) + n <= LIM) by (unfold vm_live_bytes in *; unfold LIM, LBND in *; lia).
    destruct (free_slot _ _ n HN Hwf Hbud Hnp) as (i & Hi & Hfree).
    pose proof (live_bytes_nonneg (vm_maps hC)) as Hnn.
    pose proof (cls_bounds n ltac:(unfold LIM, LBND in *; unfold vm_live_bytes in *; lia)) as [Hc Hsz].
    set (c := cls n) in *. set (aC := ARENA c + i * 2^c) in *.
    destruct HX as (XP & XBE & XRE & Xbrk & Xb0 & X40).
    assert (HaC : ABASE <= aC /\ aC + n <= ARENA 34 + 2^35).
    { subst aC. pose proof (ARENA_lo c ltac:(lia)). assert (0 <= i * 2^c) by (apply Z.mul_nonneg_nonneg; [lia| apply Z.pow_nonneg; lia]).
      assert (i * 2^c + 2^c <= 2^35). { rewrite (pow35_split c) by lia. assert (0 < 2^c) by (apply Z.pow_pos_nonneg; lia). nia. }
      assert (ARENA c + 2^35 <= ARENA 34 + 2^35). { destruct (Z.eq_dec c 34) as [->|]; [lia|]. pose proof (ARENA_mono c 34 ltac:(lia)). lia. } nia. }
    pose proof ABASE_40 as HA40. pose proof ARENA_top as HAtop. rewrite alloc_ceiling_lo_val in HAtop.
    pose proof (backing_le_live_minv moC (kl_minv _ _ _ KC)) as HbackC. fold hC in HbackC.
    assert (HstC : nstep (NMmap 0 len prot MAPF) moC
              (mkEffectU (Z_to_bv 64 aC) [] (if prot =? PROT_NONE then [] else [(Z_to_bv 64 aC, Z_to_bv 64 n)]) (if prot =? PROT_NONE then [(Z_to_bv 64 aC, Z_to_bv 64 n)] else []) [] [])
              (with_vmmaps (mkVmMapsFull (vm_reserved hC) ((Z_to_bv 64 aC, Z_to_bv 64 n) :: vm_maps hC)
                 (if prot =? PROT_NONE then (Z_to_bv 64 aC, Z_to_bv 64 n) :: vm_noaccess hC else vm_noaccess hC)
                 (vm_start_brk hC) (vm_brk hC) (vm_limit hC) (vm_mmap_base hC) (vm_init_sp hC)) moC) []).
    { apply (nstep_mmap_ok_intro len prot moC aC); fold hC n; try lia.
      - subst aC. apply ARENA_aligned; lia.
      - apply region_free_intro. intros e He. rewrite !unsigned_lit by lia. apply in_app_or in He as [He|He].
        + left. pose proof (kl_resv_top _ _ _ KC e He). fold hC in H. unfold CORR in *. lia.
        + apply Hfree. exact He.
      - unfold PGSZ in *. lia. }
    set (moC' := with_vmmaps _ moC) in HstC.
    assert (HdC : (if prot =? 0 then dec_mmap_none (j_atopC J) len [] (mkEffectU (Z_to_bv 64 aC) [] (if prot =? PROT_NONE then [] else [(Z_to_bv 64 aC, Z_to_bv 64 n)]) (if prot =? PROT_NONE then [(Z_to_bv 64 aC, Z_to_bv 64 n)] else []) [] [])
                   else dec_mmap (j_atopC J) len [] (mkEffectU (Z_to_bv 64 aC) [] (if prot =? PROT_NONE then [] else [(Z_to_bv 64 aC, Z_to_bv 64 n)]) (if prot =? PROT_NONE then [(Z_to_bv 64 aC, Z_to_bv 64 n)] else []) [] []))
                  = Some (MmOk aC)).
    { assert (Hok : mmap_addr_ok (j_atopC J) len [] aC = true).
      { unfold mmap_addr_ok. rewrite page_size_eq. replace (aC mod 4096) with 0 by (subst aC; symmetry; apply ARENA_aligned; lia). cbn [Z.eqb].
        rewrite (proj2 (Z.ltb_lt 0 aC)) by lia. fold n. rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity. }
      change PROT_NONE with 0. destruct (prot =? 0); unfold dec_mmap, dec_mmap_none; fold n; rewrite !bv_eqb_refl, unsigned_lit, Hok by lia; reflexivity. }
    assert (HpC : tpath nstep (ev_step (j_atopC J) (EMmap 0 len prot MAPF) sC0) moC [] (Ok (aC, sC0)) moC').
    { apply (path_mmap_anon _ 0 len prot MAPF sC0); [exact Hf|]. eexists; exists (MmOk aC). split; [exact HstC|]. auto. }
    exists [], aC, sC0, moC', []. split; [exact HpC|]. unfold debt0. rewrite !app_nil_r. split; [reflexivity|]. split; [reflexivity|].
    assert (Un : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
    assert (HvoC : vm_only moC moC') by (subst moC'; apply vm_only_with_vmmaps; reflexivity).
    destruct (tables_after _ _ _ _ HvoG HvoC Hfds Hfs) as [Hfds' Hfs'].
    apply (ev_post_intro J _ _ sG0 moG sC0 moC [] [] _ _ _ moG' _ moC').
    + exact Hrel.
    + unfold KR. splits; eauto.
    + exact HpG0.
    + exact HpC.
    + cbn -[is_err]. unfold is_err, TWO64. rewrite !(proj2 (Z.ltb_ge _ _)) by lia. reflexivity.
    + intros; discriminate.
    + intros; discriminate.
    + rewrite HliveG'. subst moC'. rewrite m_vmmaps_with_vmmaps. unfold vm_live_bytes in *. cbn [vm_maps]. rewrite live_bytes_cons. unfold esz; cbn [snd]. rewrite Un. lia.
    + rewrite HliveG'. exact Hbnd'.
    + subst moC'. rewrite m_vmmaps_with_vmmaps. cbn. exact HlimC.
    + exists BE, ((Z_to_bv 64 aC, Z_to_bv 64 n) :: RE). subst moC'. rewrite m_vmmaps_with_vmmaps. unfold XMC. cbn [vm_maps vm_start_brk vm_brk].
      splits; auto.
      * eapply Permutation_trans; [apply perm_skip; exact XP| apply Permutation_middle].
      * intros e [<-|He]; [|apply XRE; exact He]. exists c, i. rewrite elo_pair. unfold esz; cbn [snd]. rewrite unsigned_lit, Un by lia. splits; auto; lia.
    + exact Hfds'.
    + exact Hfs'.
    + apply (GB40_post _ _ _ HB40). intros; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma fixed_gate : forall L cur pbrk mo,
  KL L pbrk mo -> ld_brk L = BPGuard cur ->
  let h := m_vmmaps mo in let a := round_up_pg cur in
  a = cur /\ cur = bv_unsigned (vm_start_brk h) /\ bv_unsigned (vm_brk h) = cur + 2 * PGSZ /\ pbrk = cur + 2 * PGSZ
  /\ 0 < a /\ a + 2 * PGSZ <= alloc_top h < alloc_ceiling + 1 /\ a mod 4096 = 0    (* [comment removed for export] *)
  /\ region_free (vm_reserved h) (Z_to_bv 64 a) (Z_to_bv 64 PGSZ) = true
  /\ map_contains (vm_maps h) (Z_to_bv 64 a) (Z_to_bv 64 PGSZ) = true
  /\ exists e0, In e0 (vm_maps h) /\ elo e0 <= cur /\ cur + 2 * PGSZ <= ehi e0.
Proof.
  intros L cur pbrk mo HK Hph h a. pose proof alloc_ceiling_lt as Hcl.
  pose proof (KL_atop_range _ _ _ HK) as HKat. pose proof (kl_atop _ _ _ HK) as HKtop. fold h in HKtop.
  pose proof (kl_phase _ _ _ HK) as Kph. rewrite Hph in Kph. destruct Kph as (Ecur & Ebrk & Epbrk & Ereg & Hceil & (e0 & He0 & He0l & He0h) & Dg & Dm).
  pose proof (kl_start _ _ _ HK) as (S1 & S2 & S3 & S4). fold h in Ecur, Ebrk, He0, S1, S2, S3, S4.
  assert (Ha : a = cur). { subst a. apply round_up_pg_aligned. rewrite Ecur. exact S2. }
  Local Ltac2 Set LiaHints.tbl := fun () => "00:0>16967896987.2926983928455.2942465685538.2943471126322.2948914111491.2951026372527.2956765667309.2759577416033.2861335291095.296883411291.29 00000100=00F00G00P00\01401501E01FFS4Ecur2S12HaS4He0l2HaFS4He0h2HaS4HKat5HKtopS3Hcl4HKat4Ecur2S12S42HaSS5HKtop5Hceil2HaF".
assert (Ua : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit; unfold PGSZ in *; lia).
  assert (Un : bv_unsigned (Z_to_bv 64 PGSZ) = PGSZ) by (apply unsigned_lit; unfold PGSZ; lia).
  splits; auto; try lia.
  - rewrite Ha, Ecur. exact S2.
  - apply region_free_above. intros e He. rewrite Ua, Ha, Ecur. apply (kl_resv_top _ _ _ HK). exact He.
  - unfold map_contains. apply existsb_exists. exists e0. split; [exact He0|]. rewrite Ua, Un. unfold elo, ehi in He0l, He0h.
    rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by (unfold PGSZ in *; lia). reflexivity.
  - exists e0. auto.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

Lemma sim_mmap_fixed : forall J cG cC sG0 sC0,
  j_brk J = JGuard cG cC ->
  let aG := round_up_pg cG in let aC := round_up_pg cC in
  let eG := EMmap aG PGSZ PROT_NONE MAPFX in let eC := EMmap aC PGSZ PROT_NONE MAPFX in
  jev_rel J eG eC ->
  fsim debt0 debt0 stepB (pin (KRJ J) sG0 sC0) (ev_step (j_atopG J) eG) (ev_step (j_atopC J) eC) (ev_post J eG eC sG0 sC0).
Proof.
  intros J cG cC sG0 sC0 Hph aG aC eG eC Hrel sG moG sC moC (-> & -> & HKR). split; [| intros trG Hx; exfalso; eapply ev_step_no_exit; exact Hx].
  intros trG zG sG' moG' HpG. pose proof HpG as HpG0. pose proof alloc_ceiling_lt as Hcl.
  destruct HKR as (KG & KC & Hlive & Hbnd & HlimC & (BE & RE & HX) & Hfds & Hfs & HB40). pose proof HX as HX0.
  assert (HphG : ld_brk (projG J) = BPGuard cG) by (unfold projG; cbn; rewrite Hph; reflexivity).
  assert (HphC : ld_brk (projC J) = BPGuard cC) by (unfold projC; cbn; rewrite Hph; reflexivity).
  destruct (fixed_gate _ _ _ _ KG HphG) as (EaG & EcG & EbG & EpG & PaG & CaG & AaG & RfG & McG & _).
  destruct (fixed_gate _ _ _ _ KC HphC) as (EaC & EcC & EbC & EpC & PaC & CaC & AaC & RfC & McC & (e0 & He0 & He0l & He0h)).
  fold aG in EaG, PaG, CaG, AaG, RfG, McG. fold aC in EaC, PaC, CaC, AaC, RfC, McC.
  set (hG := m_vmmaps moG) in *. set (hC := m_vmmaps moC) in *.
  assert (Hf : Z.land MAPFX MAP_FIXED_Z =? 0 = false) by reflexivity.
  apply (path_mmap_fixed _ aG PGSZ PROT_NONE MAPFX sG0) in HpG as (rspG & x & [HstG [HbG HnfG]] & HdG & -> & ->); [|exact Hf].
  Local Ltac2 Set LiaHints.tbl := fun () => "00=0>12010102484.6615104755572.6718939340826.6824210388506.6824225066763.6924842579014.6528874572299.6835794986574.6436715178494.6947579392569.6157608325307.6959579513095.6560318969460.8100000100200300D00U00f01301D01I01N01O01P01^SSSS3Hcl3PaG3CaG3PaCS3Hcl3PaG3CaG3PaCS3Hcl3PaG3PaC3CaCS3Hcl3CaG3PaCS3Hcl3PaG3PaC3CaCS3CaCS3CaGSSS4Hbnd7HliveG'".
pose proof (nstep_mmap_fixed_inv aG moG rspG moG' trG PaG ltac:(subst hG; unfold PGSZ in *; lia) AaG RfG McG HstG) as (-> & HvoG & x' & HdG' & Hx).
  fold hG in Hx. rewrite HdG in HdG'. injection HdG' as <-.
  set (awC := Z_to_bv 64 aC) in *. set (nw := Z_to_bv 64 PGSZ) in *.
  assert (UaC : bv_unsigned awC = aC) by (subst awC; apply unsigned_lit; unfold PGSZ in *; lia).
  assert (Un : bv_unsigned nw = PGSZ) by (subst nw; apply unsigned_lit; unfold PGSZ; lia).
  assert (HdecD : dec_mmap_fixed aC PGSZ (mkEffectU awC [] [] [(awC, nw)] [] []) = Some FxDone).
  { unfold dec_mmap_fixed. subst awC nw. change (mmap_len PGSZ) with PGSZ. rewrite !bv_eqb_refl. cbn [andb]. rewrite errno_of_lit by (unfold PGSZ in *; lia). reflexivity. }
  (* [comment removed for export] *)
  assert (HliveG' : vm_live_bytes (m_vmmaps moG') <= vm_live_bytes hG).
  { destruct x as [e| |e].
    - destruct Hx as [_ ->]. fold hG. lia.
    - rewrite Hx. unfold vm_live_bytes. cbn [vm_maps]. fold hG. lia.
    - destruct Hx as [_ EvmG]. rewrite EvmG. unfold vm_live_bytes. cbn [vm_maps].
      pose proof (live_bytes_subtract (vm_maps hG) (Z_to_bv 64 aG) nw (kl_wf _ _ _ KG) ltac:(rewrite Un; unfold PGSZ; lia)
                    ltac:(rewrite unsigned_lit, Un by (unfold PGSZ in *; lia); unfold PGSZ in *; lia) McG) as HS.
      rewrite unsigned_lit, Un in HS by (unfold PGSZ in *; lia). fold hG in HS. rewrite HS. unfold PGSZ. lia. }
  (* [comment removed for export] *)
  assert (TAIL : forall rspC moC' xC, nstep (NMmap aC PGSZ PROT_NONE MAPFX) moC rspC moC' [] -> dec_mmap_fixed aC PGSZ rspC = Some xC ->
            vm_only moC moC' ->
            vm_live_bytes (m_vmmaps moG') = vm_live_bytes (m_vmmaps moC') ->
            vm_limit (m_vmmaps moC') = vm_limit hC ->
            (exists BE RE, XMC (m_vmmaps moC') BE RE) ->
            exists trC b sC' moC'' v, tpath nstep (ev_step (j_atopC J) eC sC0) moC trC (Ok (b, sC')) moC''
              /\ [] ++ debt0 sG0 = debt0 sG0 ++ v /\ trC ++ debt0 sC' = debt0 sC0 ++ v /\ ev_post J eG eC sG0 sC0 (fval aG x) b sG0 moG' sC' moC'').
  { intros rspC moC' xC HstC HdC HvoC L1 L4 L5.
    assert (HpC : tpath nstep (ev_step (j_atopC J) eC sC0) moC [] (Ok (fval aC xC, sC0)) moC').
    { apply (path_mmap_fixed _ aC PGSZ PROT_NONE MAPFX sC0); [exact Hf|]. exists rspC, xC. auto. }
    exists [], (fval aC xC), sC0, moC', []. split; [exact HpC|]. unfold debt0. rewrite !app_nil_r. split; [reflexivity|]. split; [reflexivity|].
    destruct (tables_after _ _ _ _ HvoG HvoC Hfds Hfs) as [Hfds' Hfs'].
    apply (ev_post_intro J eG eC sG0 moG sC0 moC [] [] _ _ _ moG' _ moC'); try assumption.
    - unfold KR. splits; eauto.
    - cbn. reflexivity.
    - intros; discriminate.
    - intros; discriminate.
    - fold hG in Hbnd. lia.
    - rewrite L4. exact HlimC. }
  (* [comment removed for export] *)
  pose proof (dec_mmap_fixed_err_errno _ _ _ _ HdG) as HerrG.
  destruct x as [e| |e]; [exfalso; rewrite (HnfG _ _ _ HstG) in HerrG; discriminate| |exfalso; rewrite (HnfG _ _ _ HstG) in HerrG; discriminate].
  - (* [comment removed for export] *)
    pose proof (nstep_fixed_done_intro aC moC PaC ltac:(subst hC; unfold PGSZ in *; lia) AaC RfC McC) as HstC. fold awC nw hC in HstC.
    eapply (TAIL _ _ FxDone HstC HdecD).
    + apply vm_only_fixed_done.
    + rewrite Hx, m_vmmaps_fixed_done. unfold fixed_done_h. cbn. exact Hlive.
    + rewrite m_vmmaps_fixed_done. reflexivity.
    + exists BE, RE. rewrite m_vmmaps_fixed_done. eapply XMC_same; [exact HX0| reflexivity| reflexivity| reflexivity].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma nstep_munmap_inv_has : forall a len mo rsp mo' evs,
  let h := m_vmmaps mo in let n := mmap_len len in let aw := Z_to_bv 64 a in let nw := Z_to_bv 64 n in
  0 <= a -> a mod 4096 = 0 -> 0 < len -> a + n <= TASK_SIZE -> map_has (vm_maps h) aw nw = true ->     (* [comment removed for export] *)
  nstep (NMunmap a len) mo rsp mo' evs ->
  evs = [] /\ vm_only mo mo' /\ rsp = mkEffectU (Z_to_bv 64 0) [] [] [(aw, nw)] [] []
  /\ mo' = with_mmap_destroyed aw nw (munmap_h h aw nw) mo.
Proof.
  intros a len mo rsp mo' evs h n aw nw Ha Hal Hlen Hb Hhas H. pose proof (mmap_len_ge len Hlen) as Hn. fold n in Hn. pose proof TASK_SIZE_val as TS.
  pose proof (nstep_mm_vm_only (NMunmap a len) mo rsp mo' evs I H) as [Hv ->]. split; [reflexivity|]. split; [exact Hv|].
  apply nstep_munmap_iff in H. destruct rsp as [r ws zs us cs ci]. unfold check_munmap in H. fold aw h in H.
  Local Ltac2 Set LiaHints.tbl := fun () => "0040>2017773237.24 2427180125.24 56765668728.2265120999233.2400000600=00O00aS4HlenS2Hb2UaS2Ha4Hlen2Hb2Hn2TSS2Ha4Hlen2Hb2Hn2TS".
assert (Ua : bv_unsigned aw = a) by (subst aw; apply unsigned_lit; lia).
  replace (negb (bv_unsigned aw mod page_size =? 0)) with false in H by (rewrite Ua, page_size_eq, Hal; reflexivity).
  rewrite w_is0_lit in H by lia. replace (len =? 0) with false in H by (symmetry; apply Z.eqb_neq; lia). cbn [orb] in H. cbv zeta in H.
  rewrite (unsigned_lit len) in H by lia. fold (mmap_len len) in H. fold n nw in H.
  replace (TASK_SIZE <? bv_unsigned aw + n) with false in H by (symmetry; apply Z.ltb_ge; lia). rewrite Hhas in H.
  destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct cs; [|destruct us; discriminate]. destruct ci; [|destruct us; discriminate].
  destruct (w_is0 r && listNN_eqb us [(aw, nw)]) eqn:E; [|discriminate]. injection H as <-.
  apply andb_prop in E as [E1 E2]. apply listNN_eqb_eq in E2. unfold w_is0 in E1. apply bv_eqb_eq in E1. subst r us.
  split; [reflexivity|]. unfold munmap_h. rewrite Ua. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
Lemma group_facts : forall L pbrk mo a l, KL L pbrk mo -> In (a, l) (ld_groups L) ->
  let n := mmap_len l in
  0 < l < LEN_MAX /\ 0 < a /\ a mod 4096 = 0 /\ a + n <= alloc_ceiling /\ PGSZ <= n /\ In (went a n) (vm_maps (m_vmmaps mo)).
Proof.
  intros L pbrk mo a l HK Hin n. pose proof (kl_groups _ _ _ HK a l Hin) as (G1 & G2 & G3 & G4 & G5 & G6). pose proof (KL_atop_range _ _ _ HK).
  Local Ltac2 Set LiaHints.tbl := fun () => "0040>12693366658.1512699655098.1612921049996.1639965899214.1600000400800<00BS2G1S2G1S2G1S2G41H".
pose proof (mmap_len_pos_pg l ltac:(lia)). unfold PGSZ in G3. splits; auto; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

Lemma sim_munmap : forall J aG aC len l sG0 sC0,
  In (aG, aC, l) (j_groups J) -> (len = l \/ len = round_up_pg l) ->
  jev_rel J (EMunmap aG len) (EMunmap aC len) ->
  fsim debt0 debt0 stepB (pin (KRJ J) sG0 sC0)
       (ev_step (j_atopG J) (EMunmap aG len)) (ev_step (j_atopC J) (EMunmap aC len)) (ev_post J (EMunmap aG len) (EMunmap aC len) sG0 sC0).
Proof.
  intros J aG aC len l sG0 sC0 Hin Hlen Hrel sG moG sC moC (-> & -> & HKR). split; [| intros trG Hx; exfalso; eapply ev_step_no_exit; exact Hx].
  intros trG zG sG' moG' HpG. pose proof HpG as HpG0. pose proof alloc_ceiling_lt as Hcl. pose proof alloc_ceiling_val as Hcv. pose proof TASK_SIZE_val as HTS.
  destruct HKR as (KG & KC & Hlive & Hbnd & HlimC & (BE & RE & HX) & Hfds & Hfs & HB40). pose proof HX as HX0.
  assert (HinG : In (aG, l) (ld_groups (projG J))) by (unfold projG; cbn; apply in_map_iff; exists (aG, aC, l); auto).
  assert (HinC : In (aC, l) (ld_groups (projC J))) by (unfold projC; cbn; apply in_map_iff; exists (aG, aC, l); auto).
  destruct (group_facts _ _ _ _ _ KG HinG) as (LG & PG & AG & CG & NG & MG).
  destruct (group_facts _ _ _ _ _ KC HinC) as (LC & PC & AC & CC & NC & MC).
  set (n := mmap_len l) in *. set (hG := m_vmmaps moG) in *. set (hC := m_vmmaps moC) in *.
  assert (Hll : 0 < len /\ mmap_len len = n).
  { rewrite round_up_pg_eq in Hlen. fold (mmap_len l) in Hlen. fold n in Hlen. Local Ltac2 Set LiaHints.tbl := fun () => "00>0>10157366173.5712699574543.4712699574543.482424873429.48 35797089073.7845500892925.5747845298470.5753392464346.4853512494145.6056340013752.7059310678500.7861931851943.6465037478718.5768116046959.7000000B00F00J00N01<01N01R01X01Y01b02D02U02Y02`S3Hcv3HTS2PG2PC2CCS2LGS2LGS2NGS3Hcv2PG2PC2CC2NC5Hlive4Hbnd4Xbrk3X402B21W3HBES3Hcv3HTS2PG2CG2PCS2PGS2LC1HSS4Hbnd2NCS5Hlive4Hbnd4Xbrk3X403H402B21W3HBES3Hcv2PG2CG2NG2PCS2PCS5Hlive".
destruct Hlen as [-> | ->]; [unfold LEN_MAX in LG; split; [lia| reflexivity]|].
    split; [unfold PGSZ in NG; lia|]. subst n. apply mmap_len_of_aligned; [pose proof (mmap_len_ge l ltac:(lia)); lia| apply mmap_len_aligned]. }
  destruct Hll as [Hlen0 Hn].
  apply path_munmap in HpG as (rspG & x & [HstG [HbG HnfG]] & HdG & -> & ->).
  assert (HhasG : map_has (vm_maps hG) (Z_to_bv 64 aG) (Z_to_bv 64 (mmap_len len)) = true).
  { rewrite Hn. unfold map_has. apply existsb_exists. exists (went aG n). split; [exact MG|]. unfold went, wz. cbn [fst snd]. rewrite !bv_eqb_refl. reflexivity. }
  assert (HhasC : map_has (vm_maps hC) (Z_to_bv 64 aC) (Z_to_bv 64 (mmap_len len)) = true).
  { rewrite Hn. unfold map_has. apply existsb_exists. exists (went aC n). split; [exact MC|]. unfold went, wz. cbn [fst snd]. rewrite !bv_eqb_refl. reflexivity. }
  pose proof (nstep_munmap_inv_has aG len moG rspG moG' trG ltac:(lia) AG Hlen0 ltac:(rewrite Hn; lia) HhasG HstG) as (-> & HvoG & -> & EmoG). rewrite Hn in EmoG.
  pose proof (nstep_munmap_intro aC len moC ltac:(lia) AC Hlen0 ltac:(rewrite Hn; lia) HhasC) as HstC. rewrite Hn in HstC. fold hC in HstC.
  set (moC' := with_mmap_destroyed _ _ _ moC) in HstC.
  assert (Hdec : forall a, dec_munmap a len (mkEffectU (Z_to_bv 64 0) [] [] [(Z_to_bv 64 a, Z_to_bv 64 n)] [] []) = Some (RgDone true)).
  { intros a. unfold dec_munmap. rewrite Hn, !bv_eqb_refl, unsigned_lit by lia. reflexivity. }
  rewrite Hn, Hdec in HdG. injection HdG as <-.
  assert (HpC : tpath nstep (ev_step (j_atopC J) (EMunmap aC len) sC0) moC [] (Ok (0, sC0)) moC').
  { apply path_munmap. eexists; exists (RgDone true). split; [exact HstC|]. split; [apply Hdec|]. auto. }
  exists [], 0, sC0, moC', []. split; [exact HpC|]. unfold debt0. rewrite !app_nil_r. split; [reflexivity|]. split; [reflexivity|].
  destruct HX as (XP & XBE & XRE & Xbrk & Xb0 & X40).
  assert (Un : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; unfold PGSZ in *; lia).
  assert (HvoC : vm_only moC moC') by (subst moC'; apply vm_only_destroyed; reflexivity).
  destruct (tables_after _ _ _ _ HvoG HvoC Hfds Hfs) as [Hfds' Hfs'].
  assert (EvmG : m_vmmaps moG' = munmap_h hG (Z_to_bv 64 aG) (Z_to_bv 64 n)) by (rewrite EmoG; apply m_vmmaps_munmap).
  assert (EvmC : m_vmmaps moC' = munmap_h hC (Z_to_bv 64 aC) (Z_to_bv 64 n)) by (subst moC'; apply m_vmmaps_munmap).
  apply (ev_post_intro J _ _ sG0 moG sC0 moC [] [] _ _ _ moG' _ moC').
  - exact Hrel.
  - unfold KR. splits; eauto.
  - exact HpG0.
  - exact HpC.
  - reflexivity.
  - intros aG' aC' len1 len2 E1 E2. injection E1 as <- <-. injection E2 as <- <-. intros g Hg.
    pose proof (kl_distinct _ _ _ KG) as DG. pose proof (kl_distinct _ _ _ KC) as DC. unfold projG, projC in DG, DC. cbn [ld_groups ld_metas] in DG, DC.
    apply List.NoDup_app_remove_r in DG. apply List.NoDup_app_remove_r in DC. rewrite map_map in DG, DC.
    split; intros E.
    + pose proof (nodup_map_inj (fun x => fst (gG x)) (j_groups J) g (aG, aC, l) DG Hg Hin) as Q. destruct g as [[bG bC] l']. cbn in E, Q |- *. specialize (Q ltac:(congruence)). congruence.
    + pose proof (nodup_map_inj (fun x => fst (gC x)) (j_groups J) g (aG, aC, l) DC Hg Hin) as Q. destruct g as [[bG bC] l']. cbn in E, Q |- *. specialize (Q ltac:(congruence)). congruence.
  - intros; discriminate.
  - rewrite EvmG, EvmC. unfold munmap_h, vm_live_bytes in *. cbn [vm_maps]. fold hG hC.
    rewrite (live_bytes_remove (vm_maps hG) (Z_to_bv 64 aG) (Z_to_bv 64 n) (kl_wf _ _ _ KG) MG).
    rewrite (live_bytes_remove (vm_maps hC) (Z_to_bv 64 aC) (Z_to_bv 64 n) (kl_wf _ _ _ KC) MC). fold hG hC. lia.
  - rewrite EvmG. unfold munmap_h, vm_live_bytes in *. cbn [vm_maps]. rewrite (live_bytes_remove (vm_maps hG) (Z_to_bv 64 aG) (Z_to_bv 64 n) (kl_wf _ _ _ KG) MG). fold hG. rewrite Un. unfold PGSZ in *; lia.
  - rewrite EvmC. unfold munmap_h. cbn [vm_limit]. exact HlimC.
  - exists BE, (map_remove RE (Z_to_bv 64 aC)). rewrite EvmC. unfold munmap_h, XMC. cbn [vm_maps vm_start_brk vm_brk]. splits; auto.
    + unfold map_remove. eapply Permutation_trans; [apply Permutation_filter; exact XP|]. rewrite List.filter_app.
      rewrite (filter_id _ BE); [apply Permutation_refl|]. intros e He. destruct (bv_eqb (fst e) (Z_to_bv 64 aC)) eqn:E; [|reflexivity]. exfalso.
      apply bv_eqb_eq in E. pose proof (HB40 aC l (or_introl HinC)) as H40.
      pose proof (XBE e He) as [B1 B2]. pose proof (proj1 (kl_wf _ _ _ KC) e ltac:(apply (Permutation_in _ (Permutation_sym XP)); apply in_or_app; left; exact He)) as W.
      pose proof (live_bytes_bound_BE hC BE RE HX0) as HBE. fold hC in Hlive.
      unfold elo, ehi in B1, B2, W. unfold CORR, LBND, PGSZ in *. rewrite E in B1, B2, W. rewrite unsigned_lit in B1, B2, W by lia. lia.
    + intros e He. unfold map_remove in He. apply filter_In in He as [He _]. apply XRE. exact He.
  - exact Hfds'.
  - exact Hfs'.
  - apply (GB40_post _ _ _ HB40). intros ? ? ? ? E; discriminate.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma meta_facts : forall L pbrk mo b l k, KL L pbrk mo -> In (b, l, k) (ld_metas L) -> (2 + k) * PGSZ <= round_up_pg l ->
  let n := mmap_len l in let a := b + (1 + k) * PGSZ in
  0 < b /\ b mod 4096 = 0 /\ 0 <= k /\ a + PGSZ <= b + n /\ b + n <= alloc_ceiling /\ PGSZ <= n
  /\ In (went b n) (vm_maps (m_vmmaps mo))
  /\ map_contains (vm_noaccess (m_vmmaps mo)) (Z_to_bv 64 a) (Z_to_bv 64 PGSZ) = true
  /\ map_contains (vm_maps (m_vmmaps mo)) (Z_to_bv 64 a) (Z_to_bv 64 PGSZ) = true.
Proof.
  intros L pbrk mo b l k HK Hin Hk n a. pose proof alloc_ceiling_lt as Hcl. pose proof (KL_atop_range _ _ _ HK) as HKat.
  pose proof (kl_metas _ _ _ HK b l k Hin) as (A1 & A2 & A3 & A4 & Ak & Ak1 & A5 & A6 & Ana).
  rewrite round_up_pg_eq in Hk. fold (mmap_len l) n in Hk, A4, Ak1, A5, A6, Ana |- *.
  Local Ltac2 Set LiaHints.tbl := fun () => "0080>12697679081.2220338765744.2529897934945.2830502795562.2858223035862.2558931930460.2559577416033.2461929578444.2500000400500:00?00C00W00X00lS2A1SS3HehS3HelS2HkS3Hcl4HKat2A22A43HnpSS3Hcl4HKat2A22A43Hnp".
pose proof (mmap_len_pos_pg l ltac:(lia)) as Hnp. fold n in Hnp.
  assert (Ua : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit; unfold PGSZ in *; nia).
  assert (Un : bv_unsigned (Z_to_bv 64 PGSZ) = PGSZ) by (apply unsigned_lit; unfold PGSZ; lia).
  unfold PGSZ in A3. splits; auto; try (unfold PGSZ in *; nia).
  - destruct (Ana (1 + k) ltac:(lia) ltac:(lia)) as (e & He & Hel & Heh). unfold map_contains. apply existsb_exists. exists e. split; [exact He|].
    rewrite Ua, Un. unfold elo, ehi in Hel, Heh. subst a. rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity.
  - unfold map_contains. apply existsb_exists. exists (went b n). split; [exact A5|]. rewrite Ua, Un. unfold went, wz. cbn [fst snd].
    rewrite !unsigned_lit by (unfold PGSZ in *; lia). rewrite (proj2 (Z.leb_le _ _)) by (unfold PGSZ in *; nia). rewrite (proj2 (Z.leb_le _ _)) by (unfold PGSZ in *; nia). reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
Lemma meta_target_unique : forall L pbrk mo b l k b' l' k', KL L pbrk mo ->
  In (b, l, k) (ld_metas L) -> (2 + k) * PGSZ <= round_up_pg l -> In (b', l', k') (ld_metas L) ->
  b' + (1 + k') * PGSZ = b + (1 + k) * PGSZ -> (b', l', k') = (b, l, k).
Proof.
  intros L pbrk mo b l k b' l' k' HK Hin Hk Hin' E. pose proof alloc_ceiling_lt as Hcl. pose proof (KL_atop_range _ _ _ HK) as HKat.
  pose proof (kl_metas _ _ _ HK b l k Hin) as (A1 & A2 & A3 & A4 & Ak & Ak1 & A5 & _).
  pose proof (kl_metas _ _ _ HK b' l' k' Hin') as (B1 & B2 & B3 & B4 & Bk & Bk1 & B5 & _).
  rewrite round_up_pg_eq in Hk. fold (mmap_len l) in Hk.
  Local Ltac2 Set LiaHints.tbl := fun () => "0080>12699818045.3022492006009.3422494091162.3441663588811.3147962361464.3454429705994.3458931667413.3458937946166.3400000400M00f00j01B01[02302KS2A1S3Hcl4HKat2A22B12B22B42H0S3Hcl4HKat2A22B12B22B42H0S2B1S3Hcl4HKat2A12A22A42B21HS3Hcl4HKat2A22B12B22B42H0S3Hcl4HKat2A12A22A42B21HS3Hcl4HKat2A12A22A42B21H".
pose proof (mmap_len_ge l ltac:(lia)). pose proof (mmap_len_ge l' ltac:(lia)).
  destruct (Z.eq_dec b' b) as [->|Hne].
  - pose proof (kl_distinct _ _ _ HK) as Hd. apply List.NoDup_app_remove_l in Hd.
    exact (nodup_map_inj _ _ _ _ Hd Hin' Hin eq_refl).
  - exfalso. destruct (pwdisj_In _ _ _ (proj2 (kl_wf _ _ _ HK)) B5 A5) as [Ee|D].
    + apply Hne. apply (f_equal elo) in Ee. rewrite !elo_went in Ee by lia. exact Ee.
    + unfold edisj in D. rewrite !elo_went, !ehi_went in D by lia. unfold PGSZ in *. nia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

Lemma sim_mprotect : forall J bG bC l k sG0 sC0,
  In (bG, bC, l, k) (j_metas J) -> (2 + k) * PGSZ <= round_up_pg l ->
  let aG := bG + (1 + k) * PGSZ in let aC := bC + (1 + k) * PGSZ in
  jev_rel J (EMprotect aG PGSZ PROT_RW) (EMprotect aC PGSZ PROT_RW) ->
  fsim debt0 debt0 stepB (pin (KRJ J) sG0 sC0)
       (ev_step (j_atopG J) (EMprotect aG PGSZ PROT_RW)) (ev_step (j_atopC J) (EMprotect aC PGSZ PROT_RW))
       (ev_post J (EMprotect aG PGSZ PROT_RW) (EMprotect aC PGSZ PROT_RW) sG0 sC0).
Proof.
  intros J bG bC l k sG0 sC0 Hin Hk aG aC Hrel sG moG sC moC (-> & -> & HKR). split; [| intros trG Hx; exfalso; eapply ev_step_no_exit; exact Hx].
  intros trG zG sG' moG' HpG. pose proof HpG as HpG0. pose proof alloc_ceiling_lt as Hcl.
  destruct HKR as (KG & KC & Hlive & Hbnd & HlimC & (BE & RE & HX) & Hfds & Hfs & HB40). pose proof HX as HX0.
  assert (HinG : In (bG, l, k) (ld_metas (projG J))) by (unfold projG; cbn; apply in_map_iff; exists (bG, bC, l, k); auto).
  assert (HinC : In (bC, l, k) (ld_metas (projC J))) by (unfold projC; cbn; apply in_map_iff; exists (bG, bC, l, k); auto).
  destruct (meta_facts _ _ _ _ _ _ KG HinG Hk) as (PG & AG & KkG & EG & CG & NG & MG & NcG & McG).
  destruct (meta_facts _ _ _ _ _ _ KC HinC Hk) as (PC & AC & KkC & EC & CC & NC & MC & NcC & McC).
  fold aG in EG, NcG, McG. fold aC in EC, NcC, McC.
  set (n := mmap_len l) in *. set (hG := m_vmmaps moG) in *. set (hC := m_vmmaps moC) in *.
  assert (HaG : 0 <= aG /\ aG + PGSZ < 2^64 /\ aG mod 4096 = 0).
  { subst aG. unfold PGSZ in *. split; [nia|]. split; [nia|]. Local Ltac2 Set LiaHints.tbl := fun () => "0070>18926758295.6618928763969.5518928846669.5624222971799.6653506578343.7053645291812.6968077226220.6600000100200300>00?00Q00RSSSS4HaG14HaG2SS5Hlive4Hbnd5HlimCS".
rewrite Z.add_mod, AG, Z.mod_mul by lia. reflexivity. }
  assert (HaC : 0 <= aC /\ aC + PGSZ < 2^64 /\ aC mod 4096 = 0).
  { subst aC. unfold PGSZ in *. split; [nia|]. split; [nia|]. rewrite Z.add_mod, AC, Z.mod_mul by lia. reflexivity. }
  destruct HaG as (HaG1 & HaG2 & HaG3). destruct HaC as (HaC1 & HaC2 & HaC3).
  apply path_mprotect in HpG as (rspG & x & [HstG [HbG HnfG]] & HdGrw & -> & ->).
  assert (HdG : dec_mprotect aG PGSZ rspG = Some x).
  { unfold dec_mprotect_rw in HdGrw. destruct (dec_mprotect aG PGSZ rspG) as [[e|[|]]|]; try discriminate.
    - destruct (e =? ENOSYS); [discriminate|]. exact HdGrw.
    - exact HdGrw. }
  pose proof (nstep_dec_mprotect aG PGSZ moG rspG moG' trG ltac:(unfold PGSZ in *; lia) ltac:(unfold PGSZ; lia) ltac:(change (mmap_len PGSZ) with PGSZ; unfold PGSZ; lia) HstG) as (-> & HvoG & x' & HdG' & Hx).
  rewrite HdG in HdG'. injection HdG' as <-.
  (* [comment removed for export] *)
  assert (HmapsG : vm_maps (m_vmmaps moG') = vm_maps hG /\ vm_limit (m_vmmaps moG') = vm_limit hG).
  { destruct x as [e|[|]]; [destruct Hx as [_ ->]| destruct Hx as (_ & _ & E); rewrite E| rewrite Hx]; auto. }
  destruct HmapsG as [HmG HlimG].
  assert (TAIL : forall rspC moC' xC, nstep (NMprotect aC PGSZ PROT_RW) moC rspC moC' [] -> dec_mprotect_rw aC PGSZ rspC = Some xC ->
            mprot_okb (rval x) = mprot_okb (rval xC) -> vm_only moC moC' ->
            vm_maps (m_vmmaps moC') = vm_maps hC -> vm_start_brk (m_vmmaps moC') = vm_start_brk hC -> vm_brk (m_vmmaps moC') = vm_brk hC -> vm_limit (m_vmmaps moC') = vm_limit hC ->
            exists trC b sC' moC'' v, tpath nstep (ev_step (j_atopC J) (EMprotect aC PGSZ PROT_RW) sC0) moC trC (Ok (b, sC')) moC''
              /\ [] ++ debt0 sG0 = debt0 sG0 ++ v /\ trC ++ debt0 sC' = debt0 sC0 ++ v
              /\ ev_post J (EMprotect aG PGSZ PROT_RW) (EMprotect aC PGSZ PROT_RW) sG0 sC0 (rval x) b sG0 moG' sC' moC'').
  { intros rspC moC' xC HstC HdC Hcls HvoC E1 E2 E3 E4.
    assert (HpC : tpath nstep (ev_step (j_atopC J) (EMprotect aC PGSZ PROT_RW) sC0) moC [] (Ok (rval xC, sC0)) moC').
    { apply path_mprotect. exists rspC, xC. auto. }
    exists [], (rval xC), sC0, moC', []. split; [exact HpC|]. unfold debt0. rewrite !app_nil_r. split; [reflexivity|]. split; [reflexivity|].
    destruct (tables_after _ _ _ _ HvoG HvoC Hfds Hfs) as [Hfds' Hfs'].
    apply (ev_post_intro J _ _ sG0 moG sC0 moC [] [] _ _ _ moG' _ moC').
    - exact Hrel.
    - unfold KR. splits; eauto.
    - exact HpG0.
    - exact HpC.
    - cbn [same_class]. rewrite Hcls. destruct (mprot_okb (rval xC)); reflexivity.
    - intros; discriminate.
    - intros aG' aC' l1 l2 p p' Ea Eb. injection Ea as <- <- <-. injection Eb as <- <- <-. intros bG' bC' l' k' Hin'.
      pose proof (kl_distinct _ _ _ KG) as DG. pose proof (kl_distinct _ _ _ KC) as DC. unfold projG, projC in DG, DC. cbn [ld_groups ld_metas] in DG, DC.
      apply List.NoDup_app_remove_l in DG. apply List.NoDup_app_remove_l in DC. rewrite map_map in DG, DC.
      assert (HinG' : In (bG', l', k') (ld_metas (projG J))) by (unfold projG; cbn; apply in_map_iff; exists (bG', bC', l', k'); auto).
      assert (HinC' : In (bC', l', k') (ld_metas (projC J))) by (unfold projC; cbn; apply in_map_iff; exists (bG', bC', l', k'); auto).
      split; intros E.
      + pose proof (meta_target_unique _ _ _ _ _ _ _ _ _ KG HinG Hk HinG' E) as Q. injection Q as -> -> ->.
        pose proof (nodup_map_inj (fun x => fst (fst (mG x))) (j_metas J) _ _ DG Hin' Hin eq_refl) as Q. injection Q as ->. reflexivity.
      + pose proof (meta_target_unique _ _ _ _ _ _ _ _ _ KC HinC Hk HinC' E) as Q. injection Q as -> -> ->.
        pose proof (nodup_map_inj (fun x => fst (fst (mC x))) (j_metas J) _ _ DC Hin' Hin eq_refl) as Q. injection Q as ->. reflexivity.
    - unfold vm_live_bytes in *. rewrite HmG, E1. exact Hlive.
    - unfold vm_live_bytes in *. rewrite HmG. exact Hbnd.
    - rewrite E4. exact HlimC.
    - exists BE, RE. eapply XMC_same; [exact HX0| exact E1| exact E2| exact E3].
    - exact Hfds'.
    - exact Hfs'.
    - apply (GB40_post _ _ _ HB40). intros ? ? ? ? Ee; discriminate. }
  destruct x as [e|b].
  - (* [comment removed for export] *)
    exfalso. pose proof (dec_mprotect_err_errno _ _ _ _ HdG) as He. rewrite (HnfG _ _ _ HstG) in He. discriminate.
  - (* [comment removed for export] *)
    assert (Eb : b = true). { destruct b; [reflexivity|]. unfold dec_mprotect_rw in HdGrw. rewrite HdG in HdGrw. discriminate. } subst b.
    fold hC in Hlive.
    pose proof (nstep_mprotect_ok_intro aC moC HaC1 HaC2 HaC3 NcC McC ltac:(fold hC; unfold LBND, PGSZ in *; lia) (kl_minv _ _ _ KC)) as HstC.
    eapply (TAIL _ _ (RgDone true) HstC).
    + unfold dec_mprotect_rw, dec_mprotect. change (mmap_len PGSZ) with PGSZ. rewrite !bv_eqb_refl, unsigned_lit by lia. reflexivity.
    + reflexivity.
    + apply vm_only_mprotect_next.
    + rewrite (m_vmmaps_mprotect_next aC moC HaC1 HaC2). reflexivity.
    + rewrite (m_vmmaps_mprotect_next aC moC HaC1 HaC2). reflexivity.
    + rewrite (m_vmmaps_mprotect_next aC moC HaC1 HaC2). reflexivity.
    + rewrite (m_vmmaps_mprotect_next aC moC HaC1 HaC2). reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition embed_post {R1 R2} (J : jled) (tG : stree ev Z R1) (tC : stree ev Z R2) (Post : jled -> R1 -> R2 -> Prop)
  (sG0 sC0 : PState) : R1 -> R2 -> rel PState PState :=
  fun rG rC sG moG sC moC =>
    exists J', jcpath J tG tC J' rG rC /\ Post J' rG rC /\ KR J' sG moG sC moC
    /\ ps_m sG = ps_m sG0 /\ ps_fa sG = ps_fa sG0 /\ ps_so sG = ps_so sG0
    /\ ps_m sC = ps_m sC0 /\ ps_fa sC = ps_fa sC0 /\ ps_so sC = ps_so sC0.

(* [comment removed for export] *)
Lemma jevent_post_atops : forall J eG eC zG zC,
  j_atopG (jevent_post J eG eC zG zC) = j_atopG J /\ j_atopC (jevent_post J eG eC zG zC) = j_atopC J.
Proof.
  intros J eG eC zG zC. unfold jevent_post.
  repeat (first [split; reflexivity | match goal with |- context [match ?x with _ => _ end] => destruct x end]).
Qed.
