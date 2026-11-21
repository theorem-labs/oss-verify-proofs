(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.Lib Require Import PropExec MState ITree Nodes Decode.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.Spec Require Import Prelim Monad MSafe Sim MPaths STree Malloc KInv KStep PState KLink KEv JLedger Relim StepB EquivK_iface EKPlace.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.FO Require Import FOCore.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).
Local Notation MP := (Monad.M PState).


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


Section EvPaths.
Context {stp : node -> Model -> resp -> Model -> list event -> Prop}.
Context (atop : Z).

Lemma ev_step_no_exit : forall e s mo tr, ~ texit stp nexit (ev_step atop e s) mo tr.
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

Lemma path_brk0 : forall s mo tr z s' mo',
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

Lemma path_brk_grow : forall req s mo tr z s' mo', req <> 0 ->
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

Lemma path_mmap_anon : forall addr len prot flags s mo tr z s',
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

Lemma path_mmap_fixed : forall addr len prot flags s mo tr z s' mo',
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

Lemma path_munmap : forall addr len s mo tr z s' mo',
  tpath stp (ev_step atop (EMunmap addr len) s) mo tr (Ok (z, s')) mo' <->
  exists rsp x, stp (NMunmap addr len) mo rsp mo' tr /\ dec_munmap addr len rsp = Some x /\ z = rval x /\ s' = s.
Proof.
  intros addr len s mo tr z s' mo'. unfold ev_step. rewrite tpath_mbind_ok. split.
  - intros (tr1 & a & s1 & mo1 & tr2 & H1 & H2 & ->). apply tpath_msys_ok in H1 as (rsp & Hst & Hd & ->).
    apply (tpath_mret (st:=stp)) in H2 as (E & -> & ->). inversion E; subst; clear E. exists rsp, a. rewrite app_nil_r. auto.
  - intros (rsp & a & Hst & Hd & -> & ->). exists tr, a, s, mo', []. rewrite app_nil_r. split; [apply tpath_msys_ok; exists rsp; auto|]. split; [apply (tpath_mret (st:=stp)); auto| reflexivity].
Qed.

Lemma path_mprotect : forall addr len prot s mo tr z s' mo',
  tpath stp (ev_step atop (EMprotect addr len prot) s) mo tr (Ok (z, s')) mo' <->
  exists rsp x, stp (NMprotect addr len prot) mo rsp mo' tr /\ dec_mprotect_rw addr len rsp = Some x /\ z = rval x /\ s' = s.
Proof.
  intros addr len prot s mo tr z s' mo'. unfold ev_step. rewrite tpath_mbind_ok. split.
  - intros (tr1 & a & s1 & mo1 & tr2 & H1 & H2 & ->). apply tpath_msys_ok in H1 as (rsp & Hst & Hd & ->).
    apply (tpath_mret (st:=stp)) in H2 as (E & -> & ->). inversion E; subst; clear E. exists rsp, a. rewrite app_nil_r. auto.
  - intros (rsp & a & Hst & Hd & -> & ->). exists tr, a, s, mo', []. rewrite app_nil_r. split; [apply tpath_msys_ok; exists rsp; auto|]. split; [apply (tpath_mret (st:=stp)); auto| reflexivity].
Qed.
End EvPaths.

Lemma mspec_tpath {St A} : forall (P : assn St) (m : Monad.M St A) Q s mo tr a s' mo',
  mspec P m Q -> P s mo -> tpath nstep (m s) mo tr (Ok (a, s')) mo' -> Q a s' mo'.
Proof.
  intros P m Q s mo tr a s' mo' Hm HP Hp. pose proof (twf_tpath _ _ _ _ _ _ (Hm s mo HP) Hp) as H. cbn in H. exact H.
Qed.

Lemma frame_ok_true : frame_ok (fun _ _ => True).
Proof. intros ? ? ? ? ? ? ? ?. exact I. Qed.

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


Definition XMC (h : VmMaps) (BE RE : list (word * word)) : Prop :=
  let b0 := bv_unsigned (vm_start_brk h) in
  Permutation (vm_maps h) (BE ++ RE)
  /\ (forall e, In e BE -> b0 <= elo e /\ ehi e <= bv_unsigned (vm_brk h))
  /\ (forall e, In e RE -> slab_entry e)
  /\ bv_unsigned (vm_brk h) <= b0 + live_bytes BE + PGSZ
  /\ 0 < b0 /\ b0 + CORR <= 2^40.

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


Definition KRJ (J : jled) : rel PState PState := fun sG moG sC moC => KR J sG moG sC moC.

Lemma brk_model_next_limit : forall h req r, vm_limit (brk_model_next h req r) = vm_limit h.
Proof. reflexivity. Qed.

Lemma XMC_same : forall h h' BE RE, XMC h BE RE ->
  vm_maps h' = vm_maps h -> vm_start_brk h' = vm_start_brk h -> vm_brk h' = vm_brk h -> XMC h' BE RE.
Proof. intros h h' BE RE HX E1 E2 E3. unfold XMC in *. rewrite E1, E2, E3. exact HX. Qed.

Lemma live_bytes_bound_BE : forall h BE RE, XMC h BE RE -> live_bytes BE <= vm_live_bytes h.
Proof.
  intros h BE RE (HP & _). unfold vm_live_bytes. rewrite (live_bytes_perm _ _ HP), live_bytes_app. pose proof (live_bytes_nonneg RE). lia.
Qed.

Lemma tables_after : forall moG moG' moC moC',
  vm_only moG moG' -> vm_only moC moC' -> m_fds moG = m_fds moC -> m_fs moG = m_fs moC ->
  m_fds moG' = m_fds moC' /\ m_fs moG' = m_fs moC'.
Proof.
  intros moG moG' moC moC' HvG HvC Hf Hs. destruct (vm_only_tables _ _ HvG) as [F1 F2]. destruct (vm_only_tables _ _ HvC) as [F3 F4].
  rewrite F1, F2, F3, F4. auto.
Qed.


Lemma sim_brk0 : forall J sG0 sC0, j_brk J = JUntried ->
  fsim debt0 debt0 stepB (pin (KRJ J) sG0 sC0) (ev_step (j_atopG J) (EBrk 0)) (ev_step (j_atopC J) (EBrk 0)) (ev_post J (EBrk 0) (EBrk 0) sG0 sC0).
Proof.
  intros J sG0 sC0 Hph sG moG sC moC (-> & -> & HKR). split; [| intros trG Hx; exfalso; eapply ev_step_no_exit; exact Hx].
  intros trG zG sG' moG' HpG. pose proof HpG as HpG0. apply path_brk0 in HpG as (rspG & [HstG [HbG HnfG]] & HdG & ->).
  destruct HKR as (KG & KC & Hlive & Hbnd & HlimC & (BE & RE & HX) & Hfds & Hfs & HB40).
  pose proof (nstep_dec_brk0 _ _ _ _ HstG) as (-> & HdG' & HvoG & HbrkG).
  pose proof (nstep_brk_inv _ _ _ _ _ HstG) as (rG & HrG & EmoG & _ & _). apply brk_r_ok_query in HrG. subst rG.
  rewrite with_brk_next_noshrink in EmoG by lia.
  pose proof (brk_model_next_query (m_vmmaps moG)) as (QG1 & QG2 & QG3 & QG4 & QG5).
  set (hC := m_vmmaps moC).
  pose proof (nstep_brk_intro 0 moC (vm_brk hC) (brk_r_ok_refuse moC (Z_to_bv 64 0)) eq_refl) as HstC. fold hC in HstC.
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
Qed.

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
    rewrite !round_up_pg_aligned by (subst; assumption). splits; lia.
  - rewrite Hph, Hreg in PG, PC. cbn in PG, PC. destruct PG as (bG' & l' & E1 & EG2 & EG3). injection E1 as <- <-.
    destruct PC as (bC' & l'' & E2 & EC2 & EC3). injection E2 as <- <-.
    pose proof (kl_brkreg _ _ _ KG bG l) as RG. pose proof (kl_brkreg _ _ _ KC bC l) as RC. cbn [projG projC ld_brkreg option_map rG rC] in RG, RC.
    rewrite Hreg in RG, RC. cbn in RG, RC. specialize (RG eq_refl). specialize (RC eq_refl).
    destruct RG as (RG1 & RG2 & RG3 & RG4 & RG5 & _). destruct RC as (RC1 & RC2 & RC3 & RC4 & RC5 & _).
    exists PGSZ. split; [left; reflexivity|]. unfold PGSZ in *. splits; try lia.
    all: try (rewrite EG2; rewrite Z.add_mod, RG2, RG4 by lia; reflexivity).
    all: try (rewrite EC2; rewrite Z.add_mod, RC2, RC4 by lia; reflexivity).
Qed.

Lemma nstep_mmap_anon_inv : forall atop len prot mo rsp mo' evs,
  let h := m_vmmaps mo in let n := mmap_len len in
  0 < len < 2^63 -> (prot = PROT_NONE \/ prot = PROT_RW) ->
  atop = alloc_top h ->
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
  intros atop len prot mo rsp mo' evs h n Hlen Hp Hat H. pose proof (mmap_len_ge len ltac:(lia)) as Hn. fold n in Hn.
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
Qed.

Lemma NICE_of_XMC : forall h BE RE, XMC h BE RE -> vm_live_bytes h <= LBND -> NICE (bv_unsigned (vm_start_brk h)) (vm_maps h).
Proof.
  intros h BE RE HX Hlim. pose proof (live_bytes_perm _ _ (proj1 HX)) as HPl. destruct HX as (XP & XBE & XRE & Xbrk & Xb0 & X40).
  unfold vm_live_bytes in Hlim. rewrite HPl, live_bytes_app in Hlim. pose proof (live_bytes_nonneg RE).
  split; [|split; [exact Xb0| exact X40]]. intros e He. apply (Permutation_in _ XP) in He. apply in_app_or in He as [He|He].
  - left. specialize (XBE e He). unfold in_corr, CORR, LBND, PGSZ in *. lia.
  - right. apply XRE. exact He.
Qed.

(* sim_mmap_anon left out: unused; its C step picks a canonical arena slot, and at an anonymous NULL-hint grant is Linux placement only (linux_place_is), so it cannot hold *)


Lemma fixed_gate : forall L cur pbrk mo,
  KL L pbrk mo -> ld_brk L = BPGuard cur ->
  let h := m_vmmaps mo in let a := round_up_pg cur in
  a = cur /\ cur = bv_unsigned (vm_start_brk h) /\ bv_unsigned (vm_brk h) = cur + 2 * PGSZ /\ pbrk = cur + 2 * PGSZ
  /\ 0 < a /\ a + 2 * PGSZ <= alloc_top h < alloc_ceiling + 1 /\ a mod 4096 = 0
  /\ region_free (vm_reserved h) (Z_to_bv 64 a) (Z_to_bv 64 PGSZ) = true
  /\ map_contains (vm_maps h) (Z_to_bv 64 a) (Z_to_bv 64 PGSZ) = true
  /\ exists e0, In e0 (vm_maps h) /\ elo e0 <= cur /\ cur + 2 * PGSZ <= ehi e0.
Proof.
  intros L cur pbrk mo HK Hph h a. pose proof alloc_ceiling_lt as Hcl.
  pose proof (KL_atop_range _ _ _ HK) as HKat. pose proof (kl_atop _ _ _ HK) as HKtop. fold h in HKtop.
  pose proof (kl_phase _ _ _ HK) as Kph. rewrite Hph in Kph. destruct Kph as (Ecur & Ebrk & Epbrk & Ereg & Hceil & (e0 & He0 & He0l & He0h) & Dg & Dm).
  pose proof (kl_start _ _ _ HK) as (S1 & S2 & S3 & S4). fold h in Ecur, Ebrk, He0, S1, S2, S3, S4.
  assert (Ha : a = cur). { subst a. apply round_up_pg_aligned. rewrite Ecur. exact S2. }
  assert (Ua : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit; unfold PGSZ in *; lia).
  assert (Un : bv_unsigned (Z_to_bv 64 PGSZ) = PGSZ) by (apply unsigned_lit; unfold PGSZ; lia).
  splits; auto; try lia.
  - rewrite Ha, Ecur. exact S2.
  - (* port727: kl_resv_top is two-sided at (the vDSO pair sits 4 pages or more above
       start_brk), so the guard page misses every reserved entry, as in Spec/KEv and Spec/LB_KCount. *)
    apply region_free_sep. intros e He. rewrite Ua, Un, Ha, Ecur.
    destruct (kl_resv_top _ _ _ HK e He) as [E|E]; [left; exact E| right; fold h in E; unfold PGSZ in *; lia].
  - unfold map_contains. apply existsb_exists. exists e0. split; [exact He0|]. rewrite Ua, Un. unfold elo, ehi in He0l, He0h.
    rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by (unfold PGSZ in *; lia). reflexivity.
  - exists e0. auto.
Qed.

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
  pose proof (nstep_mmap_fixed_inv aG moG rspG moG' trG PaG ltac:(subst hG; unfold PGSZ in *; lia) AaG RfG McG HstG) as (-> & HvoG & x' & HdG' & Hx).
  fold hG in Hx. rewrite HdG in HdG'. injection HdG' as <-.
  set (awC := Z_to_bv 64 aC) in *. set (nw := Z_to_bv 64 PGSZ) in *.
  assert (UaC : bv_unsigned awC = aC) by (subst awC; apply unsigned_lit; unfold PGSZ in *; lia).
  assert (Un : bv_unsigned nw = PGSZ) by (subst nw; apply unsigned_lit; unfold PGSZ; lia).
  assert (HdecD : dec_mmap_fixed aC PGSZ (mkEffectU awC [] [] [(awC, nw)] [] []) = Some FxDone).
  { unfold dec_mmap_fixed. subst awC nw. change (mmap_len PGSZ) with PGSZ. rewrite !bv_eqb_refl. cbn [andb]. rewrite errno_of_lit by (unfold PGSZ in *; lia). reflexivity. }
  assert (HliveG' : vm_live_bytes (m_vmmaps moG') <= vm_live_bytes hG).
  { destruct x as [e| |e].
    - destruct Hx as [_ ->]. fold hG. lia.
    - rewrite Hx. unfold vm_live_bytes. cbn [vm_maps]. fold hG. lia.
    - destruct Hx as [_ EvmG]. rewrite EvmG. unfold vm_live_bytes. cbn [vm_maps].
      pose proof (live_bytes_subtract (vm_maps hG) (Z_to_bv 64 aG) nw (kl_wf _ _ _ KG) ltac:(rewrite Un; unfold PGSZ; lia)
                    ltac:(rewrite unsigned_lit, Un by (unfold PGSZ in *; lia); unfold PGSZ in *; lia) McG) as HS.
      rewrite unsigned_lit, Un in HS by (unfold PGSZ in *; lia). fold hG in HS. rewrite HS. unfold PGSZ. lia. }
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
  pose proof (dec_mmap_fixed_err_errno _ _ _ _ HdG) as HerrG.
  destruct x as [e| |e]; [exfalso; rewrite (HnfG _ _ _ HstG) in HerrG; discriminate| |exfalso; rewrite (HnfG _ _ _ HstG) in HerrG; discriminate].
  -
    pose proof (nstep_fixed_done_intro aC moC PaC ltac:(subst hC; unfold PGSZ in *; lia) AaC RfC McC) as HstC. fold awC nw hC in HstC.
    eapply (TAIL _ _ FxDone HstC HdecD).
    + apply vm_only_fixed_done.
    + rewrite Hx, m_vmmaps_fixed_done. unfold fixed_done_h. cbn. exact Hlive.
    + rewrite m_vmmaps_fixed_done. reflexivity.
    + exists BE, RE. rewrite m_vmmaps_fixed_done. eapply XMC_same; [exact HX0| reflexivity| reflexivity| reflexivity].
Qed.


(* nstep_munmap_inv_has left out: unused; at check_munmap answers the injected ENOMEM first and its kept arm returns mmap_fixed_destroyed_next, so the inversion needs real proof work and the donor apartness premise (sim_munmap rests on it) *)

Lemma group_facts : forall L pbrk mo a l, KL L pbrk mo -> In (a, l) (ld_groups L) ->
  let n := mmap_len l in
  0 < l < LEN_MAX /\ 0 < a /\ a mod 4096 = 0 /\ a + n <= alloc_ceiling /\ PGSZ <= n /\ In (went a n) (vm_maps (m_vmmaps mo)).
Proof.
  intros L pbrk mo a l HK Hin n. pose proof (kl_groups _ _ _ HK a l Hin) as (G1 & G2 & G3 & G4 & G5 & G6). pose proof (KL_atop_range _ _ _ HK).
  pose proof (mmap_len_pos_pg l ltac:(lia)). unfold PGSZ in G3. splits; auto; lia.
Qed.

(* sim_munmap left out: unused; at check_munmap answers the injected ENOMEM first and its kept arm returns mmap_fixed_destroyed_next, so the inversion needs real proof work and the donor apartness premise (sim_munmap rests on it) *)


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
  pose proof (mmap_len_pos_pg l ltac:(lia)) as Hnp. fold n in Hnp.
  assert (Ua : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit; unfold PGSZ in *; nia).
  assert (Un : bv_unsigned (Z_to_bv 64 PGSZ) = PGSZ) by (apply unsigned_lit; unfold PGSZ; lia).
  unfold PGSZ in A3. splits; auto; try (unfold PGSZ in *; nia).
  - destruct (Ana (1 + k) ltac:(lia) ltac:(lia)) as (e & He & Hel & Heh). unfold map_contains. apply existsb_exists. exists e. split; [exact He|].
    rewrite Ua, Un. unfold elo, ehi in Hel, Heh. subst a. rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity.
  - unfold map_contains. apply existsb_exists. exists (went b n). split; [exact A5|]. rewrite Ua, Un. unfold went, wz. cbn [fst snd].
    rewrite !unsigned_lit by (unfold PGSZ in *; lia). rewrite (proj2 (Z.leb_le _ _)) by (unfold PGSZ in *; nia). rewrite (proj2 (Z.leb_le _ _)) by (unfold PGSZ in *; nia). reflexivity.
Qed.

Lemma meta_target_unique : forall L pbrk mo b l k b' l' k', KL L pbrk mo ->
  In (b, l, k) (ld_metas L) -> (2 + k) * PGSZ <= round_up_pg l -> In (b', l', k') (ld_metas L) ->
  b' + (1 + k') * PGSZ = b + (1 + k) * PGSZ -> (b', l', k') = (b, l, k).
Proof.
  intros L pbrk mo b l k b' l' k' HK Hin Hk Hin' E. pose proof alloc_ceiling_lt as Hcl. pose proof (KL_atop_range _ _ _ HK) as HKat.
  pose proof (kl_metas _ _ _ HK b l k Hin) as (A1 & A2 & A3 & A4 & Ak & Ak1 & A5 & _).
  pose proof (kl_metas _ _ _ HK b' l' k' Hin') as (B1 & B2 & B3 & B4 & Bk & Bk1 & B5 & _).
  rewrite round_up_pg_eq in Hk. fold (mmap_len l) in Hk.
  pose proof (mmap_len_ge l ltac:(lia)). pose proof (mmap_len_ge l' ltac:(lia)).
  destruct (Z.eq_dec b' b) as [->|Hne].
  - pose proof (kl_distinct _ _ _ HK) as Hd. apply List.NoDup_app_remove_l in Hd.
    exact (nodup_map_inj _ _ _ _ Hd Hin' Hin eq_refl).
  - exfalso. destruct (pwdisj_In _ _ _ (proj2 (kl_wf _ _ _ HK)) B5 A5) as [Ee|D].
    + apply Hne. apply (f_equal elo) in Ee. rewrite !elo_went in Ee by lia. exact Ee.
    + unfold edisj in D. rewrite !elo_went, !ehi_went in D by lia. unfold PGSZ in *. nia.
Qed.

(* sim_mprotect left out: unused; at nstep_mprotect_ok_intro takes the vDSO region-free premise (Spec/EKPlace Section Mprotect, Hvd), which this simulation does not carry; supplying it is new proof work *)


Definition embed_post {R1 R2} (J : jled) (tG : stree ev Z R1) (tC : stree ev Z R2) (Post : jled -> R1 -> R2 -> Prop)
  (sG0 sC0 : PState) : R1 -> R2 -> rel PState PState :=
  fun rG rC sG moG sC moC =>
    exists J', jcpath J tG tC J' rG rC /\ Post J' rG rC /\ KR J' sG moG sC moC
    /\ ps_m sG = ps_m sG0 /\ ps_fa sG = ps_fa sG0 /\ ps_so sG = ps_so sG0
    /\ ps_m sC = ps_m sC0 /\ ps_fa sC = ps_fa sC0 /\ ps_so sC = ps_so sC0.

Lemma jevent_post_atops : forall J eG eC zG zC,
  j_atopG (jevent_post J eG eC zG zC) = j_atopG J /\ j_atopC (jevent_post J eG eC zG zC) = j_atopC J.
Proof.
  intros J eG eC zG zC. unfold jevent_post.
  repeat (first [split; reflexivity | match goal with |- context [match ?x with _ => _ end] => destruct x end]).
Qed.

