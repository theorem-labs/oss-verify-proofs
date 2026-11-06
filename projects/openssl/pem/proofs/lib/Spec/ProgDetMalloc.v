(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import PropExec MState Mem ITree Nodes Decode Ceiling.
From OSSVerify.Proofs.openssl.pem.lib.Spec Require Import Prelim Monad STree Malloc MallocCtrl Prog ProgDetIface ProgDetLogic ProgDetNodes.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint oktree {R} (t : stree ev Z R) (P : R -> Prop) : Prop :=
  match t with
  | SRet r => P r
  | SVis e k =>
      match e with
      | EUndef _ | EPeek _ _ _ => True
      | EMmap _ _ _ flags =>
          if Z.land flags MAP_FIXED =? 0 then forall z, is_err z = false -> oktree (k z) P
          else forall z, oktree (k z) P
      | EMprotect _ _ _ => oktree (k 0) P
      | _ => forall z, oktree (k z) P
      end
  end.

Lemma oktree_mono : forall {R} (t : stree ev Z R) (P P' : R -> Prop),
  oktree t P -> (forall r, P r -> P' r) -> oktree t P'.
Proof.
  intros R t. induction t as [r|e k IH]; intros P P' H HP; cbn in *; [auto|].
  destruct e as [a|a len prot flags|a len|a len prot|p c h|w]; eauto.
  destruct (Z.land flags MAP_FIXED =? 0); intros; eauto.
Qed.

Lemma oktree_sbind : forall {R S} (t : stree ev Z R) (f : R -> stree ev Z S) P,
  oktree t (fun r => oktree (f r) P) -> oktree (sbind t f) P.
Proof.
  intros R S t. induction t as [r|e k IH]; intros f P H; cbn in *; [exact H|].
  destruct e as [a|a len prot flags|a len|a len prot|p c h|w]; eauto.
  destruct (Z.land flags MAP_FIXED =? 0); intros; eauto.
Qed.

Lemma oktree_true : forall {R} (t : stree ev Z R), oktree t (fun _ => True).
Proof.
  intros R t. induction t as [r|e k IH]; cbn; [exact I|].
  destruct e as [a|a len prot flags|a len|a len prot|p c h|w]; auto. destruct (Z.land flags MAP_FIXED =? 0); auto.
Qed.

Lemma guard_ok : forall {R} tag c (k bail : Malloc.M R) P, (c = true -> oktree k P) -> oktree (guard tag c k bail) P.
Proof. intros R tag c k bail P H. unfold guard. destruct c; [apply H; reflexivity| exact I]. Qed.

Lemma bad_answer_ok : forall {R} (bail : Malloc.M R) P, oktree (bad_answer bail) P.
Proof. intros. exact I. Qed.

Lemma undef_ok : forall {R} why (k : Z -> Malloc.M R) P, oktree (SVis (EUndef why) k) P.
Proof. intros. exact I. Qed.

Ltac okstep :=
  first [ apply undef_ok | apply bad_answer_ok
        | apply guard_ok; intros ?
        | progress cbv beta iota zeta ].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Walk.
Context {R : Type}.
Variable P : R -> Prop.

Lemma queue_ok : forall h m st (k : mstate -> Malloc.M R) bail,
  (forall st', oktree (k st') P) -> oktree (queue h m st k bail) P.
Proof.
  intros h m st k bail Hk. unfold queue. apply guard_ok; intros _. apply guard_ok; intros _.
  destruct (get_head st h); apply Hk.
Qed.

Lemma activate_group_ok : forall m st (k : mstate -> Z -> Malloc.M R) bail,
  (forall st' mask, oktree (k st' mask) P) -> oktree (activate_group m st k bail) P.
Proof. intros m st k bail Hk. unfold activate_group. apply guard_ok; intros _. apply Hk. Qed.

Lemma am_take_ok : forall st (k : mstate -> optr -> Malloc.M R) bail,
  (forall st' m, oktree (k st' (Some m)) P) -> oktree (am_take st k bail) P.
Proof. intros st k bail Hk. unfold am_take. destruct (c_avail_meta (ctx st)); [apply Hk| exact I]. Qed.

Lemma am_carve_ok : forall st p (k : mstate -> optr -> Malloc.M R) bail,
  (forall st' m, oktree (k st' (Some m)) P) -> oktree (am_carve st p k bail) P.
Proof. intros st p k bail Hk. unfold am_carve. apply am_take_ok. exact Hk. Qed.

Lemma am_finish_ok : forall st nu (k : mstate -> optr -> Malloc.M R) bail,
  (forall st' m, oktree (k st' (Some m)) P) -> oktree (am_finish st nu k bail) P.
Proof.
  intros st nu k bail Hk. unfold am_finish. destruct (c_avail_meta_areas (ctx st)) as [p|]; [|exact I].
  destruct (if negb (snd p mod PGSZ =? 0) then false else nu).
  - cbn [oktree]. change (mprotect_answer_ok 0) with true. cbn [negb].
    change ((0 =? 0) || (0 =? TWO64 - ENOSYS)) with true. apply am_carve_ok. exact Hk.
  - apply am_carve_ok. exact Hk.
Qed.

Lemma am_after_brk_ok : forall st nu (k : mstate -> optr -> Malloc.M R) bail,
  (forall st' m, oktree (k st' (Some m)) P) -> oktree (am_after_brk st nu k bail) P.
Proof.
  intros st nu k bail Hk. unfold am_after_brk.
  destruct (c_avail_meta_area_count (ctx st) =? 0).
  - cbn [oktree]. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true. intros z Hz.
    destruct (negb (mmap_answer_ok _ _ z)); [exact I|]. rewrite Hz.
    destruct (new_region RKMeta z _ st). apply am_finish_ok. exact Hk.
  - apply am_finish_ok. exact Hk.
Qed.

Lemma alloc_meta_ok : forall st (k : mstate -> optr -> Malloc.M R) bail,
  (forall st' m, oktree (k st' (Some m)) P) -> oktree (alloc_meta st k bail) P.
Proof.
  intros st k bail Hk. unfold alloc_meta. cbv zeta.
  set (st1 := if c_init_done (ctx st) =? 0 then _ else st).
  destruct (c_free_meta_head (ctx st1)); [apply Hk|].
  destruct (negb (c_avail_meta_count (ctx st1) =? 0)); [apply am_take_ok; exact Hk|].
  destruct ((c_avail_meta_area_count (ctx st1) =? 0) && _); [|apply am_after_brk_ok; exact Hk].
  destruct (c_brk (ctx st1)) as [| |rid off].
  - cbn [oktree]. intros cur. destruct (negb (brk0_answer_ok cur)); [exact I|].
    cbn [oktree]. intros r. destruct (negb (brk_answer_ok _ _ r)); [exact I|].
    destruct (negb (r =? _)); [apply am_after_brk_ok; exact Hk|].
    destruct (negb (brk_pages_ok _ _ _)); [exact I|].
    cbn [oktree]. change (Z.land (MAP_PRIVATE + MAP_ANON + MAP_FIXED) MAP_FIXED =? 0) with false. intros rg.
    destruct (negb (mmap_fixed_answer_ok _ rg)); [exact I|].
    destruct (new_region RKBrk _ _ st1). apply am_after_brk_ok. exact Hk.
  - apply am_after_brk_ok. exact Hk.
  - cbn [oktree]. intros r. destruct (negb (brk_answer_ok _ _ r)); [exact I|].
    destruct (negb (r =? _)); [apply am_after_brk_ok; exact Hk|].
    destruct (negb (brk_pages_ok _ _ _)); [exact I|]. apply am_after_brk_ok. exact Hk.
Qed.

Ltac okcase :=
  match goal with
  | |- oktree (match ?x with _ => _ end) _ => destruct x
  | |- oktree (if ?x then _ else _) _ => destruct x
  end.

Lemma try_avail_ok : forall sc st (k : mstate -> Z -> Malloc.M R) bail,
  (forall st' first, oktree (k st' first) P) -> oktree (try_avail sc st k bail) P.
Proof.
  intros sc st k bail Hk. unfold try_avail. destruct (active st sc) as [m|]; [|apply Hk]. cbv zeta.
  destruct (negb _); [unfold ta_fin; apply Hk|].
  repeat okcase; try first [ apply Hk | exact I ];
  apply activate_group_ok; intros st4 mask; apply guard_ok; intros _; unfold ta_fin; apply Hk.
Qed.

Section AllocGroup.
Variable lay : layout_hook.
Variable rec : mstate -> Z -> Z -> (mstate -> Z -> Malloc.M R) -> Malloc.M R -> Malloc.M R.
Hypothesis Hrec : forall st sc req k bail,
  (forall st' idx, 0 <= idx -> oktree (k st' idx) P) -> oktree (rec st sc req k bail) P.

Lemma alloc_group_ok : forall st sc req (k : mstate -> optr -> Malloc.M R) bail,
  (forall st' m, oktree (k st' (Some m)) P) -> oktree (alloc_group R lay rec st sc req k bail) P.
Proof.
  intros st sc req k bail Hk. unfold alloc_group. apply alloc_meta_ok. intros st' m. cbv zeta.
  destruct (PGSZ / 2 <? _).
  - match goal with |- oktree (match ?x with _ => _ end) _ => destruct x as [cnt needed] end.
    cbn [oktree]. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true. intros z Hz.
    destruct (negb (mmap_answer_ok _ _ z)); [exact I|]. rewrite Hz.
    match goal with |- oktree (match ?x with _ => _ end) _ => destruct x end.
    unfold ag_tail. apply Hk.
  - apply Hrec. intros st1 idx Hidx. destruct (Z.ltb_spec idx 0); [lia|].
    destruct (active st1 _); [unfold ag_tail; apply Hk| exact I].
Qed.
End AllocGroup.

Lemma alloc_slot_ok : forall lay fuel st sc req (k : mstate -> Z -> Malloc.M R) bail,
  (forall st' idx, 0 <= idx -> oktree (k st' idx) P) -> oktree (alloc_slot lay fuel st sc req k bail) P.
Proof.
  intros lay fuel. induction fuel as [|f IH]; intros st sc req k bail Hk; cbn [alloc_slot]; [exact I|].
  apply try_avail_ok. intros st1 first. destruct (negb (first =? 0)).
  - apply Hk. unfold ctz32. apply Z.log2_nonneg.
  - apply alloc_group_ok; [exact IH|]. intros st2 g. cbv zeta. apply queue_ok. intros st4. apply Hk. lia.
Qed.

Lemma malloc_small_ctrl_ok : forall lay st n (k : mstate -> option (aptr * Z) -> Malloc.M R) bail,
  (forall st' gi, oktree (k st' (Some gi)) P) -> oktree (malloc_small_ctrl lay st n k bail) P.
Proof.
  intros lay st n k bail Hk. unfold malloc_small_ctrl. cbv zeta.
  assert (Hs : forall sc, oktree (alloc_slot lay FUEL st sc n (fun st1 idx =>
              if idx <? 0 then k st1 None else match active st1 sc with Some gp => k st1 (Some (gp, idx))
                                                | None => SVis (EUndef UBadPtr) (fun _ => bail) end) bail) P).
  { intros sc. apply alloc_slot_ok. intros st1 idx Hidx. destruct (Z.ltb_spec idx 0); [lia|].
    destruct (active st1 sc); [apply Hk| exact I]. }
  repeat okcase; first [ apply Hk | apply Hs ].
Qed.

End Walk.

Lemma malloc_core_ok : forall lay st n, size_overflows n = false ->
  oktree (malloc_core lay st n) (fun r => snd r <> None).
Proof.
  intros lay st n Hn. unfold malloc_core. cbv zeta. rewrite Hn. destruct (MMAP_THRESHOLD <=? n).
  - cbn [oktree]. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true. intros z Hz.
    destruct (negb (mmap_answer_ok _ _ z)); [exact I|]. rewrite Hz.
    match goal with |- oktree (match ?x with _ => _ end) _ => destruct x end.
    apply alloc_meta_ok. intros st' g. cbn [oktree snd]. discriminate.
  - apply malloc_small_ctrl_ok. intros st' gi. cbn [oktree snd]. discriminate.
Qed.

Lemma cmalloc_ok : forall cs n, size_overflows n = false -> oktree (cmalloc cs n) (fun r => snd r <> None).
Proof.
  intros cs n Hn. unfold cmalloc. apply oktree_sbind. eapply oktree_mono; [apply malloc_core_ok; exact Hn|].
  intros [st1 [[g idx]|]] H; cbn in *; [discriminate| contradiction].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition fstable (K : assnE PState) : Prop :=
  forall s mo tr s' mo', K s mo tr -> ps_so s' = ps_so s -> m_fds mo' = m_fds mo -> m_fs mo' = m_fs mo -> K s' mo' tr.

Lemma msysE_mm {St A} sel X n (dec : resp -> option A) (P : assnE St) (Q : A -> assnE St) :
  is_mm n ->
  (forall s mo tr rsp mo' a, P s mo tr -> m_fds mo' = m_fds mo -> m_fs mo' = m_fs mo -> ans_ok n rsp ->
     dec rsp = Some a -> Q a s mo' tr) ->
  mspecE sel X P (msys n dec) Q.
Proof.
  intros Hn Hk. apply msysE_node; [destruct n; first [exact I| contradiction]| intros; apply nprog_mm; exact Hn|].
  intros s mo tr rsp mo' evs a HP Hst Hd. destruct (stepR_mm sel n mo rsp mo' evs Hn Hst) as (-> & Hfd & Hfs & Hok).
  rewrite app_nil_r. eapply Hk; eauto.
Qed.

Lemma is_err_errno_none : forall w, errno_of w = None -> is_err (bv_unsigned w) = false.
Proof.
  intros w H. unfold errno_of in H. unfold is_err, TWO64.
  destruct (Z.leb_spec0 (2^64 - 4095) (bv_unsigned w)); [discriminate|]. apply Z.ltb_ge. lia.
Qed.

Lemma dec_mmap_MmOk : forall {CE : Ceiling} len avoid rsp x, dec_mmap len avoid rsp = Some (MmOk x) -> x = bv_unsigned (eff_ret rsp).
Proof.
  intros CE len avoid [r ws zs us cs ci] x H. unfold dec_mmap in H.
  destruct ws; [|discriminate]. destruct zs as [|[a n] [|? ?]]; try discriminate.
  - destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
    destruct (errno_of r); discriminate.
  - destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
    destruct (_ && _ && _); [|discriminate]. injection H as <-. reflexivity.
Qed.

Lemma dec_mmap_none_MmOk : forall {CE : Ceiling} len avoid rsp x, dec_mmap_none len avoid rsp = Some (MmOk x) -> x = bv_unsigned (eff_ret rsp).
Proof.
  intros CE len avoid [r ws zs us cs ci] x H. unfold dec_mmap_none in H.
  destruct ws; [|discriminate]. destruct zs; [|discriminate].
  destruct us as [|[a n] [|? ?]]; try discriminate; destruct cs; try discriminate; destruct ci; try discriminate.
  - destruct (errno_of r); discriminate.
  - destruct (_ && _ && _); [|discriminate]. injection H as <-. reflexivity.
Qed.

Lemma dec_mmap_MmErr : forall {CE : Ceiling} len avoid rsp e, dec_mmap len avoid rsp = Some (MmErr e) -> errno_of (eff_ret rsp) <> None.
Proof.
  intros CE len avoid rsp e H. pose proof (dec_mmap_Some _ _ _ _ H) as [-> He]. cbn [eff_ret efferr eff0].
  rewrite errno_of_errno_ret by exact He. discriminate.
Qed.

Lemma dec_mmap_none_MmErr : forall {CE : Ceiling} len avoid rsp e, dec_mmap_none len avoid rsp = Some (MmErr e) -> errno_of (eff_ret rsp) <> None.
Proof.
  intros CE len avoid rsp e H. pose proof (dec_mmap_none_Some _ _ _ _ H) as [-> He]. cbn [eff_ret efferr eff0].
  rewrite errno_of_errno_ret by exact He. discriminate.
Qed.

Lemma dec_mprotect_rw_RgErr : forall addr len rsp e, dec_mprotect_rw addr len rsp = Some (RgErr e) -> errno_of (eff_ret rsp) <> None.
Proof.
  intros addr len rsp e H. unfold dec_mprotect_rw in H.
  destruct (dec_mprotect addr len rsp) as [[e'|[|]]|] eqn:E; try discriminate.
  destruct (e' =? ENOSYS); [discriminate|]. injection H as <-.
  pose proof (dec_mprotect_Some _ _ _ _ E) as [-> He]. cbn [eff_ret efferr eff0].
  rewrite errno_of_errno_ret by exact He. discriminate.
Qed.

(* [comment removed for export] *)
Definition okans (e : ev) (z : Z) : Prop :=
  match e with
  | EMmap _ _ _ flags => (Z.land flags MAP_FIXED =? 0) = true -> is_err z = false
  | EMprotect _ _ _ => z = 0
  | _ => True
  end.

Section Embed.
Context {CE__ : Ceiling}.
Variable sel : option bool.
Variable X : list event -> Prop.

Lemma ev_step_E : forall e (K : assnE PState), fstable K ->
  mspecE sel X K (ev_step e) (fun z s mo tr => K s mo tr /\ okans e z).
Proof.
  intros e K HK.
  assert (Hupd : forall v, mspecE sel X K (mupd (set_brk_ps v)) (fun _ => K)).
  { intros v. apply mspecE_upd. intros s mo tr H. eapply HK; [exact H| reflexivity| reflexivity| reflexivity]. }
  assert (Hmm : forall n A (dec : resp -> option A), is_mm n -> mspecE sel X K (msys n dec) (fun _ => K)).
  { intros n A dec Hn. apply msysE_mm; [exact Hn|]. intros s mo tr rsp mo' a HKs Hfd Hfs _ _.
    eapply HK; [exact HKs| reflexivity| exact Hfd| exact Hfs]. }
  destruct e as [req|addr len prot flags|addr len|addr len prot|p c h|w]; cbn [ev_step].
  - destruct (req =? 0).
    + eapply mspecE_seq; [apply Hmm; exact I|]. intros r. eapply mspecE_seq; [apply Hupd|]. intros _.
      apply mspecE_ret. intros s mo tr H. split; [exact H| exact I].
    + eapply mspecE_bind with (Q1 := fun s0 s mo tr => K s mo tr /\ s = s0); [apply mspecE_get; intros s mo tr H; exact (conj H (eq_refl s))|]. intros s0.
      eapply mspecE_bind.
      { apply (msysE_mm sel X (NBrk req) _ (fun s mo tr => K s mo tr /\ s = s0) (fun _ s mo tr => K s mo tr /\ s = s0)); [exact I|].
        intros s mo tr rsp mo' a [HKs ->] Hfd Hfs _ _. split; [eapply HK; [exact HKs| reflexivity| exact Hfd| exact Hfs]| reflexivity]. }
      intros [|].
      * eapply mspecE_seq; [eapply mspecE_pre; [apply Hupd| intros s mo tr [H _]; exact H]|]. intros _.
        apply mspecE_ret. intros s mo tr H. split; [exact H| exact I].
      * apply mspecE_ret. intros s mo tr [H _]. split; [exact H| exact I].
  - destruct (negb (Z.land flags MAP_FIXED_Z =? 0)) eqn:Ef.
    + eapply mspecE_seq; [apply Hmm; exact I|]. intros a.
      apply mspecE_ret. intros s mo tr H. split; [exact H|]. cbn [okans].
      change MAP_FIXED with MAP_FIXED_Z. rewrite <- (negb_involutive (Z.land flags MAP_FIXED_Z =? 0)), Ef. discriminate.
    + apply negb_false_iff in Ef. destruct (prot =? 0).
      * eapply mspecE_bind.
        { apply (msysE_mm sel X (NMmap addr len prot flags) _ K (fun a s mo tr => K s mo tr /\ exists x, a = MmOk x /\ is_err x = false)); [exact I|].
          intros s mo tr rsp mo' a HKs Hfd Hfs Hok Hd. split; [eapply HK; [exact HKs| reflexivity| exact Hfd| exact Hfs]|].
          cbn [ans_ok] in Hok. apply Z.eqb_eq in Ef. specialize (Hok Ef).
          destruct a as [e|x]; [exfalso; exact (dec_mmap_none_MmErr _ _ _ _ Hd Hok)|].
          exists x. split; [reflexivity|]. rewrite (dec_mmap_none_MmOk _ _ _ _ Hd). apply is_err_errno_none. exact Hok. }
        intros a. apply mspecE_ret. intros s mo tr [H (x & -> & Hx)]. split; [exact H|]. intros _. exact Hx.
      * eapply mspecE_bind.
        { apply (msysE_mm sel X (NMmap addr len prot flags) _ K (fun a s mo tr => K s mo tr /\ exists x, a = MmOk x /\ is_err x = false)); [exact I|].
          intros s mo tr rsp mo' a HKs Hfd Hfs Hok Hd. split; [eapply HK; [exact HKs| reflexivity| exact Hfd| exact Hfs]|].
          cbn [ans_ok] in Hok. apply Z.eqb_eq in Ef. specialize (Hok Ef).
          destruct a as [e|x]; [exfalso; exact (dec_mmap_MmErr _ _ _ _ Hd Hok)|].
          exists x. split; [reflexivity|]. rewrite (dec_mmap_MmOk _ _ _ _ Hd). apply is_err_errno_none. exact Hok. }
        intros a. apply mspecE_ret. intros s mo tr [H (x & -> & Hx)]. split; [exact H|]. intros _. exact Hx.
  - eapply mspecE_seq; [apply Hmm; exact I|]. intros a.
    apply mspecE_ret. intros s mo tr H. split; [exact H| exact I].
  - eapply mspecE_bind.
    { apply (msysE_mm sel X (NMprotect addr len prot) _ K (fun a s mo tr => K s mo tr /\ exists b, a = RgDone b)); [exact I|].
      intros s mo tr rsp mo' a HKs Hfd Hfs Hok Hd. split; [eapply HK; [exact HKs| reflexivity| exact Hfd| exact Hfs]|].
      cbn [ans_ok] in Hok. destruct a as [e|b]; [exfalso; exact (dec_mprotect_rw_RgErr _ _ _ _ Hd Hok)| eauto]. }
    intros a. apply mspecE_ret. intros s mo tr [H (b & ->)]. split; [exact H| reflexivity].
  - apply mspecE_munr.
  - apply mspecE_munr.
Qed.

Lemma membed_E : forall {R} (t : stree ev Z R) (P : R -> Prop) (K : assnE PState),
  fstable K -> oktree t P -> mspecE sel X K (membed t) (fun r s mo tr => K s mo tr /\ P r).
Proof.
  intros R t. induction t as [r|e k IH]; intros P K HK Ht; cbn [membed].
  - apply mspecE_ret. intros s mo tr H. split; [exact H| exact Ht].
  - assert (Hpk : match e with EPeek _ _ _ | EUndef _ => True | _ => False end \/ forall z, okans e z -> oktree (k z) P).
    { cbn [oktree] in Ht. destruct e as [a|a len prot flags|a len|a len prot|p c h|w]; cbn [okans]; [right..|left; exact I|left; exact I].
      - intros z _. exact (Ht z).
      - destruct (Z.land flags MAP_FIXED =? 0) eqn:E; intros z Hz; [exact (Ht z (Hz eq_refl))| exact (Ht z)].
      - intros z _. exact (Ht z).
      - intros z ->. exact Ht. }
    destruct Hpk as [Hpk|Hpk].
    + destruct e; try contradiction; intros s mo tr _; exact I.
    + eapply mspecE_bind; [apply ev_step_E; exact HK|]. intros z. apply mspecE_pure. intros Hz.
      apply IH; [exact HK| exact (Hpk z Hz)].
Qed.

End Embed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Raw.
Context {CE__ : Ceiling}.
Variable sel : option bool.
Variable X : list event -> Prop.

Lemma raw_malloc_E : forall n (K : assnE PState), fstable K -> size_overflows n = false ->
  mspecE sel X K (raw_malloc n) (fun r s mo tr => K s mo tr /\ r <> None).
Proof.
  intros n K HK Hn. unfold raw_malloc.
  eapply mspecE_bind with (Q1 := fun s0 s mo tr => K s mo tr /\ s = s0);
    [apply mspecE_get; intros s mo tr H; exact (conj H (eq_refl s))|]. intros s0.
  eapply mspecE_bind.
  { eapply mspecE_pre; [apply membed_E; [exact HK| apply cmalloc_ok; exact Hn]| intros s mo tr [H _]; exact H]. }
  intros [st' p]. cbv beta iota. apply mspecE_pure. intros Hp. cbn [snd] in Hp.
  eapply mspecE_seq with (R := K).
  { apply mspecE_upd. intros s mo tr H. eapply HK; [exact H| reflexivity| reflexivity| reflexivity]. }
  intros _. apply mspecE_ret. intros s mo tr H. split; [exact H|]. destruct p; [discriminate| contradiction].
Qed.

Lemma raw_free_E : forall p (K : assnE PState), fstable K -> mspecE sel X K (raw_free p) (fun _ => K).
Proof.
  intros p K HK. unfold raw_free.
  eapply mspecE_bind with (Q1 := fun s0 s mo tr => K s mo tr /\ s = s0);
    [apply mspecE_get; intros s mo tr H; exact (conj H (eq_refl s))|]. intros s0.
  eapply mspecE_bind.
  { eapply mspecE_pre; [apply membed_E; [exact HK| apply oktree_true]| intros s mo tr [H _]; exact H]. }
  intros st'. apply mspecE_upd. intros s mo tr [H _]. eapply HK; [exact H| reflexivity| reflexivity| reflexivity].
Qed.

End Raw.
