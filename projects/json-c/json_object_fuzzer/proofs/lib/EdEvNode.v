From Stdlib Require Import ZArith List Lia Bool Classical_Prop.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Import EdAlloc EdBridge.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH QiVh.
Import ListNotations.

(* An outcome the configured step keeps: a spec outcome that is not a spurious refusal. *)
Definition ekept (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) : Prop :=
  syscall_spec i m o
  /\ forall eff m' evs, o = Ok eff m' evs -> ~ spurious_refusal_cfg (alloc_only_cfg false) i m eff.

Lemma ekept_Ok : forall i m eff m' evs,
  ekept i m (Ok eff m' evs)
  <-> syscall_spec i m (Ok eff m' evs) /\ ~ spurious_refusal_cfg (alloc_only_cfg false) i m eff.
Proof.
  intros i m eff m' evs. unfold ekept. split.
  - intros [Hs Hn]. split; [exact Hs | exact (Hn eff m' evs eq_refl)].
  - intros [Hs Hn]. split; [exact Hs |]. intros eff2 m2 evs2 E. injection E as <- <- <-. exact Hn.
Qed.

Lemma ekept_bool : forall (b : bool) (P : Prop), (b = false <-> P) -> (b = true <-> ~ P).
Proof.
  intros b P H. destruct b; split; intros X.
  - intros HP. apply H in HP. discriminate HP.
  - reflexivity.
  - discriminate X.
  - exfalso. apply X. apply H. reflexivity.
Qed.

Lemma ekept_arm : forall i m (R : Prop) (Rf G : outcome SyscallEffect -> Prop),
  enomem_sysno (bv_unsigned (in_sysno i)) ->
  (forall o, syscall_spec i m o <-> Rf o \/ G o) ->
  (forall o, Rf o -> exists eff m' evs, o = Ok eff m' evs /\ eff_ret eff = errno_ret ENOMEM) ->
  (forall o, G o -> exists eff m' evs, o = Ok eff m' evs /\ eff_ret eff <> errno_ret ENOMEM) ->
  (R <-> ~ exists o, G o) ->
  forall o, ekept i m o <-> (R /\ Rf o) \/ G o.
Proof.
  intros i m R Rf G Hno Hiff HRf HG HR o. unfold ekept. split.
  - intros [Hs Hns]. apply Hiff in Hs. destruct Hs as [Hr | Hg]; [left | right; exact Hg].
    split; [| exact Hr]. apply HR. intros (o2 & Hg2).
    destruct (HRf o Hr) as (eff & m' & evs & -> & Hret).
    destruct (HG o2 Hg2) as (eff2 & m2 & evs2 & -> & Hret2).
    apply (Hns eff m' evs eq_refl).
    apply (ed_spurious_intro i m eff eff2 m2 evs2 Hno Hret); [apply Hiff; right; exact Hg2 | exact Hret2].
  - intros [[HRt Hr] | Hg].
    + split; [apply Hiff; left; exact Hr |]. intros eff m' evs E.
      apply ed_not_spurious_all; [exact Hno |]. intros eff2 m2 evs2 Hs2.
      apply Hiff in Hs2. destruct Hs2 as [Hr2 | Hg2].
      * destruct (HRf _ Hr2) as (e3 & m3 & evs3 & E3 & Hret). injection E3 as -> -> ->. exact Hret.
      * exfalso. apply (proj1 HR HRt). exists (Ok eff2 m2 evs2). exact Hg2.
    + split; [apply Hiff; right; exact Hg |]. intros eff m' evs E. subst o.
      apply ed_not_spurious_ret; [exact Hno |].
      destruct (HG _ Hg) as (e3 & m3 & evs3 & E3 & Hret). injection E3 as -> -> ->. exact Hret.
Qed.

Section Node.
Variable segs : list Segment.

Lemma node_ekept : forall ms model x8 (I : Type) (effs : I -> SyscallEffect) (ms' : I -> Model),
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  (forall eff m' evs, syscall_spec (sys_input segs ms x8) model (Ok eff m' evs) -> m_halted m' = None) ->
  (forall o, ekept (sys_input segs ms x8) model o <-> exists i, o = Ok (effs i) (ms' i) []) ->
  (forall i, m_halted (ms' i) = None) ->
  (forall i, m_vm_lazy (ms' i) = []) ->
  QRjH.node_ok segs (mkCfg ms model) I (fun _ => [])
    (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)).
Proof.
  intros ms model x8 I effs ms' Hh Hsvc Hnh Hk Hh' Hl. split.
  - intros i. destruct (proj2 (Hk (Ok (effs i) (ms' i) [])) (ex_intro _ i eq_refl)) as [Hs Hns].
    apply (sstep_cfg_syscall segs (alloc_only_cfg false) ms model x8 (effs i) (ms' i) (ms' i) []
             Hh Hsvc Hs (Hns _ _ _ eq_refl) (Hh' i)).
    apply materialize_model_accesses_no_lazy. exact (Hl i).
  - intros e st Hss. inversion Hss; subst; try congruence;
      match goal with H : ms_svc_pending ms = Some ?y |- _ => rewrite Hsvc in H; injection H as <- end.
    + match goal with
      | Hs : syscall_spec _ _ (Ok ?eff ?m1 ?ev), Hn : ~ spurious_refusal_cfg _ _ _ ?eff,
        Hm : materialize_model_accesses ?m1 _ = Some ?m2 |- _ =>
          destruct (proj1 (Hk (Ok eff m1 ev)) (proj2 (ekept_Ok _ _ _ _ _) (conj Hs Hn))) as (i & Ei);
          injection Ei as -> -> ->;
          rewrite (materialize_model_accesses_no_lazy _ _ (Hl i)) in Hm; injection Hm as <-;
          exists i; split; reflexivity
      end.
    + match goal with
      | Hs : syscall_spec _ _ (Ok ?eff ?m1 ?ev), Hn : ~ spurious_refusal_cfg _ _ _ ?eff,
        Hm : materialize_model_accesses ?m1 _ = None |- _ =>
          destruct (proj1 (Hk (Ok eff m1 ev)) (proj2 (ekept_Ok _ _ _ _ _) (conj Hs Hn))) as (i & Ei);
          injection Ei as -> -> ->;
          rewrite (materialize_model_accesses_no_lazy _ _ (Hl i)) in Hm; discriminate Hm
      end.
    + match goal with
      | Hs : syscall_spec _ _ (Ok _ ?m1 _), Hx : m_halted ?m1 = Some _ |- _ =>
          rewrite (Hnh _ _ _ Hs) in Hx; discriminate Hx
      end.
    + match goal with
      | Hs : syscall_spec _ _ (Ok _ ?m1 _), Hx : m_killed ?m1 = Some _ |- _ =>
          rewrite (m_killed_of_m_halted_none _ (Hnh _ _ _ Hs)) in Hx; discriminate Hx
      end.
    + match goal with
      | Hs : syscall_spec _ _ Unmodeled |- _ =>
          assert (HkU : ekept (sys_input segs ms x8) model Unmodeled)
            by (split; [exact Hs | intros ? ? ? E; discriminate E]);
          destruct (proj1 (Hk _) HkU) as (i & E); discriminate E
      end.
Qed.

Lemma ncl_ekept : forall (J : config -> Prop) ms model x8 (I : Type)
  (effs : I -> SyscallEffect) (ms' : I -> Model) (i0 : I),
  QRjH.NClosed segs J ->
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  (forall eff m' evs, syscall_spec (sys_input segs ms x8) model (Ok eff m' evs) -> m_halted m' = None) ->
  (forall o, ekept (sys_input segs ms x8) model o <-> exists i, o = Ok (effs i) (ms' i) []) ->
  (forall i, m_halted (ms' i) = None) ->
  (forall i, m_vm_lazy (ms' i) = []) ->
  (forall i, J (mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i))) ->
  J (mkCfg ms model).
Proof.
  intros J ms model x8 I effs ms' i0 HJ Hh Hsvc Hnh Hk Hh' Hl Hc.
  apply (HJ _ I (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)) i0); [| exact Hc].
  exact (node_ekept ms model x8 I effs ms' Hh Hsvc Hnh Hk Hh' Hl).
Qed.

Lemma ncl_spec_family : forall (J : config -> Prop) ms model x8 (I : Type)
  (effs : I -> SyscallEffect) (ms' : I -> Model) (i0 : I),
  QRjH.NClosed segs J ->
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  (forall o, syscall_spec (sys_input segs ms x8) model o <-> exists i, o = Ok (effs i) (ms' i) []) ->
  (forall i, m_halted (ms' i) = None) ->
  (forall i, m_vm_lazy (ms' i) = []) ->
  (forall i, J (mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i))) ->
  J (mkCfg ms model).
Proof.
  intros J ms model x8 I effs ms' i0 HJ Hh Hsvc Hiff Hh' Hl Hc.
  assert (Hi0 : exists j, ~ spurious_refusal_cfg (alloc_only_cfg false) (sys_input segs ms x8) model (effs j)).
  { destruct (classic (spurious_refusal_cfg (alloc_only_cfg false) (sys_input segs ms x8) model (effs i0)))
      as [Hsp | Hns]; [| exists i0; exact Hns].
    destruct Hsp as (_ & _ & eff2 & m2 & evs2 & Hs2 & Hnr).
    destruct (proj1 (Hiff _) Hs2) as (j & E). injection E as -> -> ->.
    exists j. apply spurious_refusal_not_refusal. exact Hnr. }
  destruct Hi0 as (j0 & Hj0).
  apply (ncl_ekept J ms model x8
           {j : I | ~ spurious_refusal_cfg (alloc_only_cfg false) (sys_input segs ms x8) model (effs j)}
           (fun j => effs (proj1_sig j)) (fun j => ms' (proj1_sig j)) (exist _ j0 Hj0) HJ Hh Hsvc).
  - intros eff m' evs Hs. destruct (proj1 (Hiff _) Hs) as (j & E). injection E as -> -> ->. exact (Hh' j).
  - intros o. split.
    + intros [Hs Hns]. destruct (proj1 (Hiff _) Hs) as (j & E). subst o.
      exists (exist _ j (Hns _ _ _ eq_refl)). reflexivity.
    + intros ([j Hj] & ->). split; [apply Hiff; exists j; reflexivity |].
      intros eff m' evs E. injection E as <- <- <-. exact Hj.
  - intros [j Hj]. exact (Hh' j).
  - intros [j Hj]. exact (Hl j).
  - intros [j Hj]. exact (Hc j).
Qed.

End Node.

Module Mb.
Import QiVh.

Section B.
Variable segs : list Segment.

Definition ebrk_eff (ms : machine_state) (model : Model) (r : word) : SyscallEffect :=
  mkEffectU r [] (Mmap.brk_zeros (ms_gpr ms 0) r (vm_brk (m_vmmaps model)))
    (Mmap.brk_unmaps r (vm_brk (m_vmmaps model))) [] [].

Definition ebrk_idx (ms : machine_state) (model : Model) (x8 : word) : Type :=
  {r : word | brk_resolution_ok model (ms_gpr ms 0) r
     /\ ~ spurious_refusal_cfg (alloc_only_cfg false) (sys_input segs ms x8) model (ebrk_eff ms model r)}.

Lemma ebrk_keep_ok : forall m req, brk_resolution_ok m req (vm_brk (m_vmmaps m)).
Proof.
  intros m req. unfold brk_resolution_ok, Mmap.brk_r_ok. cbv zeta.
  rewrite !ed_bv_eqb_refl, !orb_true_r, ed_brk_grow_ok_keep.
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; reflexivity.
Qed.

Lemma ebrk_idx_inh : forall ms model x8, bv_unsigned x8 = 214%Z ->
  exists r, brk_resolution_ok model (ms_gpr ms 0) r
    /\ ~ spurious_refusal_cfg (alloc_only_cfg false) (sys_input segs ms x8) model (ebrk_eff ms model r).
Proof.
  intros ms model x8 Hno.
  destruct (classic (spurious_refusal_cfg (alloc_only_cfg false) (sys_input segs ms x8) model
                       (ebrk_eff ms model (vm_brk (m_vmmaps model))))) as [Hsp | Hns].
  - destruct Hsp as (_ & _ & eff2 & m2 & evs2 & Hs2 & Hnr).
    apply (brk_ok_iff segs ms x8 model eff2 m2 evs2 Hno) in Hs2 as (Heff & _ & Hok & _).
    exists (eff_ret eff2). split; [exact Hok |]. apply spurious_refusal_not_refusal. exact Hnr.
  - exists (vm_brk (m_vmmaps model)). split; [apply ebrk_keep_ok | exact Hns].
Qed.

Lemma node_brk_ekept : forall ms model x8,
  m_halted model = None -> m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 214%Z ->
  QRjH.node_ok segs (mkCfg ms model) (ebrk_idx ms model x8) (fun _ => [])
    (fun i => mkCfg (advance_past_svc (apply_effect ms (ebrk_eff ms model (proj1_sig i))))
                (brk_model (ms_gpr ms 0) (proj1_sig i) model)).
Proof.
  intros ms model x8 Hh Hlazy Hsvc Hno.
  apply (node_ekept segs ms model x8 (ebrk_idx ms model x8) (fun i => ebrk_eff ms model (proj1_sig i))
           (fun i => brk_model (ms_gpr ms 0) (proj1_sig i) model) Hh Hsvc).
  - intros eff m' evs Hs. exact (proj1 (proj2 (brk_step_shape segs ms x8 model eff m' evs Hh Hlazy Hno Hs))).
  - intros [eff m' evs |]; split.
    + intros [Hs Hns]. pose proof (Hns eff m' evs eq_refl) as Hns'.
      apply (brk_ok_iff segs ms x8 model eff m' evs Hno) in Hs as (Heff & -> & Hok & ->).
      assert (Hns2 : ~ spurious_refusal_cfg (alloc_only_cfg false) (sys_input segs ms x8) model
                       (ebrk_eff ms model (eff_ret eff))) by (unfold ebrk_eff; rewrite <- Heff; exact Hns').
      exists (exist _ (eff_ret eff) (conj Hok Hns2)). cbn [proj1_sig]. unfold ebrk_eff. rewrite <- Heff. reflexivity.
    + intros ([r [Hr Hns]] & E). injection E as -> -> ->. cbn [proj1_sig]. unfold ebrk_eff. split.
      * apply brk_ok_intro; [exact Hno | exact Hr].
      * intros eff m' evs E. injection E as <- <- <-. exact Hns.
    + intros [Hs _]. exfalso. exact (brk_no_unmodeled segs ms x8 model Hno Hs).
    + intros (i & E). discriminate E.
  - intros [r [Hr Hns]]. cbn [proj1_sig].
    exact (proj1 (proj2 (brk_step_shape segs ms x8 model _ _ _ Hh Hlazy Hno (brk_ok_intro segs ms x8 model r Hno Hr)))).
  - intros [r [Hr Hns]]. cbn [proj1_sig].
    pose proof (brk_step_shape segs ms x8 model _ _ _ Hh Hlazy Hno (brk_ok_intro segs ms x8 model r Hno Hr)) as (_ & _ & _ & _ & E).
    rewrite E. exact Hlazy.
Qed.

Lemma node_brk_query : forall ms model x8,
  m_halted model = None -> m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 214%Z ->
  ms_gpr ms 0 = Z_to_bv 64 0 ->
  QRjH.node_ok segs (mkCfg ms model)
    {r : word | brk_resolution_ok model (ms_gpr ms 0) r}
    (fun _ => [])
    (fun i => mkCfg (advance_past_svc (apply_effect ms
      (mkEffectU (proj1_sig i) []
        (Mmap.brk_zeros (ms_gpr ms 0) (proj1_sig i) (vm_brk (m_vmmaps model)))
        (Mmap.brk_unmaps (proj1_sig i) (vm_brk (m_vmmaps model))) [] [])))
      (brk_model (ms_gpr ms 0) (proj1_sig i) model)).
Proof.
  intros ms model x8 Hh Hlazy Hsvc Hno H0.
  assert (Hns : forall eff, ~ spurious_refusal_cfg (alloc_only_cfg false) (sys_input segs ms x8) model eff).
  { intros eff. apply (ed_brk_query_not_spurious _ (ms_gpr ms 0)); [split; [exact Hno | reflexivity] |].
    rewrite H0. unfold w_is0. apply ed_bv_eqb_refl. }
  apply (node_ekept segs ms model x8 {r : word | brk_resolution_ok model (ms_gpr ms 0) r}
           (fun i => ebrk_eff ms model (proj1_sig i))
           (fun i => brk_model (ms_gpr ms 0) (proj1_sig i) model) Hh Hsvc).
  - intros eff m' evs Hs. exact (proj1 (proj2 (brk_step_shape segs ms x8 model eff m' evs Hh Hlazy Hno Hs))).
  - intros [eff m' evs |]; split.
    + intros [Hs _].
      apply (brk_ok_iff segs ms x8 model eff m' evs Hno) in Hs as (Heff & -> & Hok & ->).
      exists (exist _ (eff_ret eff) Hok). cbn [proj1_sig]. unfold ebrk_eff. rewrite <- Heff. reflexivity.
    + intros ([r Hr] & E). injection E as -> -> ->. cbn [proj1_sig]. unfold ebrk_eff. split.
      * apply brk_ok_intro; [exact Hno | exact Hr].
      * intros eff m' evs _. apply Hns.
    + intros [Hs _]. exfalso. exact (brk_no_unmodeled segs ms x8 model Hno Hs).
    + intros (i & E). discriminate E.
  - intros [r Hr]. cbn [proj1_sig].
    exact (proj1 (proj2 (brk_step_shape segs ms x8 model _ _ _ Hh Hlazy Hno (brk_ok_intro segs ms x8 model r Hno Hr)))).
  - intros [r Hr]. cbn [proj1_sig].
    pose proof (brk_step_shape segs ms x8 model _ _ _ Hh Hlazy Hno (brk_ok_intro segs ms x8 model r Hno Hr)) as (_ & _ & _ & _ & E).
    rewrite E. exact Hlazy.
Qed.

Lemma ncl_brk : forall (J : config -> Prop) ms model x8,
  QRjH.NClosed segs J -> m_halted model = None -> m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 214%Z ->
  (forall i : {r : word | brk_resolution_ok model (ms_gpr ms 0) r},
    J (mkCfg (advance_past_svc (apply_effect ms
      (mkEffectU (proj1_sig i) []
        (Mmap.brk_zeros (ms_gpr ms 0) (proj1_sig i) (vm_brk (m_vmmaps model)))
        (Mmap.brk_unmaps (proj1_sig i) (vm_brk (m_vmmaps model))) [] [])))
      (brk_model (ms_gpr ms 0) (proj1_sig i) model))) ->
  J (mkCfg ms model).
Proof.
  intros J ms model x8 HJ Hh Hlazy Hsvc Hno Hc.
  destruct (ebrk_idx_inh ms model x8 Hno) as (r0 & Hr0 & Hns0).
  apply (HJ _ _ _ (exist _ r0 (conj Hr0 Hns0) : ebrk_idx ms model x8) (node_brk_ekept ms model x8 Hh Hlazy Hsvc Hno)).
  intros [r [Hr Hns]]. exact (Hc (exist _ r Hr)).
Qed.

End B.
End Mb.
