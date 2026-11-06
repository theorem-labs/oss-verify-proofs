From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK11 YK0s YK0i YK15 YM06 YM02 YP09.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YO0i YO0f YO0x YO0d YO0p YM06_cf.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.R Require Import Cfg.
Import ListNotations.
Local Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Definition charged (q : kreq) : bool :=
  match q with
  | KMmapRW _ | KMprotect _ | KBrkGrow _ | KMremap _ _ _ => true
  | _ => false
  end.

Fixpoint roomcf {A : Type} (X : Z) (t : itree astate A) : Prop :=
  match t with
  | IRet _ => True
  | IFail _ => True
  | IAsk q s k => (charged q = true -> live_bytes s + req_len q <= X) /\ (forall z, canswer04 q z -> roomcf X (k z))
  end.

Section h.
Variable segs : list Segment.

Definition knode_cf (c1 : config) (q : kreq) (snap : astate) (Kont : Z -> config -> Prop) : Prop :=
  knode segs c1 q snap Kont /\
  match q with
  | KJunk _ => True
  | _ =>
      ((charged q = true -> live_bytes snap + req_len q <= vml c1) -> ~ budget_refused_at segs c1) /\
      (forall e c2, sstep_cfg segs ACFG c1 e (SNext c2) -> vml c2 = vml c1)
  end.

Fixpoint mreal_cf {R : Type} (c : config) (t : itree astate R) (Q : R -> config -> Prop) {struct t} : Prop :=
  match t with
  | IRet r => SR_cfv segs c (Q r)
  | IFail _ => True
  | IAsk q snap k => SR_cfv segs c (fun c1 => knode_cf c1 q snap (fun z c2 => mreal_cf c2 (k z) Q))
  end.

Lemma knode_mono_K : forall c1 q snap (K K' : Z -> config -> Prop),
  (forall z c2, K z c2 -> K' z c2) -> knode segs c1 q snap K -> knode segs c1 q snap K'.
Proof using.
  intros c1 q snap K K' HK Hk. destruct q;
  try (destruct Hk as (J & nx & bit & i0 & Hn & Hc & Hcl); exists J, nx, bit, i0;
       split; [exact Hn|]; split; [intros i; apply HK, Hc | exact Hcl]).
  destruct Hk as (z & Hz & Hc). exists z. split; [exact Hz | apply HK, Hc].
Qed.

Lemma knode_cf_mono : forall c1 q snap (K K' : Z -> config -> Prop),
  (forall z c2, K z c2 -> K' z c2) -> knode_cf c1 q snap K -> knode_cf c1 q snap K'.
Proof using.
  intros c1 q snap K K' HK [Hk X]. split; [exact (knode_mono_K c1 q snap K K' HK Hk) | exact X].
Qed.

Lemma mreal_cf_mreal {R} : forall (t : itree astate R) c Q, mreal_cf c t Q -> mreal segs c t Q.
Proof using.
  induction t as [r | q s k IH | f]; intros c Q H; cbn in *.
  - exact (SR_cfv_SR segs c (Q r) H).
  - eapply SR_mono; [exact (SR_cfv_SR segs _ _ H)|]. intros c1 [Hk _].
    eapply knode_mono_K; [|exact Hk]. intros z c2 Hm. apply IH, Hm.
  - exact I.
Qed.

Lemma mreal_cf_mono {R} : forall (t : itree astate R) c (Q Q' : R -> config -> Prop),
  (forall r c', Q r c' -> Q' r c') -> mreal_cf c t Q -> mreal_cf c t Q'.
Proof using.
  induction t as [r | q s k IH | f]; intros c Q Q' HQ H; cbn in *.
  - eapply SR_cfv_mono; [exact H | intros c' H'; apply HQ, H'].
  - eapply SR_cfv_mono; [exact H |]. intros c1 Hk.
    eapply knode_cf_mono; [|exact Hk]. intros z c2 Hm. eapply IH; [exact HQ | exact Hm].
  - exact I.
Qed.

Lemma mreal_cf_SR_pre {R} : forall (t : itree astate R) c Q (P : config -> Prop),
  SR_cfv segs c P -> (forall c', P c' -> mreal_cf c' t Q) -> mreal_cf c t Q.
Proof using.
  intros t c Q P HP H. destruct t as [r | q s k | f]; cbn in *.
  - eapply SR_cfv_bind; [exact HP | exact H].
  - eapply SR_cfv_bind; [exact HP | exact H].
  - exact I.
Qed.

Lemma mreal_cf_ibind {A R} : forall (t : itree astate A) (f : A -> itree astate R) c
  (P : A -> config -> Prop) (Q : R -> config -> Prop),
  mreal_cf c t P -> (forall a c', P a c' -> mreal_cf c' (f a) Q) -> mreal_cf c (ibind t f) Q.
Proof using.
  induction t as [a | q s k IH | e]; intros f c P Q H Hf; cbn in *.
  - eapply mreal_cf_SR_pre; [exact H | exact (Hf a)].
  - eapply SR_cfv_mono; [exact H|]. intros c1 Hk.
    eapply knode_cf_mono; [|exact Hk]. intros z c2 Hm. eapply IH; [exact Hm | exact Hf].
  - exact I.
Qed.

Lemma mreal_cf_mbind {A R} : forall (m : M A) (f : A -> M R) (s : astate) c
  (P : A * astate -> config -> Prop) (Q : R * astate -> config -> Prop),
  mreal_cf c (m s) P -> (forall a s' c', P (a, s') c' -> mreal_cf c' (f a s') Q) -> mreal_cf c (bind m f s) Q.
Proof using.
  intros m f s c P Q H Hf. unfold bind. eapply mreal_cf_ibind; [exact H|]. intros [a s'] c' HP. apply Hf, HP.
Qed.

Lemma mreal_cf_ret {R} : forall (r : R) (s : astate) c (Q : R * astate -> config -> Prop),
  Q (r, s) c -> mreal_cf c (ret r s) Q.
Proof using. intros r s c Q H. cbn. apply SR_cfv_ret. exact H. Qed.

Lemma mreal_cf_ask {R} : forall c q snap (k : Z -> itree astate R) Q,
  SR_cfv segs c (fun c1 => knode_cf c1 q snap (fun z c2 => mreal_cf c2 (k z) Q)) ->
  mreal_cf c (IAsk q snap k) Q.
Proof using. intros. exact H. Qed.

Lemma mreal_cf_leaf {R} : forall c (r : R) Q, SR_cfv segs c (Q r) -> mreal_cf c (IRet r) Q.
Proof using. intros. exact H. Qed.

Lemma mreal_cf_avoid {R} : forall (t : itree astate R) c (Q : R -> config -> Prop) Lim,
  vml c = Lim -> mreal_cf c t Q -> safe t -> ok04 mgrant t -> roomcf Lim t ->
  avoidv segs c (fun c' => exists r tr, cpath04 t tr r /\ Q r c').
Proof using.
  induction t as [r | q s k IH | f]; intros c Q Lim HL H Hs Hok Hrm; cbn in H, Hs.
  - eapply avoidv_mono; [exact (proj2 H)|]. intros c' H'. exists r, []. split; [reflexivity | exact H'].
  - destruct H as [_ HA]. cbn in Hok, Hrm. destruct Hrm as [Hroom Hrk].
    apply (avoidv_bind segs c _ _ HA). intros c1 [Hk Hx] HV.
    assert (STEP : forall z c2, canswer04 q z -> ok04 mgrant (k z) -> mreal_cf c2 (k z) Q -> vml c2 = Lim ->
      avoidv segs c2 (fun c' => exists r tr, cpath04 (IAsk q s k) tr r /\ Q r c')).
    { intros z c2 Hz Ho Hm HV2. eapply avoidv_mono.
      - eapply IH; [exact HV2 | exact Hm | apply Hs; apply canswer_answer_ok; apply canswer04_canswer; exact Hz | exact Ho | apply Hrk; exact Hz].
      - intros c' (r & tr & Hy & HQ). exists r, ((q, z) :: tr). cbn. auto. }
    assert (HV1 : vml c1 = Lim) by congruence.
    unfold canswer04, canswer in STEP.
    destruct q as [|np| |ln|ln|pg|rr ln|mr mol mnl|p]; cbn [charged] in Hroom, Hx; cbn in Hk, Hok, STEP.
    + destruct Hk as (J & nx & bit & i0 & Hn & Hc & Hb). destruct Hx as [Hnr Hsv].
      apply (avoidv_node segs c1 J nx _ Hn); [apply Hnr; intros E; discriminate E | intros i; apply (Hsv [] (nx i)), (proj1 Hn) |].
      intros i. eapply STEP; [exact (Hb i) | rewrite (Hb i); exact Hok | apply Hc | rewrite (Hsv [] (nx i) (proj1 Hn i)); exact HV1].
    + destruct Hk as (J & nx & bit & i0 & Hn & Hc & Hbits & _). destruct Hok as [Ho0 Ho1]. destruct Hx as [Hnr Hsv].
      assert (NR : ~ budget_refused_at segs c1) by (apply Hnr; intros _; rewrite HV1; apply Hroom; reflexivity).
      apply (avoidv_node segs c1 J nx _ Hn NR); [intros i; apply (Hsv [] (nx i)), (proj1 Hn) |].
      intros i. assert (V : vml (nx i) = Lim) by (rewrite (Hsv [] (nx i) (proj1 Hn i)); exact HV1).
      destruct (Hbits i) as [Hi|Hi]; (eapply STEP; [| | apply Hc | exact V]); rewrite Hi; auto.
    + destruct Hk as (J & nx & bit & i0 & Hn & Hc & Hb). destruct Hx as [Hnr Hsv].
      apply (avoidv_node segs c1 J nx _ Hn); [apply Hnr; intros E; discriminate E | intros i; apply (Hsv [] (nx i)), (proj1 Hn) |].
      intros i. eapply STEP; [exact (Hb i) | rewrite (Hb i); exact Hok | apply Hc | rewrite (Hsv [] (nx i) (proj1 Hn i)); exact HV1].
    + destruct Hk as (J & nx & bit & i0 & Hn & Hc & Hbits & H1). destruct Hok as [G Ho1]. destruct Hx as [Hnr Hsv].
      assert (NR : ~ budget_refused_at segs c1) by (apply Hnr; intros _; rewrite HV1; apply Hroom; reflexivity).
      assert (Hall : forall i, bit i = 1) by (destruct (H1 G) as [Hall | Hcut]; [exact Hall | contradiction]).
      apply (avoidv_node segs c1 J nx _ Hn NR); [intros i; apply (Hsv [] (nx i)), (proj1 Hn) |].
      intros i. eapply STEP; [exact (Hall i) | rewrite (Hall i); exact Ho1 | apply Hc | rewrite (Hsv [] (nx i) (proj1 Hn i)); exact HV1].
    + destruct Hk as (J & nx & bit & i0 & Hn & Hc & Hbits & H1). destruct Hok as [G Ho1]. destruct Hx as [Hnr Hsv].
      assert (NR : ~ budget_refused_at segs c1) by (apply Hnr; intros E; discriminate E).
      assert (Hall : forall i, bit i = 1) by (destruct (H1 G) as [Hall | Hcut]; [exact Hall | contradiction]).
      apply (avoidv_node segs c1 J nx _ Hn NR); [intros i; apply (Hsv [] (nx i)), (proj1 Hn) |].
      intros i. eapply STEP; [exact (Hall i) | rewrite (Hall i); exact Ho1 | apply Hc | rewrite (Hsv [] (nx i) (proj1 Hn i)); exact HV1].
    + destruct Hk as (J & nx & bit & i0 & Hn & Hc & Hbits & H1). destruct Hok as [G Ho1]. destruct Hx as [Hnr Hsv].
      assert (NR : ~ budget_refused_at segs c1) by (apply Hnr; intros _; rewrite HV1; apply Hroom; reflexivity).
      assert (Hall : forall i, bit i = 1) by (destruct (H1 G) as [Hall | Hcut]; [exact Hall | contradiction]).
      apply (avoidv_node segs c1 J nx _ Hn NR); [intros i; apply (Hsv [] (nx i)), (proj1 Hn) |].
      intros i. eapply STEP; [exact (Hall i) | rewrite (Hall i); exact Ho1 | apply Hc | rewrite (Hsv [] (nx i) (proj1 Hn i)); exact HV1].
    + destruct Hk as (J & nx & bit & i0 & Hn & Hc & Hb). destruct Hx as [Hnr Hsv].
      apply (avoidv_node segs c1 J nx _ Hn); [apply Hnr; intros E; discriminate E | intros i; apply (Hsv [] (nx i)), (proj1 Hn) |].
      intros i. eapply STEP; [exact (Hb i) | rewrite (Hb i); exact Hok | apply Hc | rewrite (Hsv [] (nx i) (proj1 Hn i)); exact HV1].
    + destruct Hk as (J & nx & bit & i0 & Hn & Hc & Hbits & _). destruct Hok as [Ho0 Ho1]. destruct Hx as [Hnr Hsv].
      assert (NR : ~ budget_refused_at segs c1) by (apply Hnr; intros _; rewrite HV1; apply Hroom; reflexivity).
      apply (avoidv_node segs c1 J nx _ Hn NR); [intros i; apply (Hsv [] (nx i)), (proj1 Hn) |].
      intros i. assert (V : vml (nx i) = Lim) by (rewrite (Hsv [] (nx i) (proj1 Hn i)); exact HV1).
      destruct (Hbits i) as [Hi|Hi]; (eapply STEP; [| | apply Hc | exact V]); rewrite Hi; auto.
    + destruct Hk as (z & Hz & Hc). eapply STEP; [exact Hz | apply Hok; exact Hz | exact Hc | exact HV1].
  - destruct Hs.
Qed.

Theorem mreal_cf_SR_cfv {R} : forall (t : itree astate R) c (Q : R -> config -> Prop),
  mreal_cf c t Q -> safe t -> ok04 mgrant t -> roomcf (vml c) t ->
  SR_cfv segs c (fun c' => exists r tr, cpath04 t tr r /\ Q r c').
Proof using.
  intros t c Q H Hs Hok Hrm. split.
  - exact (mreal_SR04 segs t c Q (mreal_cf_mreal t c Q H) Hs Hok).
  - exact (mreal_cf_avoid t c Q (vml c) eq_refl H Hs Hok Hrm).
Qed.

Theorem mreal_tset_cf {R} : forall (t : itree astate R) c (Q : R -> config -> Prop) (K : R -> TSet),
  mreal_cf c t Q -> safe t -> jinv K t -> gtree mgrant t -> roomcf (vml c) t ->
  (forall r c' tr, cpath t tr r -> Q r c' -> realizes segs c' (K r) /\ cut_free segs c') ->
  realizes segs c (tset t K) /\ cut_free segs c.
Proof using.
  intros t c Q K H Hs Hj Hg Hrm HK. split.
  - apply (mreal_tset segs t c Q K (mreal_cf_mreal t c Q H) Hs Hj Hg).
    intros r c' tr Hp HQ. exact (proj1 (HK r c' tr Hp HQ)).
  - apply (avoid_cut_free segs c (fun c' => exists r tr, cpath04 t tr r /\ Q r c')).
    + apply avoidv_avoid. exact (mreal_cf_avoid t c Q (vml c) eq_refl H Hs (gtree_ok04 mgrant t Hg) Hrm).
    + intros c' (r & tr & Hp & HQ). exact (proj2 (HK r c' tr (cpath04_cpath t tr r Hp) HQ)).
Qed.

End h.

Section u.
Variable B : malloc_syms.
Variable MR : MR_t.
Let segs := ms_segs B.

Definition malloc_realizes_cf : Prop :=
  forall L A regs mem md n,
  call_pre B MR L A regs mem md ->
  getr regs 10 = Z_to_bv 64 n -> 0 <= n < 2 ^ 62 ->
  mreal_cf segs (mkCfg (mkst regs (Z_to_bv 64 (ms_malloc B)) mem (seg_rom segs)) md)
    (malloc n A)
    (malloc_leaf B MR L A regs mem md n).

Definition free_realizes_cf : Prop :=
  forall L A regs mem md p n,
  call_pre B MR L A regs mem md ->
  In (p, n) (user_blocks A) -> getr regs 10 = Z_to_bv 64 (ptr_addr L p) ->
  mreal_cf segs (mkCfg (mkst regs (Z_to_bv 64 (ms_free B)) mem (seg_rom segs)) md)
    (free (Some p) A)
    (free_leaf B MR L A regs mem md p n).

Lemma malloc_realizes_of_cf : malloc_realizes_cf -> malloc_realizes B MR.
Proof using.
  intros H L A regs mem md n Hpre Hn Hr. exact (mreal_cf_mreal segs _ _ _ (H L A regs mem md n Hpre Hn Hr)).
Qed.

Lemma free_realizes_of_cf : free_realizes_cf -> free_realizes B MR.
Proof using.
  intros H L A regs mem md p n Hpre Hin Hp. exact (mreal_cf_mreal segs _ _ _ (H L A regs mem md p n Hpre Hin Hp)).
Qed.

Theorem malloc_tset_cf :
  malloc_realizes_cf ->
  forall L A regs mem md n (K : option sptr * astate -> TSet),
  call_pre B MR L A regs mem md -> getr regs 10 = Z_to_bv 64 n -> 0 <= n < 2 ^ 62 ->
  jinv K (malloc n A) -> gtree mgrant (malloc n A) ->
  roomcf (vm_limit (m_vmmaps md)) (malloc n A) ->
  (forall r c' tr, cpath (malloc n A) tr r -> malloc_leaf B MR L A regs mem md n r c' ->
     realizes segs c' (K r) /\ cut_free segs c') ->
  realizes segs (mkCfg (mkst regs (Z_to_bv 64 (ms_malloc B)) mem (seg_rom segs)) md) (tset (malloc n A) K) /\
  cut_free segs (mkCfg (mkst regs (Z_to_bv 64 (ms_malloc B)) mem (seg_rom segs)) md).
Proof using.
  intros HM L A regs mem md n K Hpre Hn Hrange Hj Hg Hrm HK.
  assert (HW : WF A) by (destruct Hpre as (_ & HW & _); exact HW).
  apply (mreal_tset_cf segs _ _ _ K (HM L A regs mem md n Hpre Hn Hrange));
    [apply malloc_safe; [exact HW | lia] | exact Hj | exact Hg | exact Hrm | exact HK].
Qed.

Theorem free_tset_cf :
  free_realizes_cf ->
  forall L A regs mem md p n (K : unit * astate -> TSet),
  call_pre B MR L A regs mem md -> In (p, n) (user_blocks A) -> getr regs 10 = Z_to_bv 64 (ptr_addr L p) ->
  jinv K (free (Some p) A) -> gtree mgrant (free (Some p) A) ->
  roomcf (vm_limit (m_vmmaps md)) (free (Some p) A) ->
  (forall r c' tr, cpath (free (Some p) A) tr r -> free_leaf B MR L A regs mem md p n r c' ->
     realizes segs c' (K r) /\ cut_free segs c') ->
  realizes segs (mkCfg (mkst regs (Z_to_bv 64 (ms_free B)) mem (seg_rom segs)) md) (tset (free (Some p) A) K) /\
  cut_free segs (mkCfg (mkst regs (Z_to_bv 64 (ms_free B)) mem (seg_rom segs)) md).
Proof using.
  intros HF L A regs mem md p n K Hpre Hin Hp Hj Hg Hrm HK.
  assert (HW : WF A) by (destruct Hpre as (_ & HW & _); exact HW).
  apply (mreal_tset_cf segs _ _ _ K (HF L A regs mem md p n Hpre Hin Hp));
    [eapply free_safe; [exact HW | exact Hin] | exact Hj | exact Hg | exact Hrm | exact HK].
Qed.

End u.
End d.
Arguments knode_cf segs c1 q snap Kont : clear implicits.
