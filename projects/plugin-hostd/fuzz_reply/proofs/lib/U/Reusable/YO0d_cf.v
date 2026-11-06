From Stdlib Require Import ZArith List Bool Lia Classical_Prop.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YK11 YK0s YK0i YK15 YM06 YM02 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YO0i YO0f YO0x YO0d YO0p YM06_cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable.R Require Import Cfg.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import PlaceCapW.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Uniform.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require AgreeLim.
Import ListNotations.
Local Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Definition charged (q : kreq) : bool :=
  match q with
  | KMmapRW _ | KMprotect _ | KBrkGrow _ | KMremap _ _ _ => true
  | _ => false
  end.

(* The requests the placement policy places: anonymous mmaps and moved mremaps. *)
Definition slotted (q : kreq) : bool :=
  match q with
  | KMmapRW _ | KMmapNone _ | KMremap _ _ _ => true
  | _ => false
  end.

(* What the policy's window count needs at such a request: the ledger's bytes under the budget, a slot count the
   window holds (PlaceCapW), and a modest length. *)
Definition slot_room (X : Z) (s : astate) (q : kreq) : Prop :=
  live_bytes s <= X /\ nslots s + KRES <= slot_capW (req_len q) /\ 0 < req_len q <= MG_REQ.

Fixpoint roomcf {A : Type} (X : Z) (t : itree astate A) : Prop :=
  match t with
  | IRet _ => True
  | IFail _ => True
  | IAsk q s k => (charged q = true -> live_bytes s + req_len q <= X) /\
      (slotted q = true -> X <= AgreeLim.LIM_AG -> slot_room X s q) /\ (forall z, canswer04 q z -> roomcf X (k z))
  end.

Section h.
Variable segs : list Segment.

Definition knode_cf (c1 : config) (q : kreq) (snap : astate) (Kont : Z -> config -> Prop) : Prop :=
  knode segs c1 q snap Kont /\
  match q with
  | KJunk _ => True
  | _ =>
      ((charged q = true -> live_bytes snap + req_len q <= vml c1) -> ~ budget_refused_at segs c1) /\
      (forall e c2, sstep_cfg segs ACFG c1 e (SNext c2) -> vml c2 = vml c1) /\
      ms_svc_pending (cfg_ms c1) <> None /\
      ((charged q = true -> live_bytes snap + req_len q <= vml c1) ->
       (slotted q = true -> vml c1 <= AgreeLim.LIM_AG -> slot_room (vml c1) snap q) -> canon_fit_at segs c1)
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

(* The policy's step at a node of the walk, from the room the tree gives the node. *)
Lemma knode_cf_fit : forall c1 q snap (K : Z -> config -> Prop), (forall p, q <> KJunk p) -> knode_cf c1 q snap K ->
  (charged q = true -> live_bytes snap + req_len q <= vml c1) ->
  (slotted q = true -> vml c1 <= AgreeLim.LIM_AG -> slot_room (vml c1) snap q) -> canon_fit_at segs c1.
Proof using.
  intros c1 q snap K HJ [_ X]. destruct q; try exact (proj2 (proj2 (proj2 X))).
  exfalso. exact (HJ _ eq_refl).
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
  - eapply avoidv_mono; [exact (SR_cfv_avoidv segs _ _ H)|]. intros c' H'. exists r, []. split; [reflexivity | exact H'].
  - pose proof (SR_cfv_avoidv segs _ _ H) as HA. cbn in Hok, Hrm. destruct Hrm as (Hroom & _ & Hrk).
    apply (avoidv_bind segs c _ _ HA). intros c1 [Hk Hx] HV.
    assert (STEP : forall z c2, canswer04 q z -> ok04 mgrant (k z) -> mreal_cf c2 (k z) Q -> vml c2 = Lim ->
      avoidv segs c2 (fun c' => exists r tr, cpath04 (IAsk q s k) tr r /\ Q r c')).
    { intros z c2 Hz Ho Hm HV2. eapply avoidv_mono.
      - eapply IH; [exact HV2 | exact Hm | apply Hs; apply canswer_answer_ok; apply canswer04_canswer; exact Hz | exact Ho | apply Hrk; exact Hz].
      - intros c' (r & tr & Hy & HQ). exists r, ((q, z) :: tr). cbn. auto. }
    assert (HV1 : vml c1 = Lim) by congruence.
    unfold canswer04, canswer in STEP.
    destruct q as [|np| |ln|ln|pg|rr ln|mr mol mnl|p]; cbn [charged] in Hroom, Hx; cbn in Hk, Hok, STEP.
    + destruct Hk as (J & nx & bit & i0 & Hn & Hc & Hb). destruct Hx as [Hnr [Hsv _]].
      apply (avoidv_node segs c1 J nx _ Hn); [apply Hnr; intros E; discriminate E | intros i; apply (Hsv [] (nx i)), (proj1 Hn) |].
      intros i. eapply STEP; [exact (Hb i) | rewrite (Hb i); exact Hok | apply Hc | rewrite (Hsv [] (nx i) (proj1 Hn i)); exact HV1].
    + destruct Hk as (J & nx & bit & i0 & Hn & Hc & Hbits & _). destruct Hok as [Ho0 Ho1]. destruct Hx as [Hnr [Hsv _]].
      assert (NR : ~ budget_refused_at segs c1) by (apply Hnr; intros _; rewrite HV1; apply Hroom; reflexivity).
      apply (avoidv_node segs c1 J nx _ Hn NR); [intros i; apply (Hsv [] (nx i)), (proj1 Hn) |].
      intros i. assert (V : vml (nx i) = Lim) by (rewrite (Hsv [] (nx i) (proj1 Hn i)); exact HV1).
      destruct (Hbits i) as [Hi|Hi]; (eapply STEP; [| | apply Hc | exact V]); rewrite Hi; auto.
    + destruct Hk as (J & nx & bit & i0 & Hn & Hc & Hb). destruct Hx as [Hnr [Hsv _]].
      apply (avoidv_node segs c1 J nx _ Hn); [apply Hnr; intros E; discriminate E | intros i; apply (Hsv [] (nx i)), (proj1 Hn) |].
      intros i. eapply STEP; [exact (Hb i) | rewrite (Hb i); exact Hok | apply Hc | rewrite (Hsv [] (nx i) (proj1 Hn i)); exact HV1].
    + destruct Hk as (J & nx & bit & i0 & Hn & Hc & Hbits & H1). destruct Hok as [G Ho1]. destruct Hx as [Hnr [Hsv _]].
      assert (NR : ~ budget_refused_at segs c1) by (apply Hnr; intros _; rewrite HV1; apply Hroom; reflexivity).
      assert (Hall : forall i, bit i = 1) by (destruct (H1 G) as [Hall | Hcut]; [exact Hall | contradiction]).
      apply (avoidv_node segs c1 J nx _ Hn NR); [intros i; apply (Hsv [] (nx i)), (proj1 Hn) |].
      intros i. eapply STEP; [exact (Hall i) | rewrite (Hall i); exact Ho1 | apply Hc | rewrite (Hsv [] (nx i) (proj1 Hn i)); exact HV1].
    + destruct Hk as (J & nx & bit & i0 & Hn & Hc & Hbits & H1). destruct Hok as [G Ho1]. destruct Hx as [Hnr [Hsv _]].
      assert (NR : ~ budget_refused_at segs c1) by (apply Hnr; intros E; discriminate E).
      assert (Hall : forall i, bit i = 1) by (destruct (H1 G) as [Hall | Hcut]; [exact Hall | contradiction]).
      apply (avoidv_node segs c1 J nx _ Hn NR); [intros i; apply (Hsv [] (nx i)), (proj1 Hn) |].
      intros i. eapply STEP; [exact (Hall i) | rewrite (Hall i); exact Ho1 | apply Hc | rewrite (Hsv [] (nx i) (proj1 Hn i)); exact HV1].
    + destruct Hk as (J & nx & bit & i0 & Hn & Hc & Hbits & H1). destruct Hok as [G Ho1]. destruct Hx as [Hnr [Hsv _]].
      assert (NR : ~ budget_refused_at segs c1) by (apply Hnr; intros _; rewrite HV1; apply Hroom; reflexivity).
      assert (Hall : forall i, bit i = 1) by (destruct (H1 G) as [Hall | Hcut]; [exact Hall | contradiction]).
      apply (avoidv_node segs c1 J nx _ Hn NR); [intros i; apply (Hsv [] (nx i)), (proj1 Hn) |].
      intros i. eapply STEP; [exact (Hall i) | rewrite (Hall i); exact Ho1 | apply Hc | rewrite (Hsv [] (nx i) (proj1 Hn i)); exact HV1].
    + destruct Hk as (J & nx & bit & i0 & Hn & Hc & Hb). destruct Hx as [Hnr [Hsv _]].
      apply (avoidv_node segs c1 J nx _ Hn); [apply Hnr; intros E; discriminate E | intros i; apply (Hsv [] (nx i)), (proj1 Hn) |].
      intros i. eapply STEP; [exact (Hb i) | rewrite (Hb i); exact Hok | apply Hc | rewrite (Hsv [] (nx i) (proj1 Hn i)); exact HV1].
    + destruct Hk as (J & nx & bit & i0 & Hn & Hc & Hbits & _). destruct Hok as [Ho0 Ho1]. destruct Hx as [Hnr [Hsv _]].
      assert (NR : ~ budget_refused_at segs c1) by (apply Hnr; intros _; rewrite HV1; apply Hroom; reflexivity).
      apply (avoidv_node segs c1 J nx _ Hn NR); [intros i; apply (Hsv [] (nx i)), (proj1 Hn) |].
      intros i. assert (V : vml (nx i) = Lim) by (rewrite (Hsv [] (nx i) (proj1 Hn i)); exact HV1).
      destruct (Hbits i) as [Hi|Hi]; (eapply STEP; [| | apply Hc | exact V]); rewrite Hi; auto.
    + destruct Hk as (z & Hz & Hc). eapply STEP; [exact Hz | apply Hok; exact Hz | exact Hc | exact HV1].
  - destruct Hs.
Qed.

Theorem mreal_cf_SR_cf {R} : forall (t : itree astate R) c (Q : R -> config -> Prop),
  mreal_cf c t Q -> safe t -> ok04 mgrant t -> roomcf (vml c) t ->
  SR_cf segs c (fun c' => exists r tr, cpath04 t tr r /\ Q r c').
Proof using.
  intros t c Q H Hs Hok Hrm. split.
  - exact (mreal_SR04 segs t c Q (mreal_cf_mreal t c Q H) Hs Hok).
  - apply avoidv_avoid. exact (mreal_cf_avoid t c Q (vml c) eq_refl H Hs Hok Hrm).
Qed.

(* Reachable configurations of a cut-free allocator walk: an instruction configuration inside a segment, a node of
   the tree (with its subtree), or a configuration after a leaf. *)
Fixpoint subt {A} (t : itree astate A) (pre : list (kreq * Z)) (u : itree astate A) {struct pre} : Prop :=
  match pre with
  | [] => u = t
  | (q', z) :: pre' =>
      match t with
      | IAsk q _ k => q' = q /\ canswer04 q z /\ subt (k z) pre' u
      | _ => False
      end
  end.

Lemma subt_cpath04 {A} : forall pre (t u : itree astate A) tr r, subt t pre u -> cpath04 u tr r -> cpath04 t (pre ++ tr) r.
Proof using.
  induction pre as [|[q' z] pre IH]; intros t u tr r H Hc; cbn in H |- *.
  - subst u. exact Hc.
  - destruct t as [a | q s k | f]; try contradiction. destruct H as (-> & Hz & H).
    split; [reflexivity|]. split; [exact Hz | exact (IH _ _ _ _ H Hc)].
Qed.

Lemma subt_cpath {A} : forall pre (t u : itree astate A) tr r, subt t pre u -> cpath u tr r -> cpath t (pre ++ tr) r.
Proof using.
  induction pre as [|[q' z] pre IH]; intros t u tr r H Hc; cbn in H |- *.
  - subst u. exact Hc.
  - destruct t as [a | q s k | f]; try contradiction. destruct H as (-> & Hz & H).
    split; [reflexivity|]. split; [exact (canswer04_canswer q z Hz) | exact (IH _ _ _ _ H Hc)].
Qed.

Lemma subt_inherit {A} (Pr : itree astate A -> Prop) :
  (forall q s k z, Pr (IAsk q s k) -> canswer04 q z -> Pr (k z)) ->
  forall pre t u, subt t pre u -> Pr t -> Pr u.
Proof using.
  intros HP pre. induction pre as [|[q' z] pre IH]; intros t u H Ht; cbn in H.
  - subst u. exact Ht.
  - destruct t as [a | q s k | f]; try contradiction. destruct H as (-> & Hz & H).
    exact (IH _ _ H (HP q s k z Ht Hz)).
Qed.

Lemma safe_sub {A} : forall q s (k : Z -> itree astate A) z, safe (IAsk q s k) -> canswer04 q z -> safe (k z).
Proof using. intros q s k z H Hz. apply H. apply canswer_answer_ok. apply canswer04_canswer. exact Hz. Qed.

Lemma ok04_sub {A} : forall G q s (k : Z -> itree astate A) z, ok04 G (IAsk q s k) -> canswer04 q z -> ok04 G (k z).
Proof using.
  intros G q s k z H Hz. unfold canswer04, canswer in Hz.
  destruct q; cbn in H, Hz; try (subst z; tauto); try (destruct Hz as [-> | ->]; tauto).
  apply H. exact Hz.
Qed.

Lemma roomcf_sub {A} : forall X q s (k : Z -> itree astate A) z, roomcf X (IAsk q s k) -> canswer04 q z -> roomcf X (k z).
Proof using. intros X q s k z H Hz. exact (proj2 (proj2 H) z Hz). Qed.

Lemma roomcf_node {A} : forall X q s (k : Z -> itree astate A), roomcf X (IAsk q s k) ->
  (charged q = true -> live_bytes s + req_len q <= X) /\ (slotted q = true -> X <= AgreeLim.LIM_AG -> slot_room X s q).
Proof using. intros X q s k H. exact (conj (proj1 H) (proj1 (proj2 H))). Qed.

Lemma gtree_sub {A} : forall G q s (k : Z -> itree astate A) z, gtree G (IAsk q s k) -> canswer04 q z -> gtree G (k z).
Proof using.
  intros G q s k z H Hz. unfold canswer04, canswer in Hz.
  destruct q; cbn in H, Hz; try (subst z; tauto); try (destruct Hz as [-> | ->]; tauto).
  apply H. exact Hz.
Qed.

Lemma jinv_sub {A} : forall (K : A -> TSet) q s (k : Z -> itree astate A) z, jinv K (IAsk q s k) -> canswer04 q z -> jinv K (k z).
Proof using.
  intros K q s k z H Hz. unfold canswer04, canswer in Hz.
  destruct q; cbn in H, Hz; try (subst z; tauto); try (destruct Hz as [-> | ->]; tauto).
  apply (proj2 H). exact Hz.
Qed.

Lemma star_first : forall (P : config -> Prop) c tr c'',
  star_cfg segs ACFG c tr c'' ->
  reach_av segs P c c'' \/
  exists c1 tr2, P c1 /\ (c1 = c \/ exists c0 e, reach_av segs P c c0 /\ sstep_cfg segs ACFG c0 e (SNext c1)) /\
    star_cfg segs ACFG c1 tr2 c''.
Proof using.
  intros P c tr c'' H. induction H as [c | c1 evs c2 tr c3 Hs Hst IH].
  - destruct (classic (P c)) as [HP|HP].
    + right. exists c, []. split; [exact HP|]. split; [left; reflexivity | apply star_cfg_refl].
    + left. apply ra_refl. exact HP.
  - destruct (classic (P c1)) as [HP|HP].
    + right. exists c1, (evs ++ tr). split; [exact HP|]. split; [left; reflexivity|]. eapply star_cfg_step; eassumption.
    + destruct IH as [IH | (c4 & tr4 & HP4 & Hw & Hst4)].
      * left. eapply ra_step; eassumption.
      * right. exists c4, tr4. split; [exact HP4|]. split; [|exact Hst4].
        right. destruct Hw as [-> | (c0 & e & Hr & Hs0)].
        -- exists c1, evs. split; [apply ra_refl; exact HP | exact Hs].
        -- exists c0, e. split; [eapply ra_step; eassumption | exact Hs0].
Qed.

Lemma first_vml : forall P c c1 Lim, avoidv segs c P -> vml c = Lim ->
  (c1 = c \/ exists c0 e, reach_av segs P c c0 /\ sstep_cfg segs ACFG c0 e (SNext c1)) -> vml c1 = Lim.
Proof using.
  intros P c c1 Lim HA HV [-> | (c0 & e & Hr & Hs)]; [exact HV|].
  destruct (HA c0 Hr) as (_ & V & S). rewrite (S e c1 Hs). congruence.
Qed.

(* The steps out of a node of the walk: no event, an answer the cut-free tree follows, the same budget. *)
Lemma knode_cf_succ {R} : forall c1 q s (k : Z -> itree astate R) (Q : R -> config -> Prop) Lim,
  (forall p, q <> KJunk p) -> vml c1 = Lim ->
  knode_cf c1 q s (fun z c2 => mreal_cf c2 (k z) Q) -> ok04 mgrant (IAsk q s k) -> roomcf Lim (IAsk q s k) ->
  forall e c2, sstep_cfg segs ACFG c1 e (SNext c2) ->
  e = [] /\ exists z, canswer04 q z /\ mreal_cf c2 (k z) Q /\ vml c2 = Lim.
Proof using.
  intros c1 q s k Q Lim HJ HV1 [Hk Hx] Hok Hrm e c2 Hs.
  cbn in Hok, Hrm. destruct Hrm as [Hroom _]. unfold canswer04, canswer.
  destruct q as [|np| |ln|ln|pg|rr ln|mr mol mnl|p]; cbn [charged] in Hroom, Hx; cbn in Hk, Hok |- *.
  - destruct Hk as (J & nx & bit & i0 & Hn & Hc & Hb). destruct Hx as [_ [Hsv _]].
    destruct ((proj2 Hn) e (SNext c2) Hs) as (i & He & E). injection E as ->.
    split; [exact He|]. exists (bit i). split; [exact (Hb i)|]. split; [apply Hc | rewrite (Hsv e (nx i) Hs); exact HV1].
  - destruct Hk as (J & nx & bit & i0 & Hn & Hc & Hbits & _). destruct Hx as [_ [Hsv _]].
    destruct ((proj2 Hn) e (SNext c2) Hs) as (i & He & E). injection E as ->.
    split; [exact He|]. exists (bit i). split; [exact (Hbits i)|]. split; [apply Hc | rewrite (Hsv e (nx i) Hs); exact HV1].
  - destruct Hk as (J & nx & bit & i0 & Hn & Hc & Hb). destruct Hx as [_ [Hsv _]].
    destruct ((proj2 Hn) e (SNext c2) Hs) as (i & He & E). injection E as ->.
    split; [exact He|]. exists (bit i). split; [exact (Hb i)|]. split; [apply Hc | rewrite (Hsv e (nx i) Hs); exact HV1].
  - destruct Hk as (J & nx & bit & i0 & Hn & Hc & Hbits & H1). destruct Hok as [G _]. destruct Hx as [Hnr [Hsv _]].
    assert (NR : ~ budget_refused_at segs c1) by (apply Hnr; intros _; rewrite HV1; apply Hroom; reflexivity).
    assert (Hall : forall i, bit i = 1) by (destruct (H1 G) as [Hall | Hcut]; [exact Hall | contradiction]).
    destruct ((proj2 Hn) e (SNext c2) Hs) as (i & He & E). injection E as ->.
    split; [exact He|]. exists (bit i). split; [exact (Hall i)|]. split; [apply Hc | rewrite (Hsv e (nx i) Hs); exact HV1].
  - destruct Hk as (J & nx & bit & i0 & Hn & Hc & Hbits & H1). destruct Hok as [G _]. destruct Hx as [Hnr [Hsv _]].
    assert (NR : ~ budget_refused_at segs c1) by (apply Hnr; intros E; discriminate E).
    assert (Hall : forall i, bit i = 1) by (destruct (H1 G) as [Hall | Hcut]; [exact Hall | contradiction]).
    destruct ((proj2 Hn) e (SNext c2) Hs) as (i & He & E). injection E as ->.
    split; [exact He|]. exists (bit i). split; [exact (Hall i)|]. split; [apply Hc | rewrite (Hsv e (nx i) Hs); exact HV1].
  - destruct Hk as (J & nx & bit & i0 & Hn & Hc & Hbits & H1). destruct Hok as [G _]. destruct Hx as [Hnr [Hsv _]].
    assert (NR : ~ budget_refused_at segs c1) by (apply Hnr; intros _; rewrite HV1; apply Hroom; reflexivity).
    assert (Hall : forall i, bit i = 1) by (destruct (H1 G) as [Hall | Hcut]; [exact Hall | contradiction]).
    destruct ((proj2 Hn) e (SNext c2) Hs) as (i & He & E). injection E as ->.
    split; [exact He|]. exists (bit i). split; [exact (Hall i)|]. split; [apply Hc | rewrite (Hsv e (nx i) Hs); exact HV1].
  - destruct Hk as (J & nx & bit & i0 & Hn & Hc & Hb). destruct Hx as [_ [Hsv _]].
    destruct ((proj2 Hn) e (SNext c2) Hs) as (i & He & E). injection E as ->.
    split; [exact He|]. exists (bit i). split; [exact (Hb i)|]. split; [apply Hc | rewrite (Hsv e (nx i) Hs); exact HV1].
  - destruct Hk as (J & nx & bit & i0 & Hn & Hc & Hbits & _). destruct Hx as [_ [Hsv _]].
    destruct ((proj2 Hn) e (SNext c2) Hs) as (i & He & E). injection E as ->.
    split; [exact He|]. exists (bit i). split; [exact (Hbits i)|]. split; [apply Hc | rewrite (Hsv e (nx i) Hs); exact HV1].
  - exfalso. exact (HJ p eq_refl).
Qed.

Lemma mreal_cf_reach {R} : forall (t : itree astate R) c (Q : R -> config -> Prop) Lim tr c'',
  vml c = Lim -> mreal_cf c t Q -> safe t -> ok04 mgrant t -> roomcf Lim t ->
  star_cfg segs ACFG c tr c'' ->
  ms_svc_pending (cfg_ms c'') = None \/
  (exists pre q s k, subt t pre (IAsk q s k) /\ (forall p, q <> KJunk p) /\ vml c'' = Lim /\
     knode_cf c'' q s (fun z c2 => mreal_cf c2 (k z) Q)) \/
  (exists r trl c' tr2, cpath04 t trl r /\ Q r c' /\ star_cfg segs ACFG c' tr2 c'').
Proof using.
  induction t as [r | q s k IH | f]; intros c Q Lim tr c'' HV H Hs Hok Hrm Hst; cbn in H.
  - destruct (star_first (Q r) c tr c'' Hst) as [Hr | (c1 & tr2 & HQ & _ & Hst2)].
    + left. exact (SR_cfv_avoidi segs _ _ H c'' Hr).
    + right; right. exists r, [], c1, tr2. split; [reflexivity|]. split; [exact HQ | exact Hst2].
  - destruct (star_first (fun c1 => knode_cf c1 q s (fun z c2 => mreal_cf c2 (k z) Q)) c tr c'' Hst)
      as [Hr | (c1 & tr2 & HP & Hw & Hst2)].
    + left. exact (SR_cfv_avoidi segs _ _ H c'' Hr).
    + pose proof (first_vml _ c c1 Lim (SR_cfv_avoidv segs _ _ H) HV Hw) as HV1.
      assert (LIFT : forall z, canswer04 q z -> forall c2 tr3, vml c2 = Lim -> mreal_cf c2 (k z) Q ->
        star_cfg segs ACFG c2 tr3 c'' ->
        ms_svc_pending (cfg_ms c'') = None \/
        (exists pre q' s' k', subt (IAsk q s k) pre (IAsk q' s' k') /\ (forall p, q' <> KJunk p) /\ vml c'' = Lim /\
           knode_cf c'' q' s' (fun z c2 => mreal_cf c2 (k' z) Q)) \/
        (exists r trl c' tr2, cpath04 (IAsk q s k) trl r /\ Q r c' /\ star_cfg segs ACFG c' tr2 c'')).
      { intros z Hz c2 tr3 HV2 Hm Hst3.
        destruct (IH z c2 Q Lim tr3 c'' HV2 Hm (safe_sub q s k z Hs Hz) (ok04_sub mgrant q s k z Hok Hz)
          (roomcf_sub Lim q s k z Hrm Hz) Hst3)
          as [Ha | [(pre & q' & s' & k' & Hsub & HJ & HVc & Hkn) | (r & trl & c' & tr4 & Hp & HQ & Hst4)]].
        - left. exact Ha.
        - right; left. exists ((q, z) :: pre), q', s', k'. split; [cbn; auto|]. auto.
        - right; right. exists r, ((q, z) :: trl), c', tr4. split; [cbn; auto|]. auto. }
      destruct (classic (exists p, q = KJunk p)) as [(p & ->) | HJ].
      * destruct HP as [(z & Hz & Hm) _].
        assert (Hz' : canswer04 (KJunk p) z) by (cbn; exact Hz).
        exact (LIFT z Hz' c1 tr2 HV1 Hm Hst2).
      * assert (HJ' : forall p, q <> KJunk p) by (intros p E; apply HJ; exists p; exact E).
        inversion Hst2 as [c0 E1 E2 E3 | c0 evs c2 tr3 c3 Hs1 Hst3 E1 E2 E3]; subst.
        -- right; left. exists [], q, s, k. split; [reflexivity|]. split; [exact HJ'|]. split; [exact HV1 | exact HP].
        -- destruct (knode_cf_succ c1 q s k Q _ HJ' HV1 HP Hok Hrm evs c2 Hs1) as (_ & z & Hz & Hm & HV2).
           exact (LIFT z Hz c2 tr3 HV2 Hm Hst3).
  - exact (False_ind _ Hs).
Qed.

Lemma canswer04_1 : forall q, canswer04 q 1.
Proof using. intros q. unfold canswer04, canswer. destruct q; cbn; first [reflexivity | right; reflexivity | lia]. Qed.

Lemma subt_app {A} : forall pre (t : itree astate A) q s k z,
  subt t pre (IAsk q s k) -> canswer04 q z -> subt t (pre ++ [(q, z)]) (k z).
Proof using.
  induction pre as [|[q' z'] pre IH]; intros t q s k z H Hz; cbn in H |- *.
  - subst t. cbn. split; [reflexivity|]. split; [exact Hz | reflexivity].
  - destruct t as [a | q0 s0 k0 | f]; try contradiction. destruct H as (-> & Hz' & H).
    split; [reflexivity|]. split; [exact Hz' | exact (IH _ _ _ _ _ H Hz)].
Qed.

(* Under gtree mgrant every step out of a node takes the answer 1. *)
Lemma knode_cf_succ_g {R} : forall c1 q s (k : Z -> itree astate R) (Q : R -> config -> Prop) Lim,
  (forall p, q <> KJunk p) -> vml c1 = Lim ->
  knode_cf c1 q s (fun z c2 => mreal_cf c2 (k z) Q) -> gtree mgrant (IAsk q s k) -> roomcf Lim (IAsk q s k) ->
  forall e c2, sstep_cfg segs ACFG c1 e (SNext c2) -> e = [] /\ mreal_cf c2 (k 1) Q /\ vml c2 = Lim.
Proof using.
  intros c1 q s k Q Lim HJ HV1 [Hk Hx] Hg Hrm e c2 Hs.
  cbn in Hg, Hrm. destruct Hrm as [Hroom _].
  destruct q as [|np| |ln|ln|pg|rr ln|mr mol mnl|p]; cbn [charged] in Hroom, Hx; cbn in Hk, Hg.
  - destruct Hk as (J & nx & bit & i0 & Hn & Hc & Hb). destruct Hx as [_ [Hsv _]].
    destruct ((proj2 Hn) e (SNext c2) Hs) as (i & He & E). injection E as ->.
    pose proof (Hc i) as Hci. rewrite (Hb i) in Hci.
    split; [exact He|]. split; [exact Hci | rewrite (Hsv e (nx i) Hs); exact HV1].
  - destruct Hk as (J & nx & bit & i0 & Hn & Hc & Hbits & H1). destruct Hg as [G _]. destruct Hx as [Hnr [Hsv _]].
    assert (NR : ~ budget_refused_at segs c1) by (apply Hnr; intros _; rewrite HV1; apply Hroom; reflexivity).
    assert (Hall : forall i, bit i = 1) by (destruct (H1 G) as [Hall | Hcut]; [exact Hall | contradiction]).
    destruct ((proj2 Hn) e (SNext c2) Hs) as (i & He & E). injection E as ->.
    pose proof (Hc i) as Hci. rewrite (Hall i) in Hci.
    split; [exact He|]. split; [exact Hci | rewrite (Hsv e (nx i) Hs); exact HV1].
  - destruct Hk as (J & nx & bit & i0 & Hn & Hc & Hb). destruct Hx as [_ [Hsv _]].
    destruct ((proj2 Hn) e (SNext c2) Hs) as (i & He & E). injection E as ->.
    pose proof (Hc i) as Hci. rewrite (Hb i) in Hci.
    split; [exact He|]. split; [exact Hci | rewrite (Hsv e (nx i) Hs); exact HV1].
  - destruct Hk as (J & nx & bit & i0 & Hn & Hc & Hbits & H1). destruct Hg as [G _]. destruct Hx as [Hnr [Hsv _]].
    assert (NR : ~ budget_refused_at segs c1) by (apply Hnr; intros _; rewrite HV1; apply Hroom; reflexivity).
    assert (Hall : forall i, bit i = 1) by (destruct (H1 G) as [Hall | Hcut]; [exact Hall | contradiction]).
    destruct ((proj2 Hn) e (SNext c2) Hs) as (i & He & E). injection E as ->.
    pose proof (Hc i) as Hci. rewrite (Hall i) in Hci.
    split; [exact He|]. split; [exact Hci | rewrite (Hsv e (nx i) Hs); exact HV1].
  - destruct Hk as (J & nx & bit & i0 & Hn & Hc & Hbits & H1). destruct Hg as [G _]. destruct Hx as [Hnr [Hsv _]].
    assert (NR : ~ budget_refused_at segs c1) by (apply Hnr; intros E; discriminate E).
    assert (Hall : forall i, bit i = 1) by (destruct (H1 G) as [Hall | Hcut]; [exact Hall | contradiction]).
    destruct ((proj2 Hn) e (SNext c2) Hs) as (i & He & E). injection E as ->.
    pose proof (Hc i) as Hci. rewrite (Hall i) in Hci.
    split; [exact He|]. split; [exact Hci | rewrite (Hsv e (nx i) Hs); exact HV1].
  - destruct Hk as (J & nx & bit & i0 & Hn & Hc & Hbits & H1). destruct Hg as [G _]. destruct Hx as [Hnr [Hsv _]].
    assert (NR : ~ budget_refused_at segs c1) by (apply Hnr; intros _; rewrite HV1; apply Hroom; reflexivity).
    assert (Hall : forall i, bit i = 1) by (destruct (H1 G) as [Hall | Hcut]; [exact Hall | contradiction]).
    destruct ((proj2 Hn) e (SNext c2) Hs) as (i & He & E). injection E as ->.
    pose proof (Hc i) as Hci. rewrite (Hall i) in Hci.
    split; [exact He|]. split; [exact Hci | rewrite (Hsv e (nx i) Hs); exact HV1].
  - destruct Hk as (J & nx & bit & i0 & Hn & Hc & Hb). destruct Hx as [_ [Hsv _]].
    destruct ((proj2 Hn) e (SNext c2) Hs) as (i & He & E). injection E as ->.
    pose proof (Hc i) as Hci. rewrite (Hb i) in Hci.
    split; [exact He|]. split; [exact Hci | rewrite (Hsv e (nx i) Hs); exact HV1].
  - destruct Hg as [G _]. destruct G.
  - exfalso. exact (HJ p eq_refl).
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


Definition realloc_realizes_cf : Prop :=
  forall pc L A regs mem md p nold n,
  ms_realloc B = Some pc ->
  call_pre_k B MR REALLOC_STACK L A regs mem md ->
  In (p, nold) (user_blocks A) ->
  getr regs 10 = Z_to_bv 64 (ptr_addr L p) -> getr regs 11 = Z_to_bv 64 n ->
  0 <= n < 2 ^ 62 ->
  mreal_cf segs (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom segs)) md)
    (realloc (Some p) n A)
    (realloc_leaf B MR L A regs mem md p nold n).

(* realloc (NULL, n) enters malloc's body with the caller's return address: the cut-free certificate needs that
   address to differ from malloc's entry. *)
Definition realloc_null_realizes_cf : Prop :=
  forall pc L A regs mem md n,
  ms_realloc B = Some pc ->
  call_pre_k B MR REALLOC_STACK L A regs mem md ->
  getr regs 10 = Z_to_bv 64 0 -> getr regs 11 = Z_to_bv 64 n -> 0 <= n < 2 ^ 62 ->
  getr regs 1 <> Z_to_bv 64 (ms_malloc B) ->
  mreal_cf segs (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom segs)) md)
    (realloc None n A)
    (realloc_null_leaf B MR L A regs mem md n).
End u.
End d.
Arguments knode_cf segs c1 q snap Kont : clear implicits.
