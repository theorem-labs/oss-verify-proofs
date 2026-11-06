From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib Require Import PropExec MState Mem Exec Frame Cells.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc Require Import RStep.
Import ListNotations.
Open Scope Z_scope.

Definition ASAN_K : Z := 0x7fff8000.
Definition LOWMEM_END : Z := 0x7fff8000.
Definition LOWSHADOW_END : Z := 0x8fff7000.
Definition HIGHSHADOW_BEG : Z := 0x2008fff7000.
Definition HIGHMEM_BEG : Z := 0x10007fff8000.
Definition APPMEM_END : Z := 0x800000000000.

Definition app_mem (a : Z) : Prop :=
  0 <= a < LOWMEM_END \/ HIGHMEM_BEG <= a < APPMEM_END.
Definition in_shadow (a : Z) : Prop :=
  LOWMEM_END <= a < LOWSHADOW_END \/ HIGHSHADOW_BEG <= a < HIGHMEM_BEG.
Definition shadow_addr (a : Z) : Z := a / 8 + ASAN_K.
Definition shadow_ok (a k : Z) : Prop := k = 0 \/ (a mod 8 < k /\ k <= 7).
Definition app_ivl (lo hi : Z) : Prop := forall a, lo <= a < hi -> app_mem a.

Fixpoint all_app (W : list ivl) : Prop :=
  match W with [] => True | (lo, hi) :: W' => app_ivl lo hi /\ all_app W' end.

Lemma in_shadow_range : forall a, in_shadow a -> 0 <= a /\ a + 1 <= 2^64.
Proof.
  unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG.
  intros; lia.
Qed.

Lemma app_not_shadow : forall a, app_mem a -> in_shadow a -> False.
Proof.
  unfold app_mem, in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG, APPMEM_END.
  intros; lia.
Qed.

Lemma shadow_of_app : forall a, app_mem a -> in_shadow (shadow_addr a).
Proof.
  unfold app_mem, in_shadow, shadow_addr, ASAN_K, LOWMEM_END, LOWSHADOW_END,
    HIGHSHADOW_BEG, HIGHMEM_BEG, APPMEM_END.
  intros a H. Z.div_mod_to_equations. lia.
Qed.

Lemma app_ivl_meta : forall lo hi x, app_ivl lo hi -> in_shadow x -> x < lo \/ hi <= x.
Proof.
  intros lo hi x H Hx. destruct (Z_lt_le_dec x lo); [left; lia|].
  destruct (Z_lt_le_dec x hi); [|right; lia].
  exfalso. apply (app_not_shadow x); [apply H; lia | exact Hx].
Qed.

Lemma app_ivl_sub : forall lo hi lo' hi',
  app_ivl lo hi -> lo <= lo' -> hi' <= hi -> app_ivl lo' hi'.
Proof. intros lo hi lo' hi' H H1 H2 a Ha. apply H. lia. Qed.

Lemma high_stack_app : forall lo hi,
  HIGHMEM_BEG <= lo -> hi <= APPMEM_END -> app_ivl lo hi.
Proof. intros lo hi HL HH a Ha. right. lia. Qed.

Section Img.
Context {IMG : RImg}.

Definition addr_byte (m : word -> option byte) (a : Z) : Prop :=
  app_mem a /\ exists b, mrd img_segs m (wa (shadow_addr a)) = Some b /\ shadow_ok a (bv_signed b).

Definition addressable (m : word -> option byte) (p n : Z) : Prop :=
  0 <= p /\ 0 <= n /\ p + n <= APPMEM_END /\ forall i, 0 <= i < n -> addr_byte m (p + i).

Definition end_in_app (p n : Z) : Prop := n = 0 \/ app_mem (p + n).

Definition shadow_rw (m : word -> option byte) : Prop :=
  forall a, in_shadow a -> wview img_segs m (wa a) <> None /\ exists b, mrd img_segs m (wa a) = Some b.

Definition meta_kept (m m' : word -> option byte) : Prop :=
  forall a, in_shadow a -> mrd img_segs m' (wa a) = mrd img_segs m (wa a).

Definition pf_rng (m : word -> option byte) (p n : Z) : Prop :=
  n <= 2^40 /\ addressable m p n /\ end_in_app p n /\
  (forall i, 0 <= i < n -> app_mem (p + i + 7)).

Definition musl_prefix_addressable (m : word -> option byte) : Prop :=
  pf_rng m (sym 0x1029e) 9.

Lemma addressable_app : forall m p n, addressable m p n -> app_ivl p (p + n).
Proof.
  intros m p n (_ & _ & _ & H) a Ha. destruct (H (a - p) ltac:(lia)) as [Ha' _].
  replace a with (p + (a - p)) by lia. exact Ha'.
Qed.

Lemma addressable_sub : forall m p n k n',
  addressable m p n -> 0 <= k -> 0 <= n' -> k + n' <= n -> addressable m (p + k) n'.
Proof.
  intros m p n k n' (H1 & H2 & H3 & H) Hk Hn' Hkn.
  split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. replace (p + k + i) with (p + (k + i)) by lia. apply H. lia.
Qed.

Lemma pf_rng_sub : forall m p n k n',
  pf_rng m p n -> 0 <= k -> 0 <= n' -> k + n' <= n -> pf_rng m (p + k) n'.
Proof.
  intros m p n k n' (HN & AD & EN & SEVEN) HK HN' HKN.
  split; [lia|]. split; [eapply addressable_sub; eauto|]. split.
  - destruct (Z.eq_dec n' 0) as [->|NE]; [left; reflexivity|]. right.
    destruct (Z.eq_dec (k + n') n) as [E|NEQ].
    + unfold end_in_app in EN. destruct EN as [E0|E0]; [lia|].
      replace (p + k + n') with (p + n) by lia. exact E0.
    + destruct AD as (_ & _ & _ & A).
      destruct (A (k + n') ltac:(lia)) as [AP _].
      replace (p + k + n') with (p + (k + n')) by lia. exact AP.
  - intros i HI. replace (p + k + i + 7) with (p + (k + i) + 7) by lia.
    apply SEVEN. lia.
Qed.

Lemma meta_kept_trans : forall m1 m2 m3,
  meta_kept m1 m2 -> meta_kept m2 m3 -> meta_kept m1 m3.
Proof. intros m1 m2 m3 H1 H2 a Ha. rewrite (H2 a Ha). apply H1, Ha. Qed.

Lemma addressable_kept : forall m m' p n,
  addressable m p n -> meta_kept m m' -> addressable m' p n.
Proof.
  intros m m' p n (H1 & H2 & H3 & H) MK.
  split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. destruct (H i Hi) as (Ha & b & Hb & Hk).
  split; [exact Ha|]. exists b. split; [|exact Hk].
  rewrite MK; [exact Hb|]. apply shadow_of_app. exact Ha.
Qed.

Lemma pf_rng_kept : forall m m' p n,
  pf_rng m p n -> meta_kept m m' -> pf_rng m' p n.
Proof.
  intros m m' p n (HN & AD & EN & SEVEN) MK.
  split; [exact HN|]. split; [eapply addressable_kept; eauto|]. split; assumption.
Qed.

Lemma shadow_rw_kept : forall m m',
  shadow_rw m -> meta_kept m m' -> wmono img_segs m m' -> shadow_rw m'.
Proof.
  intros m m' H MK WM a Ha. destruct (H a Ha) as [Hw (b & Hb)].
  split; [apply WM, Hw|]. exists b. rewrite MK by exact Ha. exact Hb.
Qed.

Lemma munch_meta : forall W m m', munch W m m' -> all_app W -> meta_kept m m'.
Proof.
  intros W m m' MU AW a Ha. unfold mrd. rewrite (MU (wa a)); [reflexivity|].
  destruct (in_shadow_range a Ha) as [R1 R2]. rewrite wa_unsigned by lia.
  clear MU. induction W as [|[lo hi] W IH]; cbn [outside all_app] in *; [exact I|].
  destruct AW as [A1 A2]. split; [pose proof (app_ivl_meta lo hi a A1 Ha); lia | exact (IH A2)].
Qed.

Lemma musl_prefix_kept : forall W m m',
  musl_prefix_addressable m -> munch W m m' -> all_app W -> musl_prefix_addressable m'.
Proof. intros W m m' H MU AW. eapply pf_rng_kept; [exact H|]. eapply munch_meta; eauto. Qed.

End Img.
