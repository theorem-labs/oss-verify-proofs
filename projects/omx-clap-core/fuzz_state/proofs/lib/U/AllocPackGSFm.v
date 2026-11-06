From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YK11 YK0s YK0i YM06 YP09 YM05 YK15 YM02.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YO0i YO0f YO0g YO0q YO0x YO0d YO0e YO05 YO02 YO03 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO04.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YO16 YL01 YK1j YO10 YO0s YO0u YO15 YN03 YN2b YN33.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import AllocSI AllocGS AllocFree AllocMalloc AllocRealloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import AllocMB AllocMallocMB AllocFreeMB AllocReallocMB AllocSlots.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import AllocMallocPath AllocFreePath AllocBound.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import AllocPack AllocPackRoom AllocPackFree AllocReallocOK.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import AllocPackMalloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import Contract AllocCut AllocForm.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import AllocPackGSF.
Import ListNotations.
Local Open Scope Z_scope.

(* malloc keeps GSF. GSF bounds each used meta by its own (am_maplen, am_sc, am_last) alone (gfc), so it is an
   invariant of single steps (presI GSF of YO0e): steps that keep st_metas keep it; setslot of a non-used slot keeps
   it; setm keeps it when the new meta satisfies gfc, which holds for a meta read by getm with only links, masks or
   slots changed (gf_shape), for the direct meta of class 63, for the nested group (am_maplen 0), and for the mapped
   group of alloc_group, whose am_maplen * PGSZ is snd (mmap_plan ..) rounded down to a page and whose
   am_last = fst (mmap_plan ..) - 1 (gf_plan). *)

Definition gfc (a : ameta) : Prop :=
  0 < am_maplen a -> am_sc a < 48 -> 1 <= am_last a ->
  am_maplen a * PGSZ <= page_round (class_size (am_sc a) * (am_last a + 1) + UNIT).

Lemma gf_MT s q a : GSF s -> MT s q = Some (MUsed a) -> gfc a.
Proof. intros H M. exact (H q a (usedX_intro [] s q a eq_refl M)). Qed.

Lemma gf_of_MT s : (forall q a, MT s q = Some (MUsed a) -> gfc a) -> GSF s.
Proof. intros H g am Hu. exact (H g am (proj1 (usedX_MT _ _ _ _ Hu))). Qed.

Lemma gf_metas s s' : st_metas s' = st_metas s -> GSF s -> GSF s'.
Proof. intros E H. apply gf_of_MT. intros q a M. unfold MT in M. rewrite E in M. exact (gf_MT s q a H M). Qed.

Lemma gf_upd s p x : (forall a, x = MUsed a -> gfc a) -> GSF s -> GSF (upd_meta p x s).
Proof.
  intros Hx H. apply gf_of_MT. intros q a M. rewrite MT_upd in M. destruct (sptr_eqb q p).
  - injection M as M. exact (Hx a M).
  - exact (gf_MT s q a H M).
Qed.

Lemma gf_shape a a' : am_maplen a' = am_maplen a -> am_sc a' = am_sc a -> am_last a' = am_last a -> gfc a -> gfc a'.
Proof. intros L S T H. unfold gfc in *. rewrite L, S, T. exact H. Qed.

Lemma gf_of_KR {A} (m : M A) : KR m -> presI GSF m.
Proof.
  intros HK s Hs. eapply tall_mono; [|exact (HK s)]. intros [a s'] Hk. cbn [snd] in *.
  destruct Hk as (_ & _ & _ & Mc). apply gf_of_MT. intros q a' M. destruct (Mc q a' M) as (a0 & M0 & L & S & T & _).
  exact (gf_shape a0 a' L S T (gf_MT s q a0 Hs M0)).
Qed.

Lemma gf_bind_get {B} (k : astate -> M B) : (forall s, GSF s -> presI GSF (k s)) -> presI GSF (bind get k).
Proof. intros Hk s Hs. exact (Hk s Hs s Hs). Qed.

Lemma gf_bind_getm {B} p (k : ameta -> M B) : (forall am, gfc am -> presI GSF (k am)) -> presI GSF (bind (getm p) k).
Proof.
  intros Hk s Hs. unfold getm, bind, get, ret, fail. cbn [ibind].
  destruct (mlookup (st_metas s) p) as [[| |am]|] eqn:E; cbn [ibind tall]; try exact I.
  exact (Hk am (gf_MT s p am Hs E) s Hs).
Qed.

Lemma gf_setm p a : gfc a -> presI GSF (setm p a).
Proof.
  intros Ha s Hs. change (GSF (upd_meta p (MUsed a) s)). apply gf_upd; [|exact Hs].
  intros a' E. injection E as E. subst a'. exact Ha.
Qed.

Lemma gf_setslot p x : (forall a, x <> MUsed a) -> presI GSF (setslot p x).
Proof.
  intros Hx s Hs. change (GSF (upd_meta p x s)). apply gf_upd; [|exact Hs].
  intros a E. exfalso. exact (Hx a E).
Qed.

Lemma gf_getm p : presI GSF (getm p). Proof. apply gf_of_KR, kr_getm. Qed.
Lemma gf_get_links p : presI GSF (get_links p). Proof. apply gf_of_KR, kr_get_links. Qed.
Lemma gf_set_links p pr nx : presI GSF (set_links p pr nx). Proof. apply gf_of_KR, kr_set_links. Qed.
Lemma gf_get_head h : presI GSF (get_head h). Proof. apply gf_of_KR, kr_get_head. Qed.
Lemma gf_set_head h v : presI GSF (set_head h v). Proof. apply gf_of_KR, kr_set_head. Qed.
Lemma gf_queue h m : presI GSF (queue h m). Proof. apply gf_of_KR, kr_queue. Qed.
Lemma gf_dequeue h m : presI GSF (dequeue h m). Proof. apply gf_of_KR, kr_dequeue. Qed.
Lemma gf_free_meta m : presI GSF (free_meta m). Proof. apply gf_of_KR, kr_free_meta. Qed.
Lemma gf_activate_group m : presI GSF (activate_group m). Proof. apply gf_of_KR, kr_activate_group. Qed.
Lemma gf_set_usage_of sc v : presI GSF (set_usage_of sc v). Proof. apply gf_of_KR, kr_set_usage_of. Qed.
Lemma gf_step_seq : presI GSF step_seq. Proof. apply gf_of_KR, kr_step_seq. Qed.
Lemma gf_upd_region r f : presI GSF (upd_region r f). Proof. apply gf_of_KR, kr_upd_region. Qed.

Lemma gf_dequeue_head h : presI GSF (dequeue_head h).
Proof.
  apply gf_of_KR. unfold dequeue_head. apply kr_bind; [apply kr_get_head | intros [m|]].
  - apply kr_bind; [apply kr_dequeue | intros _; apply kr_ret].
  - apply kr_ret.
Qed.

Ltac gf_steq := cbn; repeat (match goal with |- context [if ?b then _ else _] => destruct b end); cbn; reflexivity.

Ltac gf_mclose := match goal with H : GSF ?s0 |- GSF _ => apply (gf_metas s0); [gf_steq | exact H] end.

Ltac gf_setter := let s0 := fresh "s" in let H0 := fresh "H" in intros s0 H0; apply (gf_metas s0); [gf_steq | exact H0].

Ltac gf_cclose :=
  first
  [ match goal with H : gfc ?a |- gfc _ => apply (gf_shape a); [reflexivity | reflexivity | reflexivity | exact H] end
  | unfold gfc; cbn [am_maplen am_sc am_last]; intros; lia ].

Lemma gf_install_group m sc cnt aidx maplen mem sl :
  (0 < maplen -> sc < 48 -> 1 <= cnt - 1 -> maplen * PGSZ <= page_round (class_size sc * cnt + UNIT)) ->
  presI GSF (install_group m sc cnt aidx maplen mem sl).
Proof.
  intros Hc. unfold install_group. apply gf_bind_get. intros s0 _.
  apply presI_bind; [apply gf_set_usage_of | intros _]. cbv zeta.
  apply presI_bind; [apply gf_setm | intros _; apply gf_queue].
  unfold gfc. cbn [am_maplen am_sc am_last]. intros H1 H2 H3. replace (cnt - 1 + 1) with cnt by lia. exact (Hc H1 H2 H3).
Qed.

(* One step on the head of the goal, chosen by its syntax: presI_bind_get unifies with any monadic term (by eta), so
   it is applied only to a syntactic bind get. *)
Ltac gf_step :=
  lazymatch goal with
  | |- presI GSF (bind (getm _) _) => apply gf_bind_getm; intros ? ?
  | |- presI GSF (bind get _) => apply presI_bind_get; intros ? ?
  | |- presI GSF (bind _ _) => apply presI_bind; [ | intros ? ]
  | |- presI GSF (setm _ _) => apply gf_setm; solve [gf_cclose]
  | |- presI GSF (setslot _ _) => apply gf_setslot; intros ? ?; discriminate
  | |- presI GSF (install_group _ _ _ _ _ _ _) => apply gf_install_group
  | |- presI GSF (ret _) => apply presI_ret
  | |- presI GSF get => apply presI_get
  | |- presI GSF (ask _) => apply presI_ask
  | |- presI GSF (askz _) => apply presI_askz
  | |- presI GSF (fail _) => apply presI_fail
  | |- presI GSF (massert _ _) => apply presI_massert
  | |- presI GSF (mcheck _ _) => apply presI_mcheck
  | |- presI GSF (modify _) => apply presI_modify; solve [gf_setter]
  | |- presI GSF (match ?x with _ => _ end) => destruct x
  | |- presI GSF _ => solve [eauto 3]
  | |- GSF _ => solve [gf_mclose]
  | |- tall _ (IRet _) => cbn [tall snd fst]
  | |- tall _ (match ?x with _ => _ end ?s) => destruct x
  | |- tall _ (put _ _) => apply tall_put; solve [gf_mclose]
  | |- tall _ (bind (put _) _ _) => apply tall_bind_put
  | |- tall _ (bind get _ _) => apply tall_bind_get
  | |- tall _ (bind (modify _) _ _) => apply tall_bind_modify
  | |- tall _ (?m ?s) => apply tall_of_presI; [ | solve [assumption | gf_mclose] ]
  end.

Ltac gfgo := repeat first [ progress (cbv beta zeta) | assumption | gf_step ].

Lemma gf_plan s sc req c u :
  0 < snd (mmap_plan s sc req c u) / 4096 -> sc < 48 -> 1 <= fst (mmap_plan s sc req c u) - 1 ->
  snd (mmap_plan s sc req c u) / 4096 * PGSZ <= page_round (class_size sc * fst (mmap_plan s sc req c u) + UNIT).
Proof.
  intros _ _ H1.
  assert (E : snd (mmap_plan s sc req c u) = page_round (class_size sc * fst (mmap_plan s sc req c u) + UNIT)).
  { revert H1. unfold mmap_plan. cbv zeta.
    repeat match goal with |- context [if ?b then _ else _] => destruct b end; cbn [fst snd]; intros; first [reflexivity | lia]. }
  rewrite <- E. pose proof (Z.mul_div_le (snd (mmap_plan s sc req c u)) 4096 ltac:(lia)). unfold PGSZ. lia.
Qed.

Lemma gf_account_bounce sc : presI GSF (account_bounce sc). Proof. unfold account_bounce. gfgo. Qed.
Lemma gf_decay_bounces sc : presI GSF (decay_bounces sc). Proof. unfold decay_bounces. gfgo. Qed.
Lemma gf_new_region k len : presI GSF (new_region k len). Proof. unfold new_region. gfgo. Qed.
Lemma gf_area_from_brk : presI GSF area_from_brk.
Proof. unfold area_from_brk. pose proof gf_new_region. pose proof gf_upd_region. gfgo. Qed.
Lemma gf_area_from_mmap : presI GSF area_from_mmap.
Proof. unfold area_from_mmap. pose proof gf_new_region. pose proof gf_upd_region. gfgo. Qed.
Lemma gf_open_area b : presI GSF (open_area b).
Proof. unfold open_area. pose proof gf_new_region. pose proof gf_upd_region. gfgo. Qed.

Lemma gf_alloc_meta : presI GSF alloc_meta.
Proof.
  unfold alloc_meta. pose proof gf_dequeue_head. pose proof gf_area_from_brk. pose proof gf_area_from_mmap.
  pose proof gf_open_area. gfgo.
Qed.

Lemma gf_try_avail sc : presI GSF (try_avail sc).
Proof.
  unfold try_avail. pose proof gf_get_head. pose proof gf_set_head. pose proof gf_dequeue.
  pose proof gf_activate_group. pose proof gf_decay_bounces. gfgo.
Qed.

Lemma gf_enframe g idx n ctr k : presI GSF (enframe g idx n ctr k).
Proof. unfold enframe. gfgo. Qed.

Lemma gf_alloc_slot_group fuel :
  (forall sc req, presI GSF (alloc_slot fuel sc req)) /\ (forall sc req, presI GSF (alloc_group fuel sc req)).
Proof.
  induction fuel as [|fuel [IHs IHg]]; (split; intros sc req; [cbn [alloc_slot] | cbn [alloc_group]]).
  - apply presI_fail.
  - apply presI_fail.
  - pose proof gf_try_avail. gfgo.
  - pose proof gf_alloc_meta. pose proof gf_account_bounce. pose proof gf_step_seq. pose proof gf_free_meta.
    pose proof gf_new_region. pose proof gf_get_head. pose proof gf_enframe. gfgo.
    all: first [solve [intros; lia] | apply gf_plan].
Qed.

Lemma gf_malloc n : presI GSF (malloc n).
Proof.
  unfold malloc. pose proof gf_alloc_meta. pose proof gf_step_seq. pose proof gf_new_region. pose proof gf_upd_region.
  pose proof gf_enframe. pose proof gf_get_head. pose proof (proj1 (gf_alloc_slot_group NEST_FUEL)). gfgo.
Qed.

Theorem malloc_GSF : forall s n tr r s', WF s -> GSF s -> 0 <= n -> yields (malloc n s) tr (r, s') -> GSF s'.
Proof. intros s n tr r s' _ HG _ Y. exact (tall_yields _ _ tr (r, s') (gf_malloc n s HG) Y). Qed.
