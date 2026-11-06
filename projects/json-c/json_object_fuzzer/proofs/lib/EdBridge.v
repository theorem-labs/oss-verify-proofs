From Stdlib Require Import ZArith List Bool Lia Setoid.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Import EdAlloc.
Import ListNotations.
Open Scope bv_scope.
Open Scope sys_scope.

(* ------------------------------------------------------------------------- *)
(* Calls, arm guards and outcome sets.                                        *)

Definition enomem_sysno (no : Z) : Prop := no = 216%Z \/ no = 222%Z \/ no = 226%Z.

Definition ed_mmap_call (i : SyscallInput) (addr len prot flags fd off : word) : Prop :=
  bv_unsigned (in_sysno i) = 222%Z
  /\ in_arg i 0 = addr /\ in_arg i 1 = len /\ in_arg i 2 = prot
  /\ in_arg i 3 = flags /\ in_arg i 4 = fd /\ in_arg i 5 = off.

Definition ed_mprotect_call (i : SyscallInput) (addr len prot : word) : Prop :=
  bv_unsigned (in_sysno i) = 226%Z
  /\ in_arg i 0 = addr /\ in_arg i 1 = len /\ in_arg i 2 = prot.

Definition ed_refused (m : Model) (eff : SyscallEffect) (m' : Model) (evs : list event)
    : Prop :=
  eff = mkEffect (errno_ret ENOMEM) [] [] /\ m' = m /\ evs = [].

Definition ed_destroyed (m : Model) (addr len : word)
    (eff : SyscallEffect) (m' : Model) (evs : list event) : Prop :=
  let n := Z_to_bv 64 (page_round_up_Z (bv_unsigned len)) in
  eff = mkEffectU (errno_ret ENOMEM) [] [] [(addr, n)] [] []
  /\ m' = with_mmap_destroyed addr n (mmap_fixed_destroyed_next (m_vmmaps m) addr n) m
  /\ evs = [].

Definition ed_refused_or_destroyed (m : Model) (addr len : word)
    (eff : SyscallEffect) (m' : Model) (evs : list event) : Prop :=
  ed_refused m eff m' evs \/ ed_destroyed m addr len eff m' evs.

Definition ed_eexist (m : Model) (eff : SyscallEffect) (m' : Model) (evs : list event)
    : Prop :=
  eff = mkEffect (errno_ret EEXIST) [] [] /\ m' = m /\ evs = [].

(* anonymous rw, kernel-placed *)
Definition ed_rw_arm (prot flags len off : word) : Prop :=
  mmap_off_aligned_b off = true /\ mmap_anon_b flags = true /\ w_is0 len = false
  /\ mmap_modeled_b prot flags off = true.

Definition ed_rw_grant (flags len : word) (m : Model)
    (eff : SyscallEffect) (m' : Model) (evs : list event) : Prop :=
  let h := m_vmmaps m in
  let nZ := page_round_up_Z (bv_unsigned len) in
  let n := Z_to_bv 64 nZ in
  exists a, ((bv_unsigned a mod page_size = 0)%Z
             /\ (0 < bv_unsigned a)%Z
             /\ (bv_unsigned a + nZ <= alloc_top h)%Z
             /\ region_free (vm_reserved h ++ vm_maps h) a n = true
             /\ mmap_noreserve_backed_ok flags m nZ = true)
    /\ eff = mkEffect a [] [(a, n)]
    /\ m' = with_mmap_backing flags a n
              (with_vmmaps
                 (mkVmMapsFull (vm_reserved h) ((a, n) :: vm_maps h)
                    (vm_noaccess h) (vm_start_brk h) (vm_brk h) (vm_limit h)
                    (vm_mmap_base h) (vm_init_sp h)) m)
    /\ evs = [].

(* anonymous PROT_NONE reserve, kernel-placed *)
Definition ed_reserve_arm (prot flags len off : word) : Prop :=
  mmap_off_aligned_b off = true /\ mmap_anon_b flags = true /\ w_is0 len = false
  /\ mmap_modeled_b prot flags off = false /\ mmap_noaccess_b prot flags off = true.

Definition ed_reserve_grant (flags len : word) (m : Model)
    (eff : SyscallEffect) (m' : Model) (evs : list event) : Prop :=
  let h := m_vmmaps m in
  let nZ := page_round_up_Z (bv_unsigned len) in
  let n := Z_to_bv 64 nZ in
  exists a, ((bv_unsigned a mod page_size = 0)%Z
             /\ (0 < bv_unsigned a)%Z
             /\ (bv_unsigned a + nZ <= alloc_top h)%Z
             /\ region_free (vm_reserved h ++ vm_maps h) a n = true)
    /\ eff = mkEffectU a [] [] [(a, n)] [] []
    /\ m' = with_mmap_backing flags a n
              (with_vmmaps
                 (mkVmMapsFull (vm_reserved h) ((a, n) :: vm_maps h)
                    ((a, n) :: vm_noaccess h) (vm_start_brk h)
                    (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) m)
    /\ evs = [].

(* mprotect PROT_READ|PROT_WRITE over a reserved (noaccess) range *)
Definition ed_expose_arm (m : Model) (addr len prot : word) : Prop :=
  mprotect_grows_conflict_b prot = false
  /\ (bv_unsigned addr mod page_size =? 0)%Z = true
  /\ w_is0 len = false
  /\ (two_pow_64 <=? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z = false
  /\ mprotect_modeled_b prot = true
  /\ (map_contains (vm_noaccess (m_vmmaps m)) addr
        (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))
      && map_contains (vm_maps (m_vmmaps m)) addr
        (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))) = true.

Definition ed_expose_grant (m : Model) (addr len : word)
    (eff : SyscallEffect) (m' : Model) (evs : list event) : Prop :=
  let n := Z_to_bv 64 (page_round_up_Z (bv_unsigned len)) in
  mprotect_budget_ok m addr n = true
  /\ eff = mkEffect (Z_to_bv 64 0) [] [(addr, n)]
  /\ m' = mprotect_model_next m addr n
  /\ evs = [].

(* the argument gate the MAP_FIXED and MAP_FIXED_NOREPLACE arms share *)
Definition ed_fixed_gate (m : Model) (addr len : word) : Prop :=
  (two_pow_64 <=? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z = false
  /\ (bv_unsigned addr + page_round_up_Z (bv_unsigned len) <=? alloc_top (m_vmmaps m))%Z = true
  /\ (bv_unsigned addr mod page_size =? 0)%Z = true
  /\ (0 <? bv_unsigned addr)%Z = true.

(* the ledger tests the fixed arms split on *)
Definition ed_fixed_contained (m : Model) (addr len : word) : bool :=
  region_free (vm_reserved (m_vmmaps m)) addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))
  && map_contains (vm_maps (m_vmmaps m)) addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))).

Definition ed_fixed_free (m : Model) (addr len : word) : bool :=
  region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) addr
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))).

Definition ed_fixed_resfree (m : Model) (addr len : word) : bool :=
  region_free (vm_reserved (m_vmmaps m)) addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))).

Definition ed_fna_arm (m : Model) (addr len prot flags off : word) : Prop :=
  mmap_off_aligned_b off = true /\ mmap_anon_b flags = true /\ w_is0 len = false
  /\ mmap_modeled_b prot flags off = false /\ mmap_noaccess_b prot flags off = false
  /\ mmap_fixed_noaccess_b prot flags off = true
  /\ ed_fixed_gate m addr len.

Definition ed_frw_arm (m : Model) (addr len prot flags off : word) : Prop :=
  mmap_off_aligned_b off = true /\ mmap_anon_b flags = true /\ w_is0 len = false
  /\ mmap_modeled_b prot flags off = false /\ mmap_noaccess_b prot flags off = false
  /\ mmap_fixed_noaccess_b prot flags off = false /\ mmap_fixed_rw_b prot flags off = true
  /\ ed_fixed_gate m addr len.

Definition ed_nrna_arm (m : Model) (addr len prot flags off : word) : Prop :=
  mmap_off_aligned_b off = true /\ mmap_anon_b flags = true /\ w_is0 len = false
  /\ mmap_modeled_b prot flags off = false /\ mmap_noaccess_b prot flags off = false
  /\ mmap_fixed_noaccess_b prot flags off = false /\ mmap_fixed_rw_b prot flags off = false
  /\ mmap_noreplace_noaccess_b prot flags off = true
  /\ ed_fixed_gate m addr len.

Definition ed_nrrw_arm (m : Model) (addr len prot flags off : word) : Prop :=
  mmap_off_aligned_b off = true /\ mmap_anon_b flags = true /\ w_is0 len = false
  /\ mmap_modeled_b prot flags off = false /\ mmap_noaccess_b prot flags off = false
  /\ mmap_fixed_noaccess_b prot flags off = false /\ mmap_fixed_rw_b prot flags off = false
  /\ mmap_noreplace_noaccess_b prot flags off = false
  /\ mmap_noreplace_rw_b prot flags off = true
  /\ ed_fixed_gate m addr len.

Definition ed_fna_contained_ok (flags : word) (m : Model) (addr len : word)
    (eff : SyscallEffect) (m' : Model) (evs : list event) : Prop :=
  let h := m_vmmaps m in
  let n := Z_to_bv 64 (page_round_up_Z (bv_unsigned len)) in
  eff = mkEffectU addr [] [] [(addr, n)] [] []
  /\ m' = with_mmap_replacement flags addr n
            (with_vmmaps (mkVmMapsFull (vm_reserved h) (vm_maps h)
               ((addr, n) :: maps_subtract (vm_noaccess h)
                               (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
               (vm_start_brk h) (vm_brk h) (vm_limit h)
               (vm_mmap_base h) (vm_init_sp h)) m)
  /\ evs = [].

Definition ed_na_fresh_ok (flags : word) (m : Model) (addr len : word)
    (eff : SyscallEffect) (m' : Model) (evs : list event) : Prop :=
  let h := m_vmmaps m in
  let n := Z_to_bv 64 (page_round_up_Z (bv_unsigned len)) in
  eff = mkEffectU addr [] [] [(addr, n)] [] []
  /\ m' = with_mmap_backing flags addr n
            (with_vmmaps (mkVmMapsFull (vm_reserved h) ((addr, n) :: vm_maps h)
               ((addr, n) :: vm_noaccess h) (vm_start_brk h)
               (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) m)
  /\ evs = [].

Definition ed_fna_span_ok (flags : word) (m : Model) (addr len : word)
    (eff : SyscallEffect) (m' : Model) (evs : list event) : Prop :=
  let h := m_vmmaps m in
  let n := Z_to_bv 64 (page_round_up_Z (bv_unsigned len)) in
  eff = mkEffectU addr [] [] [(addr, n)] [] []
  /\ m' = with_mmap_replacement flags addr n
            (with_vmmaps (mmap_fixed_noaccess_span_next h addr n) m)
  /\ evs = [].

Definition ed_frw_contained_ok (flags : word) (m : Model) (addr len : word)
    (eff : SyscallEffect) (m' : Model) (evs : list event) : Prop :=
  let h := m_vmmaps m in
  let n := Z_to_bv 64 (page_round_up_Z (bv_unsigned len)) in
  mmap_fixed_rw_budget_ok flags m addr n = true
  /\ eff = mkEffect addr [] [(addr, n)]
  /\ m' = with_mmap_replacement flags addr n (with_vmmaps (mmap_fixed_rw_next h addr n) m)
  /\ evs = [].

Definition ed_rw_fresh_ok (flags : word) (m : Model) (addr len : word)
    (eff : SyscallEffect) (m' : Model) (evs : list event) : Prop :=
  let h := m_vmmaps m in
  let nZ := page_round_up_Z (bv_unsigned len) in
  let n := Z_to_bv 64 nZ in
  mmap_noreserve_backed_ok flags m nZ = true
  /\ eff = mkEffect addr [] [(addr, n)]
  /\ m' = with_mmap_backing flags addr n
            (with_vmmaps (mkVmMapsFull (vm_reserved h) ((addr, n) :: vm_maps h)
               (vm_noaccess h) (vm_start_brk h) (vm_brk h) (vm_limit h)
               (vm_mmap_base h) (vm_init_sp h)) m)
  /\ evs = [].

Definition ed_frw_span_ok (flags : word) (m : Model) (addr len : word)
    (eff : SyscallEffect) (m' : Model) (evs : list event) : Prop :=
  let h := m_vmmaps m in
  let n := Z_to_bv 64 (page_round_up_Z (bv_unsigned len)) in
  mmap_fixed_rw_span_budget_ok flags m addr n = true
  /\ eff = mkEffect addr [] [(addr, n)]
  /\ m' = with_mmap_replacement flags addr n
            (with_vmmaps (mmap_fixed_rw_span_next h addr n) m)
  /\ evs = [].

(* ------------------------------------------------------------------------- *)
(* Tactics.                                                                    *)

Lemma ed_Ok_inj {A} : forall (x x' : A) (m m' : Model) (e e' : list event),
  Ok x m e = Ok x' m' e' -> x = x' /\ m = m' /\ e = e'.
Proof. intros x x' m m' e e' H. injection H. auto. Qed.

Ltac ed_inv :=
  repeat first
    [ progress subst
    | match goal with
      | H : exists _, _ |- _ => destruct H
      | H : _ /\ _ |- _ => destruct H
      | H : _ \/ _ |- _ => destruct H
      | H : Ok _ _ _ = Ok _ _ _ |- _ => apply ed_Ok_inj in H; destruct H as (? & ? & ?)
      | H : Ok _ _ _ = Unmodeled |- _ => discriminate H
      | H : Unmodeled = Ok _ _ _ |- _ => discriminate H
      | H : False |- _ => contradiction
      | H : true = false |- _ => discriminate H
      | H : false = true |- _ => discriminate H
      end
    | progress cbv beta iota zeta in * ].

Ltac ed_solve :=
  repeat match goal with
         | |- @ex unit _ => exists tt
         | |- exists _, _ => eexists
         | |- _ /\ _ => split
         end;
  first [ eassumption | reflexivity | left; reflexivity ].

Ltac ed_pick := first [ solve [ed_solve] | left; ed_pick | right; ed_pick ].

Ltac ed_close :=
  repeat match goal with
         | Hin : In _ mmap_errnos |- _ => destruct Hin as [<- | []]
         | Hin : In _ mprotect_errnos |- _ => destruct Hin as [<- | []]
         | Hin : In _ mremap_errnos |- _ => destruct Hin as [<- | []]
         end;
  ed_pick.

Ltac ed_reduce :=
  repeat first
    [ match goal with
      | H : ?b = true |- context [?b] => rewrite H
      | H : ?b = false |- context [?b] => rewrite H
      end
    | rewrite bind_get_model
    | rewrite Bool.andb_false_r
    | rewrite Bool.andb_true_r
    | progress cbn [negb andb]
    | progress cbv beta iota zeta ].

Ltac ed_unfold :=
  unfold ed_refused_or_destroyed, ed_refused, ed_destroyed, ed_eexist,
    ed_rw_grant, ed_reserve_grant, ed_expose_grant,
    ed_fna_contained_ok, ed_na_fresh_ok, ed_fna_span_ok,
    ed_frw_contained_ok, ed_rw_fresh_ok, ed_frw_span_ok,
    alt, bind, errno_from, choose, err_ret, ret_only, pure, get_model, modify;
  cbv beta iota zeta.

Ltac ed_spec_tac := ed_reduce; ed_unfold; split; intros ?H; ed_inv; ed_close.

(* ------------------------------------------------------------------------- *)
(* The filter on the ENOMEM-only allocation arms (216, 222, 226).             *)

Lemma ed_refusal_b : forall i m r,
  enomem_sysno (bv_unsigned (in_sysno i)) ->
  refusal_b i m r = bv_eqb r (errno_ret ENOMEM).
Proof.
  intros i m r [E|[E|E]]; unfold refusal_b; rewrite E; cbv zeta;
    (transitivity (bv_eqb r (errno_ret ENOMEM) || false);
     [reflexivity | apply orb_false_r]).
Qed.

Lemma ed_family_off : forall i,
  enomem_sysno (bv_unsigned (in_sysno i)) ->
  injected_family_off (alloc_only_cfg false) i = true.
Proof. intros i [E|[E|E]]; unfold injected_family_off; rewrite E; reflexivity. Qed.

Lemma ed_bv_eqb_false : forall (a b : word), a <> b -> bv_eqb a b = false.
Proof.
  intros a b H. destruct (bv_eqb a b) eqn:E; [|reflexivity].
  apply bv_eqb_eq in E. contradiction.
Qed.

Lemma ed_bv_eqb_refl : forall (a : word), bv_eqb a a = true.
Proof. intros a. apply bv_eqb_eq. reflexivity. Qed.

Lemma ed_spurious_intro : forall i m eff eff2 m2 evs2,
  enomem_sysno (bv_unsigned (in_sysno i)) ->
  eff_ret eff = errno_ret ENOMEM ->
  syscall_spec i m (Ok eff2 m2 evs2) ->
  eff_ret eff2 <> errno_ret ENOMEM ->
  spurious_refusal_cfg (alloc_only_cfg false) i m eff.
Proof.
  intros i m eff eff2 m2 evs2 Hno Hr Hs Hne.
  split; [exact (ed_family_off i Hno)|].
  split; [rewrite (ed_refusal_b i m _ Hno), Hr; apply ed_bv_eqb_refl|].
  exists eff2, m2, evs2. split; [exact Hs|].
  rewrite (ed_refusal_b i m _ Hno). apply ed_bv_eqb_false. exact Hne.
Qed.

Lemma ed_not_spurious_ret : forall i m eff,
  enomem_sysno (bv_unsigned (in_sysno i)) ->
  eff_ret eff <> errno_ret ENOMEM ->
  ~ spurious_refusal_cfg (alloc_only_cfg false) i m eff.
Proof.
  intros i m eff Hno Hne. apply spurious_refusal_not_refusal.
  rewrite (ed_refusal_b i m _ Hno). apply ed_bv_eqb_false. exact Hne.
Qed.

Lemma ed_not_spurious_all : forall i m eff,
  enomem_sysno (bv_unsigned (in_sysno i)) ->
  (forall eff2 m2 evs2, syscall_spec i m (Ok eff2 m2 evs2) -> eff_ret eff2 = errno_ret ENOMEM) ->
  ~ spurious_refusal_cfg (alloc_only_cfg false) i m eff.
Proof.
  intros i m eff Hno Hall (_ & _ & (eff2 & m2 & evs2 & Hs & Hr)).
  rewrite (ed_refusal_b i m _ Hno), (Hall _ _ _ Hs), ed_bv_eqb_refl in Hr.
  discriminate Hr.
Qed.

(** For 216/222/226 the filter keeps an outcome iff it is not -ENOMEM or no
    outcome of the same call is anything but -ENOMEM. *)
Lemma ed_not_spurious_iff : forall i m eff,
  enomem_sysno (bv_unsigned (in_sysno i)) ->
  ~ spurious_refusal_cfg (alloc_only_cfg false) i m eff
  <-> (eff_ret eff = errno_ret ENOMEM ->
       forall eff2 m2 evs2, syscall_spec i m (Ok eff2 m2 evs2) ->
       eff_ret eff2 = errno_ret ENOMEM).
Proof.
  intros i m eff Hno. split.
  - intros Hns Hr eff2 m2 evs2 Hs.
    destruct (bv_eqb (eff_ret eff2) (errno_ret ENOMEM)) eqn:B;
      [apply bv_eqb_eq in B; exact B|].
    exfalso. apply Hns. apply (ed_spurious_intro i m eff eff2 m2 evs2 Hno Hr Hs).
    intros E. rewrite E, ed_bv_eqb_refl in B. discriminate B.
  - intros H. destruct (bv_eqb (eff_ret eff) (errno_ret ENOMEM)) eqn:B.
    + apply bv_eqb_eq in B. apply ed_not_spurious_all; [exact Hno|]. exact (H B).
    + apply ed_not_spurious_ret; [exact Hno|]. intros E.
      rewrite E, ed_bv_eqb_refl in B. discriminate B.
Qed.

(* ------------------------------------------------------------------------- *)
(* One arm, abstractly: its outcomes are refusals [Rf] (all -ENOMEM) or       *)
(* grants [G] (none -ENOMEM), and [R] is false exactly when a grant exists.   *)

Definition arm_shape (i : SyscallInput) (m : Model) (R : bool)
    (Rf G : SyscallEffect -> Model -> list event -> Prop) : Prop :=
  enomem_sysno (bv_unsigned (in_sysno i))
  /\ (forall eff m' evs, syscall_spec i m (Ok eff m' evs) <-> Rf eff m' evs \/ G eff m' evs)
  /\ (forall eff m' evs, Rf eff m' evs -> eff_ret eff = errno_ret ENOMEM)
  /\ (forall eff m' evs, G eff m' evs -> eff_ret eff <> errno_ret ENOMEM)
  /\ (R = false <-> exists eff m' evs, G eff m' evs).

Lemma arm_inversion : forall i m R Rf G, arm_shape i m R Rf G ->
  forall eff m' evs,
  syscall_spec i m (Ok eff m' evs) ->
  ~ spurious_refusal_cfg (alloc_only_cfg false) i m eff ->
  G eff m' evs \/ (Rf eff m' evs /\ R = true).
Proof.
  intros i m R Rf G (Hno & Hiff & HRf & HG & HR) eff m' evs Hs Hns.
  apply Hiff in Hs. destruct Hs as [Hr|Hg]; [|left; exact Hg].
  right. split; [exact Hr|].
  case_eq R; intros ER; [reflexivity|exfalso].
  destruct (proj1 HR ER) as (eff2 & m2 & evs2 & Hg2).
  apply Hns. apply (ed_spurious_intro i m eff eff2 m2 evs2 Hno (HRf _ _ _ Hr)).
  - apply Hiff. right. exact Hg2.
  - exact (HG _ _ _ Hg2).
Qed.

Lemma arm_inversion_false : forall i m Rf G, arm_shape i m false Rf G ->
  forall eff m' evs,
  syscall_spec i m (Ok eff m' evs) ->
  ~ spurious_refusal_cfg (alloc_only_cfg false) i m eff ->
  G eff m' evs.
Proof.
  intros i m Rf G Hsh eff m' evs Hs Hns.
  destruct (arm_inversion i m false Rf G Hsh eff m' evs Hs Hns) as [Hg|(_ & E)];
    [exact Hg | discriminate E].
Qed.

Lemma arm_forced : forall i m R Rf G, arm_shape i m R Rf G -> R = true ->
  forall eff m' evs, Rf eff m' evs ->
  syscall_spec i m (Ok eff m' evs) /\ ~ spurious_refusal_cfg (alloc_only_cfg false) i m eff.
Proof.
  intros i m R Rf G (Hno & Hiff & HRf & HG & HR) ER eff m' evs Hr.
  split; [apply Hiff; left; exact Hr|].
  apply ed_not_spurious_all; [exact Hno|].
  intros eff2 m2 evs2 Hs. apply Hiff in Hs.
  destruct Hs as [Hr2|Hg2]; [exact (HRf _ _ _ Hr2)|].
  exfalso. assert (EF : R = false) by (apply HR; exists eff2, m2, evs2; exact Hg2).
  rewrite ER in EF. discriminate EF.
Qed.

Lemma arm_grant : forall i m R Rf G, arm_shape i m R Rf G ->
  forall eff m' evs, G eff m' evs ->
  syscall_spec i m (Ok eff m' evs) /\ ~ spurious_refusal_cfg (alloc_only_cfg false) i m eff.
Proof.
  intros i m R Rf G (Hno & Hiff & HRf & HG & HR) eff m' evs Hg.
  split; [apply Hiff; right; exact Hg|].
  apply ed_not_spurious_ret; [exact Hno | exact (HG _ _ _ Hg)].
Qed.

Lemma arm_refused_spurious : forall i m R Rf G, arm_shape i m R Rf G -> R = false ->
  forall eff m' evs, Rf eff m' evs ->
  syscall_spec i m (Ok eff m' evs) /\ spurious_refusal_cfg (alloc_only_cfg false) i m eff.
Proof.
  intros i m R Rf G (Hno & Hiff & HRf & HG & HR) ER eff m' evs Hr.
  split; [apply Hiff; left; exact Hr|].
  destruct (proj1 HR ER) as (eff2 & m2 & evs2 & Hg2).
  apply (ed_spurious_intro i m eff eff2 m2 evs2 Hno (HRf _ _ _ Hr)).
  - apply Hiff. right. exact Hg2.
  - exact (HG _ _ _ Hg2).
Qed.

Lemma arm_exact : forall i m R Rf G, arm_shape i m R Rf G ->
  forall eff m' evs,
  (syscall_spec i m (Ok eff m' evs) /\ ~ spurious_refusal_cfg (alloc_only_cfg false) i m eff)
  <-> G eff m' evs \/ (Rf eff m' evs /\ R = true).
Proof.
  intros i m R Rf G Hsh eff m' evs. split.
  - intros (Hs & Hns). exact (arm_inversion i m R Rf G Hsh eff m' evs Hs Hns).
  - intros [Hg | (Hr & ER)].
    + exact (arm_grant i m R Rf G Hsh eff m' evs Hg).
    + exact (arm_forced i m R Rf G Hsh ER eff m' evs Hr).
Qed.

(* ------------------------------------------------------------------------- *)
(* Shared facts.                                                               *)

Lemma ed_mmap_call_spec : forall i addr len prot flags fd off m o,
  ed_mmap_call i addr len prot flags fd off ->
  syscall_spec i m o <-> mmap_spec addr len prot flags fd off i m o.
Proof.
  intros i addr len prot flags fd off m o (E & H0 & H1 & H2 & H3 & H4 & H5). subst.
  unfold syscall_spec, dispatch. rewrite E. reflexivity.
Qed.

Lemma ed_mmap_call_sysno : forall i addr len prot flags fd off,
  ed_mmap_call i addr len prot flags fd off -> enomem_sysno (bv_unsigned (in_sysno i)).
Proof. intros i addr len prot flags fd off (E & _). right. left. exact E. Qed.

Lemma ed_mprotect_call_spec : forall i addr len prot m o,
  ed_mprotect_call i addr len prot ->
  syscall_spec i m o <-> mprotect_spec addr len prot i m o.
Proof.
  intros i addr len prot m o (E & H0 & H1 & H2). subst.
  unfold syscall_spec, dispatch. rewrite E. reflexivity.
Qed.

Lemma ed_mprotect_call_sysno : forall i addr len prot,
  ed_mprotect_call i addr len prot -> enomem_sysno (bv_unsigned (in_sysno i)).
Proof. intros i addr len prot (E & _). right. right. exact E. Qed.

Lemma ed_nZ_nonneg : forall len : word, (0 <= page_round_up_Z (bv_unsigned len))%Z.
Proof.
  intros len. pose proof (bv_unsigned_in_range 64 len) as [H0 _].
  unfold page_round_up_Z, page_size.
  apply Z.mul_nonneg_nonneg; [apply Z.div_pos; lia | lia].
Qed.

Lemma ed_enomem_unsigned : bv_unsigned (errno_ret ENOMEM) = 18446744073709551604%Z.
Proof. vm_compute. reflexivity. Qed.

Lemma ed_below_top_ne_enomem : forall (a : word) (h : VmMaps) (nZ : Z),
  (0 <= nZ)%Z -> (bv_unsigned a + nZ <= alloc_top h)%Z -> a <> errno_ret ENOMEM.
Proof.
  intros a h nZ Hn Hle Heq. pose proof (alloc_top_room h) as Hr.
  assert (E2 : two_pow_64 = 18446744073709551616%Z) by reflexivity.
  rewrite Heq, ed_enomem_unsigned in Hle. rewrite E2 in Hr.
  unfold stack_max_size in Hr. lia.
Qed.

Lemma ed_gate_ne_enomem : forall m addr len,
  ed_fixed_gate m addr len -> addr <> errno_ret ENOMEM.
Proof.
  intros m addr len (_ & Htop & _ & _). apply Z.leb_le in Htop.
  exact (ed_below_top_ne_enomem addr (m_vmmaps m) _ (ed_nZ_nonneg len) Htop).
Qed.

Lemma ed_zero_ne_enomem : Z_to_bv 64 0 <> errno_ret ENOMEM.
Proof. intros H. apply (f_equal bv_unsigned) in H. vm_compute in H. discriminate H. Qed.

Lemma ed_eexist_ne_enomem : errno_ret EEXIST <> errno_ret ENOMEM.
Proof. intros H. apply (f_equal bv_unsigned) in H. vm_compute in H. discriminate H. Qed.

Lemma ed_refused_ret : forall m eff m' evs,
  ed_refused m eff m' evs -> eff_ret eff = errno_ret ENOMEM.
Proof. intros m eff m' evs (-> & _ & _). reflexivity. Qed.

Lemma ed_refused_or_destroyed_ret : forall m addr len eff m' evs,
  ed_refused_or_destroyed m addr len eff m' evs -> eff_ret eff = errno_ret ENOMEM.
Proof. intros m addr len eff m' evs [(-> & _ & _) | (-> & _ & _)]; reflexivity. Qed.

Lemma ed_refused_intro : forall m, ed_refused m (mkEffect (errno_ret ENOMEM) [] []) m [].
Proof. intros m. split; [reflexivity | split; reflexivity]. Qed.

(* ========================================================================= *)
(* (1) anonymous rw, kernel-placed: refusable = mmap_grant_refusable.        *)

Lemma ed_rw_spec : forall addr len prot flags fd off i m eff m' evs,
  ed_rw_arm prot flags len off ->
  mmap_spec addr len prot flags fd off i m (Ok eff m' evs)
  <-> ed_refused m eff m' evs \/ ed_rw_grant flags len m eff m' evs.
Proof.
  intros addr len prot flags fd off i m eff m' evs (Hoff & Hanon & Hlen & Hmod).
  unfold mmap_spec. ed_spec_tac.
Qed.

Lemma ed_rw_shape : forall i addr len prot flags fd off m,
  ed_mmap_call i addr len prot flags fd off ->
  ed_rw_arm prot flags len off ->
  arm_shape i m (mmap_grant_refusable flags m (page_round_up_Z (bv_unsigned len)))
    (ed_refused m) (ed_rw_grant flags len m).
Proof.
  intros i addr len prot flags fd off m Hc Harm.
  split; [exact (ed_mmap_call_sysno _ _ _ _ _ _ _ Hc)|].
  split.
  { intros eff m' evs. rewrite (ed_mmap_call_spec _ _ _ _ _ _ _ _ _ Hc).
    apply ed_rw_spec. exact Harm. }
  split; [exact (ed_refused_ret m)|].
  split.
  { intros eff m' evs HG. unfold ed_rw_grant in HG. cbv zeta in HG.
    destruct HG as (a & (Hal & Hpos & Htop & Hfree & Hb) & -> & _).
    exact (ed_below_top_ne_enomem a (m_vmmaps m) _ (ed_nZ_nonneg len) Htop). }
  unfold mmap_grant_refusable. split.
  - intros H. apply orb_false_iff in H as [H1 H2].
    apply negb_false_iff in H1. apply negb_false_iff in H2.
    apply vm_gap_available_iff in H2 as (a & Hal & Hpos & Htop & Hfree).
    unfold ed_rw_grant. cbv zeta. do 3 eexists. exists a. ed_solve.
  - intros (eff & m' & evs & HG). unfold ed_rw_grant in HG. cbv zeta in HG.
    destruct HG as (a & (Hal & Hpos & Htop & Hfree & Hb) & _).
    rewrite Hb. cbn [negb orb].
    rewrite (proj2 (vm_gap_available_iff _ _)
               (ex_intro _ a (conj Hal (conj Hpos (conj Htop Hfree))))).
    reflexivity.
Qed.

(** (a) a kept outcome is a grant, or the -ENOMEM with the refusal forced. *)
Lemma ed_rw_inversion : forall i addr len prot flags fd off m eff m' evs,
  ed_mmap_call i addr len prot flags fd off ->
  ed_rw_arm prot flags len off ->
  syscall_spec i m (Ok eff m' evs) ->
  ~ spurious_refusal_cfg (alloc_only_cfg false) i m eff ->
  ed_rw_grant flags len m eff m' evs
  \/ (ed_refused m eff m' evs
      /\ mmap_grant_refusable flags m (page_round_up_Z (bv_unsigned len)) = true).
Proof.
  intros i addr len prot flags fd off m eff m' evs Hc Ha.
  exact (arm_inversion _ _ _ _ _ (ed_rw_shape i addr len prot flags fd off m Hc Ha) eff m' evs).
Qed.

(** (b) a forced refusal is an outcome, and the filter keeps it. *)
Lemma ed_rw_forced : forall i addr len prot flags fd off m,
  ed_mmap_call i addr len prot flags fd off ->
  ed_rw_arm prot flags len off ->
  mmap_grant_refusable flags m (page_round_up_Z (bv_unsigned len)) = true ->
  syscall_spec i m (Ok (mkEffect (errno_ret ENOMEM) [] []) m [])
  /\ ~ spurious_refusal_cfg (alloc_only_cfg false) i m (mkEffect (errno_ret ENOMEM) [] []).
Proof.
  intros i addr len prot flags fd off m Hc Ha HR.
  exact (arm_forced _ _ _ _ _ (ed_rw_shape i addr len prot flags fd off m Hc Ha) HR
           _ _ _ (ed_refused_intro m)).
Qed.

(** (c) every grant is an outcome, and the filter keeps it. *)
Lemma ed_rw_grant_nonspurious : forall i addr len prot flags fd off m eff m' evs,
  ed_mmap_call i addr len prot flags fd off ->
  ed_rw_arm prot flags len off ->
  ed_rw_grant flags len m eff m' evs ->
  syscall_spec i m (Ok eff m' evs)
  /\ ~ spurious_refusal_cfg (alloc_only_cfg false) i m eff.
Proof.
  intros i addr len prot flags fd off m eff m' evs Hc Ha.
  exact (arm_grant _ _ _ _ _ (ed_rw_shape i addr len prot flags fd off m Hc Ha) eff m' evs).
Qed.

Lemma ed_rw_exact : forall i addr len prot flags fd off m eff m' evs,
  ed_mmap_call i addr len prot flags fd off ->
  ed_rw_arm prot flags len off ->
  (syscall_spec i m (Ok eff m' evs) /\ ~ spurious_refusal_cfg (alloc_only_cfg false) i m eff)
  <-> ed_rw_grant flags len m eff m' evs
      \/ (ed_refused m eff m' evs
          /\ mmap_grant_refusable flags m (page_round_up_Z (bv_unsigned len)) = true).
Proof.
  intros i addr len prot flags fd off m eff m' evs Hc Ha.
  exact (arm_exact _ _ _ _ _ (ed_rw_shape i addr len prot flags fd off m Hc Ha) eff m' evs).
Qed.

(* ========================================================================= *)
(* (2) anonymous PROT_NONE reserve: refusable = mmap_reserve_refusable.     *)

Lemma ed_reserve_spec : forall addr len prot flags fd off i m eff m' evs,
  ed_reserve_arm prot flags len off ->
  mmap_spec addr len prot flags fd off i m (Ok eff m' evs)
  <-> ed_refused m eff m' evs \/ ed_reserve_grant flags len m eff m' evs.
Proof.
  intros addr len prot flags fd off i m eff m' evs (Hoff & Hanon & Hlen & Hmod & Hna).
  unfold mmap_spec. ed_spec_tac.
Qed.

Lemma ed_reserve_shape : forall i addr len prot flags fd off m,
  ed_mmap_call i addr len prot flags fd off ->
  ed_reserve_arm prot flags len off ->
  arm_shape i m (mmap_reserve_refusable m (page_round_up_Z (bv_unsigned len)))
    (ed_refused m) (ed_reserve_grant flags len m).
Proof.
  intros i addr len prot flags fd off m Hc Harm.
  split; [exact (ed_mmap_call_sysno _ _ _ _ _ _ _ Hc)|].
  split.
  { intros eff m' evs. rewrite (ed_mmap_call_spec _ _ _ _ _ _ _ _ _ Hc).
    apply ed_reserve_spec. exact Harm. }
  split; [exact (ed_refused_ret m)|].
  split.
  { intros eff m' evs HG. unfold ed_reserve_grant in HG. cbv zeta in HG.
    destruct HG as (a & (Hal & Hpos & Htop & Hfree) & -> & _).
    exact (ed_below_top_ne_enomem a (m_vmmaps m) _ (ed_nZ_nonneg len) Htop). }
  unfold mmap_reserve_refusable. split.
  - intros H. apply negb_false_iff in H.
    apply vm_gap_available_iff in H as (a & Hal & Hpos & Htop & Hfree).
    unfold ed_reserve_grant. cbv zeta. do 3 eexists. exists a. ed_solve.
  - intros (eff & m' & evs & HG). unfold ed_reserve_grant in HG. cbv zeta in HG.
    destruct HG as (a & (Hal & Hpos & Htop & Hfree) & _).
    rewrite (proj2 (vm_gap_available_iff _ _)
               (ex_intro _ a (conj Hal (conj Hpos (conj Htop Hfree))))).
    reflexivity.
Qed.

Lemma ed_reserve_inversion : forall i addr len prot flags fd off m eff m' evs,
  ed_mmap_call i addr len prot flags fd off ->
  ed_reserve_arm prot flags len off ->
  syscall_spec i m (Ok eff m' evs) ->
  ~ spurious_refusal_cfg (alloc_only_cfg false) i m eff ->
  ed_reserve_grant flags len m eff m' evs
  \/ (ed_refused m eff m' evs
      /\ mmap_reserve_refusable m (page_round_up_Z (bv_unsigned len)) = true).
Proof.
  intros i addr len prot flags fd off m eff m' evs Hc Ha.
  exact (arm_inversion _ _ _ _ _ (ed_reserve_shape i addr len prot flags fd off m Hc Ha)
           eff m' evs).
Qed.

Lemma ed_reserve_forced : forall i addr len prot flags fd off m,
  ed_mmap_call i addr len prot flags fd off ->
  ed_reserve_arm prot flags len off ->
  mmap_reserve_refusable m (page_round_up_Z (bv_unsigned len)) = true ->
  syscall_spec i m (Ok (mkEffect (errno_ret ENOMEM) [] []) m [])
  /\ ~ spurious_refusal_cfg (alloc_only_cfg false) i m (mkEffect (errno_ret ENOMEM) [] []).
Proof.
  intros i addr len prot flags fd off m Hc Ha HR.
  exact (arm_forced _ _ _ _ _ (ed_reserve_shape i addr len prot flags fd off m Hc Ha) HR
           _ _ _ (ed_refused_intro m)).
Qed.

Lemma ed_reserve_grant_nonspurious : forall i addr len prot flags fd off m eff m' evs,
  ed_mmap_call i addr len prot flags fd off ->
  ed_reserve_arm prot flags len off ->
  ed_reserve_grant flags len m eff m' evs ->
  syscall_spec i m (Ok eff m' evs)
  /\ ~ spurious_refusal_cfg (alloc_only_cfg false) i m eff.
Proof.
  intros i addr len prot flags fd off m eff m' evs Hc Ha.
  exact (arm_grant _ _ _ _ _ (ed_reserve_shape i addr len prot flags fd off m Hc Ha)
           eff m' evs).
Qed.

Lemma ed_reserve_exact : forall i addr len prot flags fd off m eff m' evs,
  ed_mmap_call i addr len prot flags fd off ->
  ed_reserve_arm prot flags len off ->
  (syscall_spec i m (Ok eff m' evs) /\ ~ spurious_refusal_cfg (alloc_only_cfg false) i m eff)
  <-> ed_reserve_grant flags len m eff m' evs
      \/ (ed_refused m eff m' evs
          /\ mmap_reserve_refusable m (page_round_up_Z (bv_unsigned len)) = true).
Proof.
  intros i addr len prot flags fd off m eff m' evs Hc Ha.
  exact (arm_exact _ _ _ _ _ (ed_reserve_shape i addr len prot flags fd off m Hc Ha)
           eff m' evs).
Qed.

(* ========================================================================= *)
(* (3) mprotect noaccess -> rw: refusable = mprotect_refusable.             *)

Lemma ed_expose_spec : forall addr len prot i m eff m' evs,
  ed_expose_arm m addr len prot ->
  mprotect_spec addr len prot i m (Ok eff m' evs)
  <-> ed_refused m eff m' evs \/ ed_expose_grant m addr len eff m' evs.
Proof.
  intros addr len prot i m eff m' evs (Hgc & Hal & Hlen & Hwrap & Hmod & Hmc).
  unfold mprotect_spec. ed_spec_tac.
Qed.

Lemma ed_expose_shape : forall i addr len prot m,
  ed_mprotect_call i addr len prot ->
  ed_expose_arm m addr len prot ->
  arm_shape i m (mprotect_refusable m addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))))
    (ed_refused m) (ed_expose_grant m addr len).
Proof.
  intros i addr len prot m Hc Harm.
  split; [exact (ed_mprotect_call_sysno _ _ _ _ Hc)|].
  split.
  { intros eff m' evs. rewrite (ed_mprotect_call_spec _ _ _ _ _ _ Hc).
    apply ed_expose_spec. exact Harm. }
  split; [exact (ed_refused_ret m)|].
  split.
  { intros eff m' evs HG. unfold ed_expose_grant in HG. cbv zeta in HG.
    destruct HG as (_ & -> & _). exact ed_zero_ne_enomem. }
  unfold mprotect_refusable. split.
  - intros H. apply negb_false_iff in H.
    unfold ed_expose_grant. cbv zeta. do 3 eexists. ed_solve.
  - intros (eff & m' & evs & HG). unfold ed_expose_grant in HG. cbv zeta in HG.
    destruct HG as (Hb & _). rewrite Hb. reflexivity.
Qed.

Lemma ed_expose_inversion : forall i addr len prot m eff m' evs,
  ed_mprotect_call i addr len prot ->
  ed_expose_arm m addr len prot ->
  syscall_spec i m (Ok eff m' evs) ->
  ~ spurious_refusal_cfg (alloc_only_cfg false) i m eff ->
  ed_expose_grant m addr len eff m' evs
  \/ (ed_refused m eff m' evs
      /\ mprotect_refusable m addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) = true).
Proof.
  intros i addr len prot m eff m' evs Hc Ha.
  exact (arm_inversion _ _ _ _ _ (ed_expose_shape i addr len prot m Hc Ha) eff m' evs).
Qed.

Lemma ed_expose_forced : forall i addr len prot m,
  ed_mprotect_call i addr len prot ->
  ed_expose_arm m addr len prot ->
  mprotect_refusable m addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) = true ->
  syscall_spec i m (Ok (mkEffect (errno_ret ENOMEM) [] []) m [])
  /\ ~ spurious_refusal_cfg (alloc_only_cfg false) i m (mkEffect (errno_ret ENOMEM) [] []).
Proof.
  intros i addr len prot m Hc Ha HR.
  exact (arm_forced _ _ _ _ _ (ed_expose_shape i addr len prot m Hc Ha) HR
           _ _ _ (ed_refused_intro m)).
Qed.

Lemma ed_expose_grant_nonspurious : forall i addr len prot m eff m' evs,
  ed_mprotect_call i addr len prot ->
  ed_expose_arm m addr len prot ->
  ed_expose_grant m addr len eff m' evs ->
  syscall_spec i m (Ok eff m' evs)
  /\ ~ spurious_refusal_cfg (alloc_only_cfg false) i m eff.
Proof.
  intros i addr len prot m eff m' evs Hc Ha.
  exact (arm_grant _ _ _ _ _ (ed_expose_shape i addr len prot m Hc Ha) eff m' evs).
Qed.

Lemma ed_expose_exact : forall i addr len prot m eff m' evs,
  ed_mprotect_call i addr len prot ->
  ed_expose_arm m addr len prot ->
  (syscall_spec i m (Ok eff m' evs) /\ ~ spurious_refusal_cfg (alloc_only_cfg false) i m eff)
  <-> ed_expose_grant m addr len eff m' evs
      \/ (ed_refused m eff m' evs
          /\ mprotect_refusable m addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) = true).
Proof.
  intros i addr len prot m eff m' evs Hc Ha.
  exact (arm_exact _ _ _ _ _ (ed_expose_shape i addr len prot m Hc Ha) eff m' evs).
Qed.


(* ========================================================================= *)
(* (4) MAP_FIXED and MAP_FIXED_NOREPLACE: PROT_NONE arms are never refusable *)
(* (their success is unconditional); rw arms are refusable per sub-case;     *)
(* NOREPLACE over an occupied range keeps only -EEXIST.                       *)

Definition ed_destroyed_eff (addr len : word) : SyscallEffect :=
  mkEffectU (errno_ret ENOMEM) [] [] [(addr, (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))))] [] [].

Definition ed_destroyed_model (m : Model) (addr len : word) : Model :=
  with_mmap_destroyed addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))
    (mmap_fixed_destroyed_next (m_vmmaps m) addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))) m.

Lemma ed_destroyed_intro : forall m addr len,
  ed_destroyed m addr len (ed_destroyed_eff addr len) (ed_destroyed_model m addr len) [].
Proof. intros m addr len. split; [reflexivity | split; reflexivity]. Qed.

Lemma ed_fna_arm_gate : forall m addr len prot flags off,
  ed_fna_arm m addr len prot flags off -> ed_fixed_gate m addr len.
Proof. intros m addr len prot flags off H. destruct H as (_ & _ & _ & _ & _ & _ & Hg). exact Hg. Qed.

Lemma ed_frw_arm_gate : forall m addr len prot flags off,
  ed_frw_arm m addr len prot flags off -> ed_fixed_gate m addr len.
Proof. intros m addr len prot flags off H. destruct H as (_ & _ & _ & _ & _ & _ & _ & Hg). exact Hg. Qed.

Lemma ed_nrna_arm_gate : forall m addr len prot flags off,
  ed_nrna_arm m addr len prot flags off -> ed_fixed_gate m addr len.
Proof. intros m addr len prot flags off H. destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & Hg). exact Hg. Qed.

Lemma ed_nrrw_arm_gate : forall m addr len prot flags off,
  ed_nrrw_arm m addr len prot flags off -> ed_fixed_gate m addr len.
Proof. intros m addr len prot flags off H. destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hg). exact Hg. Qed.

(* ---- fna_contained ---- *)

Lemma ed_fna_contained_spec : forall addr len prot flags fd off i m eff m' evs,
  ed_fna_arm m addr len prot flags off ->
  ed_fixed_contained m addr len = true ->
  mmap_spec addr len prot flags fd off i m (Ok eff m' evs)
  <-> ed_refused_or_destroyed m addr len eff m' evs \/ ed_fna_contained_ok flags m addr len eff m' evs.
Proof.
  intros addr len prot flags fd off i m eff m' evs Harm H0.
  unfold ed_fna_arm, ed_fixed_gate in Harm. destruct Harm as (Hoff & Hanon & Hlen & Hmod & Hna & Hfx & Hw & Htop & Hal & Hpos).
  unfold ed_fixed_contained, ed_fixed_free, ed_fixed_resfree in *.
  unfold mmap_spec. ed_spec_tac.
Qed.

Lemma ed_fna_contained_shape : forall i addr len prot flags fd off m,
  ed_mmap_call i addr len prot flags fd off ->
  ed_fna_arm m addr len prot flags off ->
  ed_fixed_contained m addr len = true ->
  arm_shape i m (false) (ed_refused_or_destroyed m addr len) (ed_fna_contained_ok flags m addr len).
Proof.
  intros i addr len prot flags fd off m Hc Harm H0.
  split; [exact (ed_mmap_call_sysno _ _ _ _ _ _ _ Hc)|].
  split.
  { intros eff m' evs. rewrite (ed_mmap_call_spec _ _ _ _ _ _ _ _ _ Hc).
    apply ed_fna_contained_spec; assumption. }
  split; [exact (ed_refused_or_destroyed_ret m addr len)|].
  split.
  { intros eff m' evs HG. unfold ed_fna_contained_ok in HG. cbv zeta in HG. ed_inv.
    exact (ed_gate_ne_enomem m addr len (ed_fna_arm_gate _ _ _ _ _ _ Harm)). }

  split; [intros _; do 3 eexists; unfold ed_fna_contained_ok; cbv zeta; ed_solve | intros _; reflexivity].
Qed.

Lemma ed_fna_contained_inversion : forall i addr len prot flags fd off m eff m' evs,
  ed_mmap_call i addr len prot flags fd off ->
  ed_fna_arm m addr len prot flags off ->
  ed_fixed_contained m addr len = true ->
  syscall_spec i m (Ok eff m' evs) ->
  ~ spurious_refusal_cfg (alloc_only_cfg false) i m eff ->
  ed_fna_contained_ok flags m addr len eff m' evs.
Proof. intros i addr len prot flags fd off m eff m' evs Hc Ha H0. exact (arm_inversion_false _ _ _ _ (ed_fna_contained_shape i addr len prot flags fd off m Hc Ha H0) eff m' evs). Qed.

Lemma ed_fna_contained_refusal_spurious : forall i addr len prot flags fd off m eff m' evs,
  ed_mmap_call i addr len prot flags fd off ->
  ed_fna_arm m addr len prot flags off ->
  ed_fixed_contained m addr len = true ->
  ed_refused_or_destroyed m addr len eff m' evs ->
  syscall_spec i m (Ok eff m' evs) /\ spurious_refusal_cfg (alloc_only_cfg false) i m eff.
Proof. intros i addr len prot flags fd off m eff m' evs Hc Ha H0. exact (arm_refused_spurious _ _ _ _ _ (ed_fna_contained_shape i addr len prot flags fd off m Hc Ha H0) eq_refl eff m' evs). Qed.

Lemma ed_fna_contained_exact : forall i addr len prot flags fd off m eff m' evs,
  ed_mmap_call i addr len prot flags fd off ->
  ed_fna_arm m addr len prot flags off ->
  ed_fixed_contained m addr len = true ->
  (syscall_spec i m (Ok eff m' evs) /\ ~ spurious_refusal_cfg (alloc_only_cfg false) i m eff)
  <-> ed_fna_contained_ok flags m addr len eff m' evs.
Proof.
  intros i addr len prot flags fd off m eff m' evs Hc Ha H0. rewrite (arm_exact _ _ _ _ _ (ed_fna_contained_shape i addr len prot flags fd off m Hc Ha H0) eff m' evs).
  split; [intros [Hg | (_ & E)]; [exact Hg | discriminate E] | intros Hg; left; exact Hg].
Qed.

Lemma ed_fna_contained_grant_nonspurious : forall i addr len prot flags fd off m eff m' evs,
  ed_mmap_call i addr len prot flags fd off ->
  ed_fna_arm m addr len prot flags off ->
  ed_fixed_contained m addr len = true ->
  ed_fna_contained_ok flags m addr len eff m' evs ->
  syscall_spec i m (Ok eff m' evs) /\ ~ spurious_refusal_cfg (alloc_only_cfg false) i m eff.
Proof. intros i addr len prot flags fd off m eff m' evs Hc Ha H0. exact (arm_grant _ _ _ _ _ (ed_fna_contained_shape i addr len prot flags fd off m Hc Ha H0) eff m' evs). Qed.

(* ---- fna_free ---- *)

Lemma ed_fna_free_spec : forall addr len prot flags fd off i m eff m' evs,
  ed_fna_arm m addr len prot flags off ->
  ed_fixed_contained m addr len = false ->
  ed_fixed_free m addr len = true ->
  mmap_spec addr len prot flags fd off i m (Ok eff m' evs)
  <-> ed_refused m eff m' evs \/ ed_na_fresh_ok flags m addr len eff m' evs.
Proof.
  intros addr len prot flags fd off i m eff m' evs Harm H0 H1.
  unfold ed_fna_arm, ed_fixed_gate in Harm. destruct Harm as (Hoff & Hanon & Hlen & Hmod & Hna & Hfx & Hw & Htop & Hal & Hpos).
  unfold ed_fixed_contained, ed_fixed_free, ed_fixed_resfree in *.
  unfold mmap_spec. ed_spec_tac.
Qed.

Lemma ed_fna_free_shape : forall i addr len prot flags fd off m,
  ed_mmap_call i addr len prot flags fd off ->
  ed_fna_arm m addr len prot flags off ->
  ed_fixed_contained m addr len = false ->
  ed_fixed_free m addr len = true ->
  arm_shape i m (false) (ed_refused m) (ed_na_fresh_ok flags m addr len).
Proof.
  intros i addr len prot flags fd off m Hc Harm H0 H1.
  split; [exact (ed_mmap_call_sysno _ _ _ _ _ _ _ Hc)|].
  split.
  { intros eff m' evs. rewrite (ed_mmap_call_spec _ _ _ _ _ _ _ _ _ Hc).
    apply ed_fna_free_spec; assumption. }
  split; [exact (ed_refused_ret m)|].
  split.
  { intros eff m' evs HG. unfold ed_na_fresh_ok in HG. cbv zeta in HG. ed_inv.
    exact (ed_gate_ne_enomem m addr len (ed_fna_arm_gate _ _ _ _ _ _ Harm)). }

  split; [intros _; do 3 eexists; unfold ed_na_fresh_ok; cbv zeta; ed_solve | intros _; reflexivity].
Qed.

Lemma ed_fna_free_inversion : forall i addr len prot flags fd off m eff m' evs,
  ed_mmap_call i addr len prot flags fd off ->
  ed_fna_arm m addr len prot flags off ->
  ed_fixed_contained m addr len = false ->
  ed_fixed_free m addr len = true ->
  syscall_spec i m (Ok eff m' evs) ->
  ~ spurious_refusal_cfg (alloc_only_cfg false) i m eff ->
  ed_na_fresh_ok flags m addr len eff m' evs.
Proof. intros i addr len prot flags fd off m eff m' evs Hc Ha H0 H1. exact (arm_inversion_false _ _ _ _ (ed_fna_free_shape i addr len prot flags fd off m Hc Ha H0 H1) eff m' evs). Qed.

Lemma ed_fna_free_refusal_spurious : forall i addr len prot flags fd off m eff m' evs,
  ed_mmap_call i addr len prot flags fd off ->
  ed_fna_arm m addr len prot flags off ->
  ed_fixed_contained m addr len = false ->
  ed_fixed_free m addr len = true ->
  ed_refused m eff m' evs ->
  syscall_spec i m (Ok eff m' evs) /\ spurious_refusal_cfg (alloc_only_cfg false) i m eff.
Proof. intros i addr len prot flags fd off m eff m' evs Hc Ha H0 H1. exact (arm_refused_spurious _ _ _ _ _ (ed_fna_free_shape i addr len prot flags fd off m Hc Ha H0 H1) eq_refl eff m' evs). Qed.

Lemma ed_fna_free_exact : forall i addr len prot flags fd off m eff m' evs,
  ed_mmap_call i addr len prot flags fd off ->
  ed_fna_arm m addr len prot flags off ->
  ed_fixed_contained m addr len = false ->
  ed_fixed_free m addr len = true ->
  (syscall_spec i m (Ok eff m' evs) /\ ~ spurious_refusal_cfg (alloc_only_cfg false) i m eff)
  <-> ed_na_fresh_ok flags m addr len eff m' evs.
Proof.
  intros i addr len prot flags fd off m eff m' evs Hc Ha H0 H1. rewrite (arm_exact _ _ _ _ _ (ed_fna_free_shape i addr len prot flags fd off m Hc Ha H0 H1) eff m' evs).
  split; [intros [Hg | (_ & E)]; [exact Hg | discriminate E] | intros Hg; left; exact Hg].
Qed.

Lemma ed_fna_free_grant_nonspurious : forall i addr len prot flags fd off m eff m' evs,
  ed_mmap_call i addr len prot flags fd off ->
  ed_fna_arm m addr len prot flags off ->
  ed_fixed_contained m addr len = false ->
  ed_fixed_free m addr len = true ->
  ed_na_fresh_ok flags m addr len eff m' evs ->
  syscall_spec i m (Ok eff m' evs) /\ ~ spurious_refusal_cfg (alloc_only_cfg false) i m eff.
Proof. intros i addr len prot flags fd off m eff m' evs Hc Ha H0 H1. exact (arm_grant _ _ _ _ _ (ed_fna_free_shape i addr len prot flags fd off m Hc Ha H0 H1) eff m' evs). Qed.

(* ---- fna_span ---- *)

Lemma ed_fna_span_spec : forall addr len prot flags fd off i m eff m' evs,
  ed_fna_arm m addr len prot flags off ->
  ed_fixed_contained m addr len = false ->
  ed_fixed_free m addr len = false ->
  ed_fixed_resfree m addr len = true ->
  mmap_spec addr len prot flags fd off i m (Ok eff m' evs)
  <-> ed_refused_or_destroyed m addr len eff m' evs \/ ed_fna_span_ok flags m addr len eff m' evs.
Proof.
  intros addr len prot flags fd off i m eff m' evs Harm H0 H1 H2.
  unfold ed_fna_arm, ed_fixed_gate in Harm. destruct Harm as (Hoff & Hanon & Hlen & Hmod & Hna & Hfx & Hw & Htop & Hal & Hpos).
  unfold ed_fixed_contained, ed_fixed_free, ed_fixed_resfree in *.
  rewrite H2 in H0. cbn [andb] in H0.
  unfold mmap_spec. ed_spec_tac.
Qed.

Lemma ed_fna_span_shape : forall i addr len prot flags fd off m,
  ed_mmap_call i addr len prot flags fd off ->
  ed_fna_arm m addr len prot flags off ->
  ed_fixed_contained m addr len = false ->
  ed_fixed_free m addr len = false ->
  ed_fixed_resfree m addr len = true ->
  arm_shape i m (false) (ed_refused_or_destroyed m addr len) (ed_fna_span_ok flags m addr len).
Proof.
  intros i addr len prot flags fd off m Hc Harm H0 H1 H2.
  split; [exact (ed_mmap_call_sysno _ _ _ _ _ _ _ Hc)|].
  split.
  { intros eff m' evs. rewrite (ed_mmap_call_spec _ _ _ _ _ _ _ _ _ Hc).
    apply ed_fna_span_spec; assumption. }
  split; [exact (ed_refused_or_destroyed_ret m addr len)|].
  split.
  { intros eff m' evs HG. unfold ed_fna_span_ok in HG. cbv zeta in HG. ed_inv.
    exact (ed_gate_ne_enomem m addr len (ed_fna_arm_gate _ _ _ _ _ _ Harm)). }

  split; [intros _; do 3 eexists; unfold ed_fna_span_ok; cbv zeta; ed_solve | intros _; reflexivity].
Qed.

Lemma ed_fna_span_inversion : forall i addr len prot flags fd off m eff m' evs,
  ed_mmap_call i addr len prot flags fd off ->
  ed_fna_arm m addr len prot flags off ->
  ed_fixed_contained m addr len = false ->
  ed_fixed_free m addr len = false ->
  ed_fixed_resfree m addr len = true ->
  syscall_spec i m (Ok eff m' evs) ->
  ~ spurious_refusal_cfg (alloc_only_cfg false) i m eff ->
  ed_fna_span_ok flags m addr len eff m' evs.
Proof. intros i addr len prot flags fd off m eff m' evs Hc Ha H0 H1 H2. exact (arm_inversion_false _ _ _ _ (ed_fna_span_shape i addr len prot flags fd off m Hc Ha H0 H1 H2) eff m' evs). Qed.

Lemma ed_fna_span_refusal_spurious : forall i addr len prot flags fd off m eff m' evs,
  ed_mmap_call i addr len prot flags fd off ->
  ed_fna_arm m addr len prot flags off ->
  ed_fixed_contained m addr len = false ->
  ed_fixed_free m addr len = false ->
  ed_fixed_resfree m addr len = true ->
  ed_refused_or_destroyed m addr len eff m' evs ->
  syscall_spec i m (Ok eff m' evs) /\ spurious_refusal_cfg (alloc_only_cfg false) i m eff.
Proof. intros i addr len prot flags fd off m eff m' evs Hc Ha H0 H1 H2. exact (arm_refused_spurious _ _ _ _ _ (ed_fna_span_shape i addr len prot flags fd off m Hc Ha H0 H1 H2) eq_refl eff m' evs). Qed.

Lemma ed_fna_span_exact : forall i addr len prot flags fd off m eff m' evs,
  ed_mmap_call i addr len prot flags fd off ->
  ed_fna_arm m addr len prot flags off ->
  ed_fixed_contained m addr len = false ->
  ed_fixed_free m addr len = false ->
  ed_fixed_resfree m addr len = true ->
  (syscall_spec i m (Ok eff m' evs) /\ ~ spurious_refusal_cfg (alloc_only_cfg false) i m eff)
  <-> ed_fna_span_ok flags m addr len eff m' evs.
Proof.
  intros i addr len prot flags fd off m eff m' evs Hc Ha H0 H1 H2. rewrite (arm_exact _ _ _ _ _ (ed_fna_span_shape i addr len prot flags fd off m Hc Ha H0 H1 H2) eff m' evs).
  split; [intros [Hg | (_ & E)]; [exact Hg | discriminate E] | intros Hg; left; exact Hg].
Qed.

Lemma ed_fna_span_grant_nonspurious : forall i addr len prot flags fd off m eff m' evs,
  ed_mmap_call i addr len prot flags fd off ->
  ed_fna_arm m addr len prot flags off ->
  ed_fixed_contained m addr len = false ->
  ed_fixed_free m addr len = false ->
  ed_fixed_resfree m addr len = true ->
  ed_fna_span_ok flags m addr len eff m' evs ->
  syscall_spec i m (Ok eff m' evs) /\ ~ spurious_refusal_cfg (alloc_only_cfg false) i m eff.
Proof. intros i addr len prot flags fd off m eff m' evs Hc Ha H0 H1 H2. exact (arm_grant _ _ _ _ _ (ed_fna_span_shape i addr len prot flags fd off m Hc Ha H0 H1 H2) eff m' evs). Qed.

(* ---- frw_contained ---- *)

Lemma ed_frw_contained_spec : forall addr len prot flags fd off i m eff m' evs,
  ed_frw_arm m addr len prot flags off ->
  ed_fixed_contained m addr len = true ->
  mmap_spec addr len prot flags fd off i m (Ok eff m' evs)
  <-> ed_refused_or_destroyed m addr len eff m' evs \/ ed_frw_contained_ok flags m addr len eff m' evs.
Proof.
  intros addr len prot flags fd off i m eff m' evs Harm H0.
  unfold ed_frw_arm, ed_fixed_gate in Harm. destruct Harm as (Hoff & Hanon & Hlen & Hmod & Hna & Hfx & Hrw & Hw & Htop & Hal & Hpos).
  unfold ed_fixed_contained, ed_fixed_free, ed_fixed_resfree in *.
  unfold mmap_spec. ed_spec_tac.
Qed.

Lemma ed_frw_contained_shape : forall i addr len prot flags fd off m,
  ed_mmap_call i addr len prot flags fd off ->
  ed_frw_arm m addr len prot flags off ->
  ed_fixed_contained m addr len = true ->
  arm_shape i m (mmap_fixed_commit_refusable flags m addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))) (ed_refused_or_destroyed m addr len) (ed_frw_contained_ok flags m addr len).
Proof.
  intros i addr len prot flags fd off m Hc Harm H0.
  split; [exact (ed_mmap_call_sysno _ _ _ _ _ _ _ Hc)|].
  split.
  { intros eff m' evs. rewrite (ed_mmap_call_spec _ _ _ _ _ _ _ _ _ Hc).
    apply ed_frw_contained_spec; assumption. }
  split; [exact (ed_refused_or_destroyed_ret m addr len)|].
  split.
  { intros eff m' evs HG. unfold ed_frw_contained_ok in HG. cbv zeta in HG. ed_inv.
    exact (ed_gate_ne_enomem m addr len (ed_frw_arm_gate _ _ _ _ _ _ Harm)). }

  unfold mmap_fixed_commit_refusable. split.
  - intros HR. apply negb_false_iff in HR. do 3 eexists. unfold ed_frw_contained_ok. cbv zeta. ed_solve.
  - intros (eff & m' & evs & HG). unfold ed_frw_contained_ok in HG. cbv zeta in HG.
    destruct HG as (Hb & _). rewrite Hb. reflexivity.
Qed.

Lemma ed_frw_contained_inversion : forall i addr len prot flags fd off m eff m' evs,
  ed_mmap_call i addr len prot flags fd off ->
  ed_frw_arm m addr len prot flags off ->
  ed_fixed_contained m addr len = true ->
  syscall_spec i m (Ok eff m' evs) ->
  ~ spurious_refusal_cfg (alloc_only_cfg false) i m eff ->
  ed_frw_contained_ok flags m addr len eff m' evs \/ (ed_refused_or_destroyed m addr len eff m' evs /\ mmap_fixed_commit_refusable flags m addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) = true).
Proof. intros i addr len prot flags fd off m eff m' evs Hc Ha H0. exact (arm_inversion _ _ _ _ _ (ed_frw_contained_shape i addr len prot flags fd off m Hc Ha H0) eff m' evs). Qed.

Lemma ed_frw_contained_forced : forall i addr len prot flags fd off m,
  ed_mmap_call i addr len prot flags fd off ->
  ed_frw_arm m addr len prot flags off ->
  ed_fixed_contained m addr len = true ->
  mmap_fixed_commit_refusable flags m addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) = true ->
  syscall_spec i m (Ok (mkEffect (errno_ret ENOMEM) [] []) m [])
  /\ ~ spurious_refusal_cfg (alloc_only_cfg false) i m (mkEffect (errno_ret ENOMEM) [] []).
Proof.
  intros i addr len prot flags fd off m Hc Ha H0 HR.
  exact (arm_forced _ _ _ _ _ (ed_frw_contained_shape i addr len prot flags fd off m Hc Ha H0) HR _ _ _ (or_introl (ed_refused_intro m))).
Qed.

Lemma ed_frw_contained_exact : forall i addr len prot flags fd off m eff m' evs,
  ed_mmap_call i addr len prot flags fd off ->
  ed_frw_arm m addr len prot flags off ->
  ed_fixed_contained m addr len = true ->
  (syscall_spec i m (Ok eff m' evs) /\ ~ spurious_refusal_cfg (alloc_only_cfg false) i m eff)
  <-> ed_frw_contained_ok flags m addr len eff m' evs \/ (ed_refused_or_destroyed m addr len eff m' evs /\ mmap_fixed_commit_refusable flags m addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) = true).
Proof. intros i addr len prot flags fd off m eff m' evs Hc Ha H0. exact (arm_exact _ _ _ _ _ (ed_frw_contained_shape i addr len prot flags fd off m Hc Ha H0) eff m' evs). Qed.

Lemma ed_frw_contained_grant_nonspurious : forall i addr len prot flags fd off m eff m' evs,
  ed_mmap_call i addr len prot flags fd off ->
  ed_frw_arm m addr len prot flags off ->
  ed_fixed_contained m addr len = true ->
  ed_frw_contained_ok flags m addr len eff m' evs ->
  syscall_spec i m (Ok eff m' evs) /\ ~ spurious_refusal_cfg (alloc_only_cfg false) i m eff.
Proof. intros i addr len prot flags fd off m eff m' evs Hc Ha H0. exact (arm_grant _ _ _ _ _ (ed_frw_contained_shape i addr len prot flags fd off m Hc Ha H0) eff m' evs). Qed.

Lemma ed_frw_contained_inversion_budget : forall i addr len prot flags fd off m eff m' evs,
  ed_mmap_call i addr len prot flags fd off ->
  ed_frw_arm m addr len prot flags off ->
  ed_fixed_contained m addr len = true ->
  mmap_fixed_rw_budget_ok flags m addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) = true ->
  syscall_spec i m (Ok eff m' evs) ->
  ~ spurious_refusal_cfg (alloc_only_cfg false) i m eff ->
  ed_frw_contained_ok flags m addr len eff m' evs \/ (ed_refused m eff m' evs /\ mmap_fixed_commit_refusable flags m addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) = true).
Proof.
  intros i addr len prot flags fd off m eff m' evs Hc Ha H0 Hb Hs Hns.
  assert (ER : mmap_fixed_commit_refusable flags m addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) = false) by (unfold mmap_fixed_commit_refusable; rewrite Hb; reflexivity).
  destruct (arm_inversion _ _ _ _ _ (ed_frw_contained_shape i addr len prot flags fd off m Hc Ha H0) eff m' evs Hs Hns) as [Hg | (_ & E)];
    [left; exact Hg | rewrite ER in E; discriminate E].
Qed.

Lemma ed_frw_contained_destroyed_spurious : forall i addr len prot flags fd off m,
  ed_mmap_call i addr len prot flags fd off ->
  ed_frw_arm m addr len prot flags off ->
  ed_fixed_contained m addr len = true ->
  mmap_fixed_rw_budget_ok flags m addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) = true ->
  syscall_spec i m (Ok (ed_destroyed_eff addr len) (ed_destroyed_model m addr len) [])
  /\ spurious_refusal_cfg (alloc_only_cfg false) i m (ed_destroyed_eff addr len).
Proof.
  intros i addr len prot flags fd off m Hc Ha H0 Hb.
  assert (ER : mmap_fixed_commit_refusable flags m addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) = false) by (unfold mmap_fixed_commit_refusable; rewrite Hb; reflexivity).
  exact (arm_refused_spurious _ _ _ _ _ (ed_frw_contained_shape i addr len prot flags fd off m Hc Ha H0) ER _ _ _ (or_intror (ed_destroyed_intro m addr len))).
Qed.

Lemma ed_frw_contained_destroyed_forced : forall i addr len prot flags fd off m,
  ed_mmap_call i addr len prot flags fd off ->
  ed_frw_arm m addr len prot flags off ->
  ed_fixed_contained m addr len = true ->
  mmap_fixed_commit_refusable flags m addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) = true ->
  syscall_spec i m (Ok (ed_destroyed_eff addr len) (ed_destroyed_model m addr len) [])
  /\ ~ spurious_refusal_cfg (alloc_only_cfg false) i m (ed_destroyed_eff addr len).
Proof.
  intros i addr len prot flags fd off m Hc Ha H0 HR.
  exact (arm_forced _ _ _ _ _ (ed_frw_contained_shape i addr len prot flags fd off m Hc Ha H0) HR _ _ _ (or_intror (ed_destroyed_intro m addr len))).
Qed.

(* ---- frw_free ---- *)

Lemma ed_frw_free_spec : forall addr len prot flags fd off i m eff m' evs,
  ed_frw_arm m addr len prot flags off ->
  ed_fixed_contained m addr len = false ->
  ed_fixed_free m addr len = true ->
  mmap_spec addr len prot flags fd off i m (Ok eff m' evs)
  <-> ed_refused m eff m' evs \/ ed_rw_fresh_ok flags m addr len eff m' evs.
Proof.
  intros addr len prot flags fd off i m eff m' evs Harm H0 H1.
  unfold ed_frw_arm, ed_fixed_gate in Harm. destruct Harm as (Hoff & Hanon & Hlen & Hmod & Hna & Hfx & Hrw & Hw & Htop & Hal & Hpos).
  unfold ed_fixed_contained, ed_fixed_free, ed_fixed_resfree in *.
  unfold mmap_spec. ed_spec_tac.
Qed.

Lemma ed_frw_free_shape : forall i addr len prot flags fd off m,
  ed_mmap_call i addr len prot flags fd off ->
  ed_frw_arm m addr len prot flags off ->
  ed_fixed_contained m addr len = false ->
  ed_fixed_free m addr len = true ->
  arm_shape i m (mmap_fixed_fresh_refusable flags m (page_round_up_Z (bv_unsigned len))) (ed_refused m) (ed_rw_fresh_ok flags m addr len).
Proof.
  intros i addr len prot flags fd off m Hc Harm H0 H1.
  split; [exact (ed_mmap_call_sysno _ _ _ _ _ _ _ Hc)|].
  split.
  { intros eff m' evs. rewrite (ed_mmap_call_spec _ _ _ _ _ _ _ _ _ Hc).
    apply ed_frw_free_spec; assumption. }
  split; [exact (ed_refused_ret m)|].
  split.
  { intros eff m' evs HG. unfold ed_rw_fresh_ok in HG. cbv zeta in HG. ed_inv.
    exact (ed_gate_ne_enomem m addr len (ed_frw_arm_gate _ _ _ _ _ _ Harm)). }

  unfold mmap_fixed_fresh_refusable. split.
  - intros HR. apply negb_false_iff in HR. do 3 eexists. unfold ed_rw_fresh_ok. cbv zeta. ed_solve.
  - intros (eff & m' & evs & HG). unfold ed_rw_fresh_ok in HG. cbv zeta in HG.
    destruct HG as (Hb & _). rewrite Hb. reflexivity.
Qed.

Lemma ed_frw_free_inversion : forall i addr len prot flags fd off m eff m' evs,
  ed_mmap_call i addr len prot flags fd off ->
  ed_frw_arm m addr len prot flags off ->
  ed_fixed_contained m addr len = false ->
  ed_fixed_free m addr len = true ->
  syscall_spec i m (Ok eff m' evs) ->
  ~ spurious_refusal_cfg (alloc_only_cfg false) i m eff ->
  ed_rw_fresh_ok flags m addr len eff m' evs \/ (ed_refused m eff m' evs /\ mmap_fixed_fresh_refusable flags m (page_round_up_Z (bv_unsigned len)) = true).
Proof. intros i addr len prot flags fd off m eff m' evs Hc Ha H0 H1. exact (arm_inversion _ _ _ _ _ (ed_frw_free_shape i addr len prot flags fd off m Hc Ha H0 H1) eff m' evs). Qed.

Lemma ed_frw_free_forced : forall i addr len prot flags fd off m,
  ed_mmap_call i addr len prot flags fd off ->
  ed_frw_arm m addr len prot flags off ->
  ed_fixed_contained m addr len = false ->
  ed_fixed_free m addr len = true ->
  mmap_fixed_fresh_refusable flags m (page_round_up_Z (bv_unsigned len)) = true ->
  syscall_spec i m (Ok (mkEffect (errno_ret ENOMEM) [] []) m [])
  /\ ~ spurious_refusal_cfg (alloc_only_cfg false) i m (mkEffect (errno_ret ENOMEM) [] []).
Proof.
  intros i addr len prot flags fd off m Hc Ha H0 H1 HR.
  exact (arm_forced _ _ _ _ _ (ed_frw_free_shape i addr len prot flags fd off m Hc Ha H0 H1) HR _ _ _ (ed_refused_intro m)).
Qed.

Lemma ed_frw_free_exact : forall i addr len prot flags fd off m eff m' evs,
  ed_mmap_call i addr len prot flags fd off ->
  ed_frw_arm m addr len prot flags off ->
  ed_fixed_contained m addr len = false ->
  ed_fixed_free m addr len = true ->
  (syscall_spec i m (Ok eff m' evs) /\ ~ spurious_refusal_cfg (alloc_only_cfg false) i m eff)
  <-> ed_rw_fresh_ok flags m addr len eff m' evs \/ (ed_refused m eff m' evs /\ mmap_fixed_fresh_refusable flags m (page_round_up_Z (bv_unsigned len)) = true).
Proof. intros i addr len prot flags fd off m eff m' evs Hc Ha H0 H1. exact (arm_exact _ _ _ _ _ (ed_frw_free_shape i addr len prot flags fd off m Hc Ha H0 H1) eff m' evs). Qed.

Lemma ed_frw_free_grant_nonspurious : forall i addr len prot flags fd off m eff m' evs,
  ed_mmap_call i addr len prot flags fd off ->
  ed_frw_arm m addr len prot flags off ->
  ed_fixed_contained m addr len = false ->
  ed_fixed_free m addr len = true ->
  ed_rw_fresh_ok flags m addr len eff m' evs ->
  syscall_spec i m (Ok eff m' evs) /\ ~ spurious_refusal_cfg (alloc_only_cfg false) i m eff.
Proof. intros i addr len prot flags fd off m eff m' evs Hc Ha H0 H1. exact (arm_grant _ _ _ _ _ (ed_frw_free_shape i addr len prot flags fd off m Hc Ha H0 H1) eff m' evs). Qed.

(* ---- frw_span ---- *)

Lemma ed_frw_span_spec : forall addr len prot flags fd off i m eff m' evs,
  ed_frw_arm m addr len prot flags off ->
  ed_fixed_contained m addr len = false ->
  ed_fixed_free m addr len = false ->
  ed_fixed_resfree m addr len = true ->
  mmap_spec addr len prot flags fd off i m (Ok eff m' evs)
  <-> ed_refused_or_destroyed m addr len eff m' evs \/ ed_frw_span_ok flags m addr len eff m' evs.
Proof.
  intros addr len prot flags fd off i m eff m' evs Harm H0 H1 H2.
  unfold ed_frw_arm, ed_fixed_gate in Harm. destruct Harm as (Hoff & Hanon & Hlen & Hmod & Hna & Hfx & Hrw & Hw & Htop & Hal & Hpos).
  unfold ed_fixed_contained, ed_fixed_free, ed_fixed_resfree in *.
  rewrite H2 in H0. cbn [andb] in H0.
  unfold mmap_spec. ed_spec_tac.
Qed.

Lemma ed_frw_span_shape : forall i addr len prot flags fd off m,
  ed_mmap_call i addr len prot flags fd off ->
  ed_frw_arm m addr len prot flags off ->
  ed_fixed_contained m addr len = false ->
  ed_fixed_free m addr len = false ->
  ed_fixed_resfree m addr len = true ->
  arm_shape i m (mmap_fixed_span_refusable flags m addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))) (ed_refused_or_destroyed m addr len) (ed_frw_span_ok flags m addr len).
Proof.
  intros i addr len prot flags fd off m Hc Harm H0 H1 H2.
  split; [exact (ed_mmap_call_sysno _ _ _ _ _ _ _ Hc)|].
  split.
  { intros eff m' evs. rewrite (ed_mmap_call_spec _ _ _ _ _ _ _ _ _ Hc).
    apply ed_frw_span_spec; assumption. }
  split; [exact (ed_refused_or_destroyed_ret m addr len)|].
  split.
  { intros eff m' evs HG. unfold ed_frw_span_ok in HG. cbv zeta in HG. ed_inv.
    exact (ed_gate_ne_enomem m addr len (ed_frw_arm_gate _ _ _ _ _ _ Harm)). }

  unfold mmap_fixed_span_refusable. split.
  - intros HR. apply negb_false_iff in HR. do 3 eexists. unfold ed_frw_span_ok. cbv zeta. ed_solve.
  - intros (eff & m' & evs & HG). unfold ed_frw_span_ok in HG. cbv zeta in HG.
    destruct HG as (Hb & _). rewrite Hb. reflexivity.
Qed.

Lemma ed_frw_span_inversion : forall i addr len prot flags fd off m eff m' evs,
  ed_mmap_call i addr len prot flags fd off ->
  ed_frw_arm m addr len prot flags off ->
  ed_fixed_contained m addr len = false ->
  ed_fixed_free m addr len = false ->
  ed_fixed_resfree m addr len = true ->
  syscall_spec i m (Ok eff m' evs) ->
  ~ spurious_refusal_cfg (alloc_only_cfg false) i m eff ->
  ed_frw_span_ok flags m addr len eff m' evs \/ (ed_refused_or_destroyed m addr len eff m' evs /\ mmap_fixed_span_refusable flags m addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) = true).
Proof. intros i addr len prot flags fd off m eff m' evs Hc Ha H0 H1 H2. exact (arm_inversion _ _ _ _ _ (ed_frw_span_shape i addr len prot flags fd off m Hc Ha H0 H1 H2) eff m' evs). Qed.

Lemma ed_frw_span_forced : forall i addr len prot flags fd off m,
  ed_mmap_call i addr len prot flags fd off ->
  ed_frw_arm m addr len prot flags off ->
  ed_fixed_contained m addr len = false ->
  ed_fixed_free m addr len = false ->
  ed_fixed_resfree m addr len = true ->
  mmap_fixed_span_refusable flags m addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) = true ->
  syscall_spec i m (Ok (mkEffect (errno_ret ENOMEM) [] []) m [])
  /\ ~ spurious_refusal_cfg (alloc_only_cfg false) i m (mkEffect (errno_ret ENOMEM) [] []).
Proof.
  intros i addr len prot flags fd off m Hc Ha H0 H1 H2 HR.
  exact (arm_forced _ _ _ _ _ (ed_frw_span_shape i addr len prot flags fd off m Hc Ha H0 H1 H2) HR _ _ _ (or_introl (ed_refused_intro m))).
Qed.

Lemma ed_frw_span_exact : forall i addr len prot flags fd off m eff m' evs,
  ed_mmap_call i addr len prot flags fd off ->
  ed_frw_arm m addr len prot flags off ->
  ed_fixed_contained m addr len = false ->
  ed_fixed_free m addr len = false ->
  ed_fixed_resfree m addr len = true ->
  (syscall_spec i m (Ok eff m' evs) /\ ~ spurious_refusal_cfg (alloc_only_cfg false) i m eff)
  <-> ed_frw_span_ok flags m addr len eff m' evs \/ (ed_refused_or_destroyed m addr len eff m' evs /\ mmap_fixed_span_refusable flags m addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) = true).
Proof. intros i addr len prot flags fd off m eff m' evs Hc Ha H0 H1 H2. exact (arm_exact _ _ _ _ _ (ed_frw_span_shape i addr len prot flags fd off m Hc Ha H0 H1 H2) eff m' evs). Qed.

Lemma ed_frw_span_grant_nonspurious : forall i addr len prot flags fd off m eff m' evs,
  ed_mmap_call i addr len prot flags fd off ->
  ed_frw_arm m addr len prot flags off ->
  ed_fixed_contained m addr len = false ->
  ed_fixed_free m addr len = false ->
  ed_fixed_resfree m addr len = true ->
  ed_frw_span_ok flags m addr len eff m' evs ->
  syscall_spec i m (Ok eff m' evs) /\ ~ spurious_refusal_cfg (alloc_only_cfg false) i m eff.
Proof. intros i addr len prot flags fd off m eff m' evs Hc Ha H0 H1 H2. exact (arm_grant _ _ _ _ _ (ed_frw_span_shape i addr len prot flags fd off m Hc Ha H0 H1 H2) eff m' evs). Qed.

Lemma ed_frw_span_inversion_budget : forall i addr len prot flags fd off m eff m' evs,
  ed_mmap_call i addr len prot flags fd off ->
  ed_frw_arm m addr len prot flags off ->
  ed_fixed_contained m addr len = false ->
  ed_fixed_free m addr len = false ->
  ed_fixed_resfree m addr len = true ->
  mmap_fixed_rw_span_budget_ok flags m addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) = true ->
  syscall_spec i m (Ok eff m' evs) ->
  ~ spurious_refusal_cfg (alloc_only_cfg false) i m eff ->
  ed_frw_span_ok flags m addr len eff m' evs \/ (ed_refused m eff m' evs /\ mmap_fixed_span_refusable flags m addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) = true).
Proof.
  intros i addr len prot flags fd off m eff m' evs Hc Ha H0 H1 H2 Hb Hs Hns.
  assert (ER : mmap_fixed_span_refusable flags m addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) = false) by (unfold mmap_fixed_span_refusable; rewrite Hb; reflexivity).
  destruct (arm_inversion _ _ _ _ _ (ed_frw_span_shape i addr len prot flags fd off m Hc Ha H0 H1 H2) eff m' evs Hs Hns) as [Hg | (_ & E)];
    [left; exact Hg | rewrite ER in E; discriminate E].
Qed.

Lemma ed_frw_span_destroyed_spurious : forall i addr len prot flags fd off m,
  ed_mmap_call i addr len prot flags fd off ->
  ed_frw_arm m addr len prot flags off ->
  ed_fixed_contained m addr len = false ->
  ed_fixed_free m addr len = false ->
  ed_fixed_resfree m addr len = true ->
  mmap_fixed_rw_span_budget_ok flags m addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) = true ->
  syscall_spec i m (Ok (ed_destroyed_eff addr len) (ed_destroyed_model m addr len) [])
  /\ spurious_refusal_cfg (alloc_only_cfg false) i m (ed_destroyed_eff addr len).
Proof.
  intros i addr len prot flags fd off m Hc Ha H0 H1 H2 Hb.
  assert (ER : mmap_fixed_span_refusable flags m addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) = false) by (unfold mmap_fixed_span_refusable; rewrite Hb; reflexivity).
  exact (arm_refused_spurious _ _ _ _ _ (ed_frw_span_shape i addr len prot flags fd off m Hc Ha H0 H1 H2) ER _ _ _ (or_intror (ed_destroyed_intro m addr len))).
Qed.

Lemma ed_frw_span_destroyed_forced : forall i addr len prot flags fd off m,
  ed_mmap_call i addr len prot flags fd off ->
  ed_frw_arm m addr len prot flags off ->
  ed_fixed_contained m addr len = false ->
  ed_fixed_free m addr len = false ->
  ed_fixed_resfree m addr len = true ->
  mmap_fixed_span_refusable flags m addr (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) = true ->
  syscall_spec i m (Ok (ed_destroyed_eff addr len) (ed_destroyed_model m addr len) [])
  /\ ~ spurious_refusal_cfg (alloc_only_cfg false) i m (ed_destroyed_eff addr len).
Proof.
  intros i addr len prot flags fd off m Hc Ha H0 H1 H2 HR.
  exact (arm_forced _ _ _ _ _ (ed_frw_span_shape i addr len prot flags fd off m Hc Ha H0 H1 H2) HR _ _ _ (or_intror (ed_destroyed_intro m addr len))).
Qed.

(* ---- nrna_free ---- *)

Lemma ed_nrna_free_spec : forall addr len prot flags fd off i m eff m' evs,
  ed_nrna_arm m addr len prot flags off ->
  ed_fixed_free m addr len = true ->
  mmap_spec addr len prot flags fd off i m (Ok eff m' evs)
  <-> ed_refused m eff m' evs \/ ed_na_fresh_ok flags m addr len eff m' evs.
Proof.
  intros addr len prot flags fd off i m eff m' evs Harm H0.
  unfold ed_nrna_arm, ed_fixed_gate in Harm. destruct Harm as (Hoff & Hanon & Hlen & Hmod & Hna & Hfx & Hrw & Hnna & Hw & Htop & Hal & Hpos).
  unfold ed_fixed_contained, ed_fixed_free, ed_fixed_resfree in *.
  unfold mmap_spec. ed_spec_tac.
Qed.

Lemma ed_nrna_free_shape : forall i addr len prot flags fd off m,
  ed_mmap_call i addr len prot flags fd off ->
  ed_nrna_arm m addr len prot flags off ->
  ed_fixed_free m addr len = true ->
  arm_shape i m (false) (ed_refused m) (ed_na_fresh_ok flags m addr len).
Proof.
  intros i addr len prot flags fd off m Hc Harm H0.
  split; [exact (ed_mmap_call_sysno _ _ _ _ _ _ _ Hc)|].
  split.
  { intros eff m' evs. rewrite (ed_mmap_call_spec _ _ _ _ _ _ _ _ _ Hc).
    apply ed_nrna_free_spec; assumption. }
  split; [exact (ed_refused_ret m)|].
  split.
  { intros eff m' evs HG. unfold ed_na_fresh_ok in HG. cbv zeta in HG. ed_inv.
    exact (ed_gate_ne_enomem m addr len (ed_nrna_arm_gate _ _ _ _ _ _ Harm)). }

  split; [intros _; do 3 eexists; unfold ed_na_fresh_ok; cbv zeta; ed_solve | intros _; reflexivity].
Qed.

Lemma ed_nrna_free_inversion : forall i addr len prot flags fd off m eff m' evs,
  ed_mmap_call i addr len prot flags fd off ->
  ed_nrna_arm m addr len prot flags off ->
  ed_fixed_free m addr len = true ->
  syscall_spec i m (Ok eff m' evs) ->
  ~ spurious_refusal_cfg (alloc_only_cfg false) i m eff ->
  ed_na_fresh_ok flags m addr len eff m' evs.
Proof. intros i addr len prot flags fd off m eff m' evs Hc Ha H0. exact (arm_inversion_false _ _ _ _ (ed_nrna_free_shape i addr len prot flags fd off m Hc Ha H0) eff m' evs). Qed.

Lemma ed_nrna_free_refusal_spurious : forall i addr len prot flags fd off m eff m' evs,
  ed_mmap_call i addr len prot flags fd off ->
  ed_nrna_arm m addr len prot flags off ->
  ed_fixed_free m addr len = true ->
  ed_refused m eff m' evs ->
  syscall_spec i m (Ok eff m' evs) /\ spurious_refusal_cfg (alloc_only_cfg false) i m eff.
Proof. intros i addr len prot flags fd off m eff m' evs Hc Ha H0. exact (arm_refused_spurious _ _ _ _ _ (ed_nrna_free_shape i addr len prot flags fd off m Hc Ha H0) eq_refl eff m' evs). Qed.

Lemma ed_nrna_free_exact : forall i addr len prot flags fd off m eff m' evs,
  ed_mmap_call i addr len prot flags fd off ->
  ed_nrna_arm m addr len prot flags off ->
  ed_fixed_free m addr len = true ->
  (syscall_spec i m (Ok eff m' evs) /\ ~ spurious_refusal_cfg (alloc_only_cfg false) i m eff)
  <-> ed_na_fresh_ok flags m addr len eff m' evs.
Proof.
  intros i addr len prot flags fd off m eff m' evs Hc Ha H0. rewrite (arm_exact _ _ _ _ _ (ed_nrna_free_shape i addr len prot flags fd off m Hc Ha H0) eff m' evs).
  split; [intros [Hg | (_ & E)]; [exact Hg | discriminate E] | intros Hg; left; exact Hg].
Qed.

Lemma ed_nrna_free_grant_nonspurious : forall i addr len prot flags fd off m eff m' evs,
  ed_mmap_call i addr len prot flags fd off ->
  ed_nrna_arm m addr len prot flags off ->
  ed_fixed_free m addr len = true ->
  ed_na_fresh_ok flags m addr len eff m' evs ->
  syscall_spec i m (Ok eff m' evs) /\ ~ spurious_refusal_cfg (alloc_only_cfg false) i m eff.
Proof. intros i addr len prot flags fd off m eff m' evs Hc Ha H0. exact (arm_grant _ _ _ _ _ (ed_nrna_free_shape i addr len prot flags fd off m Hc Ha H0) eff m' evs). Qed.

(* ---- nrna_occupied ---- *)

Lemma ed_nrna_occupied_spec : forall addr len prot flags fd off i m eff m' evs,
  ed_nrna_arm m addr len prot flags off ->
  ed_fixed_free m addr len = false ->
  mmap_spec addr len prot flags fd off i m (Ok eff m' evs)
  <-> ed_refused m eff m' evs \/ ed_eexist m eff m' evs.
Proof.
  intros addr len prot flags fd off i m eff m' evs Harm H0.
  unfold ed_nrna_arm, ed_fixed_gate in Harm. destruct Harm as (Hoff & Hanon & Hlen & Hmod & Hna & Hfx & Hrw & Hnna & Hw & Htop & Hal & Hpos).
  unfold ed_fixed_contained, ed_fixed_free, ed_fixed_resfree in *.
  unfold mmap_spec. ed_spec_tac.
Qed.

Lemma ed_nrna_occupied_shape : forall i addr len prot flags fd off m,
  ed_mmap_call i addr len prot flags fd off ->
  ed_nrna_arm m addr len prot flags off ->
  ed_fixed_free m addr len = false ->
  arm_shape i m (false) (ed_refused m) (ed_eexist m).
Proof.
  intros i addr len prot flags fd off m Hc Harm H0.
  split; [exact (ed_mmap_call_sysno _ _ _ _ _ _ _ Hc)|].
  split.
  { intros eff m' evs. rewrite (ed_mmap_call_spec _ _ _ _ _ _ _ _ _ Hc).
    apply ed_nrna_occupied_spec; assumption. }
  split; [exact (ed_refused_ret m)|].
  split.
  { intros eff m' evs HG. unfold ed_eexist in HG. cbv zeta in HG. ed_inv.
    exact ed_eexist_ne_enomem. }

  split; [intros _; do 3 eexists; unfold ed_eexist; cbv zeta; ed_solve | intros _; reflexivity].
Qed.

Lemma ed_nrna_occupied_inversion : forall i addr len prot flags fd off m eff m' evs,
  ed_mmap_call i addr len prot flags fd off ->
  ed_nrna_arm m addr len prot flags off ->
  ed_fixed_free m addr len = false ->
  syscall_spec i m (Ok eff m' evs) ->
  ~ spurious_refusal_cfg (alloc_only_cfg false) i m eff ->
  ed_eexist m eff m' evs.
Proof. intros i addr len prot flags fd off m eff m' evs Hc Ha H0. exact (arm_inversion_false _ _ _ _ (ed_nrna_occupied_shape i addr len prot flags fd off m Hc Ha H0) eff m' evs). Qed.

Lemma ed_nrna_occupied_refusal_spurious : forall i addr len prot flags fd off m eff m' evs,
  ed_mmap_call i addr len prot flags fd off ->
  ed_nrna_arm m addr len prot flags off ->
  ed_fixed_free m addr len = false ->
  ed_refused m eff m' evs ->
  syscall_spec i m (Ok eff m' evs) /\ spurious_refusal_cfg (alloc_only_cfg false) i m eff.
Proof. intros i addr len prot flags fd off m eff m' evs Hc Ha H0. exact (arm_refused_spurious _ _ _ _ _ (ed_nrna_occupied_shape i addr len prot flags fd off m Hc Ha H0) eq_refl eff m' evs). Qed.

Lemma ed_nrna_occupied_exact : forall i addr len prot flags fd off m eff m' evs,
  ed_mmap_call i addr len prot flags fd off ->
  ed_nrna_arm m addr len prot flags off ->
  ed_fixed_free m addr len = false ->
  (syscall_spec i m (Ok eff m' evs) /\ ~ spurious_refusal_cfg (alloc_only_cfg false) i m eff)
  <-> ed_eexist m eff m' evs.
Proof.
  intros i addr len prot flags fd off m eff m' evs Hc Ha H0. rewrite (arm_exact _ _ _ _ _ (ed_nrna_occupied_shape i addr len prot flags fd off m Hc Ha H0) eff m' evs).
  split; [intros [Hg | (_ & E)]; [exact Hg | discriminate E] | intros Hg; left; exact Hg].
Qed.

Lemma ed_nrna_occupied_grant_nonspurious : forall i addr len prot flags fd off m eff m' evs,
  ed_mmap_call i addr len prot flags fd off ->
  ed_nrna_arm m addr len prot flags off ->
  ed_fixed_free m addr len = false ->
  ed_eexist m eff m' evs ->
  syscall_spec i m (Ok eff m' evs) /\ ~ spurious_refusal_cfg (alloc_only_cfg false) i m eff.
Proof. intros i addr len prot flags fd off m eff m' evs Hc Ha H0. exact (arm_grant _ _ _ _ _ (ed_nrna_occupied_shape i addr len prot flags fd off m Hc Ha H0) eff m' evs). Qed.

(* ---- nrrw_free ---- *)

Lemma ed_nrrw_free_spec : forall addr len prot flags fd off i m eff m' evs,
  ed_nrrw_arm m addr len prot flags off ->
  ed_fixed_free m addr len = true ->
  mmap_spec addr len prot flags fd off i m (Ok eff m' evs)
  <-> ed_refused m eff m' evs \/ ed_rw_fresh_ok flags m addr len eff m' evs.
Proof.
  intros addr len prot flags fd off i m eff m' evs Harm H0.
  unfold ed_nrrw_arm, ed_fixed_gate in Harm. destruct Harm as (Hoff & Hanon & Hlen & Hmod & Hna & Hfx & Hrw & Hnna & Hnrw & Hw & Htop & Hal & Hpos).
  unfold ed_fixed_contained, ed_fixed_free, ed_fixed_resfree in *.
  unfold mmap_spec. ed_spec_tac.
Qed.

Lemma ed_nrrw_free_shape : forall i addr len prot flags fd off m,
  ed_mmap_call i addr len prot flags fd off ->
  ed_nrrw_arm m addr len prot flags off ->
  ed_fixed_free m addr len = true ->
  arm_shape i m (mmap_fixed_fresh_refusable flags m (page_round_up_Z (bv_unsigned len))) (ed_refused m) (ed_rw_fresh_ok flags m addr len).
Proof.
  intros i addr len prot flags fd off m Hc Harm H0.
  split; [exact (ed_mmap_call_sysno _ _ _ _ _ _ _ Hc)|].
  split.
  { intros eff m' evs. rewrite (ed_mmap_call_spec _ _ _ _ _ _ _ _ _ Hc).
    apply ed_nrrw_free_spec; assumption. }
  split; [exact (ed_refused_ret m)|].
  split.
  { intros eff m' evs HG. unfold ed_rw_fresh_ok in HG. cbv zeta in HG. ed_inv.
    exact (ed_gate_ne_enomem m addr len (ed_nrrw_arm_gate _ _ _ _ _ _ Harm)). }

  unfold mmap_fixed_fresh_refusable. split.
  - intros HR. apply negb_false_iff in HR. do 3 eexists. unfold ed_rw_fresh_ok. cbv zeta. ed_solve.
  - intros (eff & m' & evs & HG). unfold ed_rw_fresh_ok in HG. cbv zeta in HG.
    destruct HG as (Hb & _). rewrite Hb. reflexivity.
Qed.

Lemma ed_nrrw_free_inversion : forall i addr len prot flags fd off m eff m' evs,
  ed_mmap_call i addr len prot flags fd off ->
  ed_nrrw_arm m addr len prot flags off ->
  ed_fixed_free m addr len = true ->
  syscall_spec i m (Ok eff m' evs) ->
  ~ spurious_refusal_cfg (alloc_only_cfg false) i m eff ->
  ed_rw_fresh_ok flags m addr len eff m' evs \/ (ed_refused m eff m' evs /\ mmap_fixed_fresh_refusable flags m (page_round_up_Z (bv_unsigned len)) = true).
Proof. intros i addr len prot flags fd off m eff m' evs Hc Ha H0. exact (arm_inversion _ _ _ _ _ (ed_nrrw_free_shape i addr len prot flags fd off m Hc Ha H0) eff m' evs). Qed.

Lemma ed_nrrw_free_forced : forall i addr len prot flags fd off m,
  ed_mmap_call i addr len prot flags fd off ->
  ed_nrrw_arm m addr len prot flags off ->
  ed_fixed_free m addr len = true ->
  mmap_fixed_fresh_refusable flags m (page_round_up_Z (bv_unsigned len)) = true ->
  syscall_spec i m (Ok (mkEffect (errno_ret ENOMEM) [] []) m [])
  /\ ~ spurious_refusal_cfg (alloc_only_cfg false) i m (mkEffect (errno_ret ENOMEM) [] []).
Proof.
  intros i addr len prot flags fd off m Hc Ha H0 HR.
  exact (arm_forced _ _ _ _ _ (ed_nrrw_free_shape i addr len prot flags fd off m Hc Ha H0) HR _ _ _ (ed_refused_intro m)).
Qed.

Lemma ed_nrrw_free_exact : forall i addr len prot flags fd off m eff m' evs,
  ed_mmap_call i addr len prot flags fd off ->
  ed_nrrw_arm m addr len prot flags off ->
  ed_fixed_free m addr len = true ->
  (syscall_spec i m (Ok eff m' evs) /\ ~ spurious_refusal_cfg (alloc_only_cfg false) i m eff)
  <-> ed_rw_fresh_ok flags m addr len eff m' evs \/ (ed_refused m eff m' evs /\ mmap_fixed_fresh_refusable flags m (page_round_up_Z (bv_unsigned len)) = true).
Proof. intros i addr len prot flags fd off m eff m' evs Hc Ha H0. exact (arm_exact _ _ _ _ _ (ed_nrrw_free_shape i addr len prot flags fd off m Hc Ha H0) eff m' evs). Qed.

Lemma ed_nrrw_free_grant_nonspurious : forall i addr len prot flags fd off m eff m' evs,
  ed_mmap_call i addr len prot flags fd off ->
  ed_nrrw_arm m addr len prot flags off ->
  ed_fixed_free m addr len = true ->
  ed_rw_fresh_ok flags m addr len eff m' evs ->
  syscall_spec i m (Ok eff m' evs) /\ ~ spurious_refusal_cfg (alloc_only_cfg false) i m eff.
Proof. intros i addr len prot flags fd off m eff m' evs Hc Ha H0. exact (arm_grant _ _ _ _ _ (ed_nrrw_free_shape i addr len prot flags fd off m Hc Ha H0) eff m' evs). Qed.

(* ---- nrrw_occupied ---- *)

Lemma ed_nrrw_occupied_spec : forall addr len prot flags fd off i m eff m' evs,
  ed_nrrw_arm m addr len prot flags off ->
  ed_fixed_free m addr len = false ->
  mmap_spec addr len prot flags fd off i m (Ok eff m' evs)
  <-> ed_refused m eff m' evs \/ ed_eexist m eff m' evs.
Proof.
  intros addr len prot flags fd off i m eff m' evs Harm H0.
  unfold ed_nrrw_arm, ed_fixed_gate in Harm. destruct Harm as (Hoff & Hanon & Hlen & Hmod & Hna & Hfx & Hrw & Hnna & Hnrw & Hw & Htop & Hal & Hpos).
  unfold ed_fixed_contained, ed_fixed_free, ed_fixed_resfree in *.
  unfold mmap_spec. ed_spec_tac.
Qed.

Lemma ed_nrrw_occupied_shape : forall i addr len prot flags fd off m,
  ed_mmap_call i addr len prot flags fd off ->
  ed_nrrw_arm m addr len prot flags off ->
  ed_fixed_free m addr len = false ->
  arm_shape i m (false) (ed_refused m) (ed_eexist m).
Proof.
  intros i addr len prot flags fd off m Hc Harm H0.
  split; [exact (ed_mmap_call_sysno _ _ _ _ _ _ _ Hc)|].
  split.
  { intros eff m' evs. rewrite (ed_mmap_call_spec _ _ _ _ _ _ _ _ _ Hc).
    apply ed_nrrw_occupied_spec; assumption. }
  split; [exact (ed_refused_ret m)|].
  split.
  { intros eff m' evs HG. unfold ed_eexist in HG. cbv zeta in HG. ed_inv.
    exact ed_eexist_ne_enomem. }

  split; [intros _; do 3 eexists; unfold ed_eexist; cbv zeta; ed_solve | intros _; reflexivity].
Qed.

Lemma ed_nrrw_occupied_inversion : forall i addr len prot flags fd off m eff m' evs,
  ed_mmap_call i addr len prot flags fd off ->
  ed_nrrw_arm m addr len prot flags off ->
  ed_fixed_free m addr len = false ->
  syscall_spec i m (Ok eff m' evs) ->
  ~ spurious_refusal_cfg (alloc_only_cfg false) i m eff ->
  ed_eexist m eff m' evs.
Proof. intros i addr len prot flags fd off m eff m' evs Hc Ha H0. exact (arm_inversion_false _ _ _ _ (ed_nrrw_occupied_shape i addr len prot flags fd off m Hc Ha H0) eff m' evs). Qed.

Lemma ed_nrrw_occupied_refusal_spurious : forall i addr len prot flags fd off m eff m' evs,
  ed_mmap_call i addr len prot flags fd off ->
  ed_nrrw_arm m addr len prot flags off ->
  ed_fixed_free m addr len = false ->
  ed_refused m eff m' evs ->
  syscall_spec i m (Ok eff m' evs) /\ spurious_refusal_cfg (alloc_only_cfg false) i m eff.
Proof. intros i addr len prot flags fd off m eff m' evs Hc Ha H0. exact (arm_refused_spurious _ _ _ _ _ (ed_nrrw_occupied_shape i addr len prot flags fd off m Hc Ha H0) eq_refl eff m' evs). Qed.

Lemma ed_nrrw_occupied_exact : forall i addr len prot flags fd off m eff m' evs,
  ed_mmap_call i addr len prot flags fd off ->
  ed_nrrw_arm m addr len prot flags off ->
  ed_fixed_free m addr len = false ->
  (syscall_spec i m (Ok eff m' evs) /\ ~ spurious_refusal_cfg (alloc_only_cfg false) i m eff)
  <-> ed_eexist m eff m' evs.
Proof.
  intros i addr len prot flags fd off m eff m' evs Hc Ha H0. rewrite (arm_exact _ _ _ _ _ (ed_nrrw_occupied_shape i addr len prot flags fd off m Hc Ha H0) eff m' evs).
  split; [intros [Hg | (_ & E)]; [exact Hg | discriminate E] | intros Hg; left; exact Hg].
Qed.

Lemma ed_nrrw_occupied_grant_nonspurious : forall i addr len prot flags fd off m eff m' evs,
  ed_mmap_call i addr len prot flags fd off ->
  ed_nrrw_arm m addr len prot flags off ->
  ed_fixed_free m addr len = false ->
  ed_eexist m eff m' evs ->
  syscall_spec i m (Ok eff m' evs) /\ ~ spurious_refusal_cfg (alloc_only_cfg false) i m eff.
Proof. intros i addr len prot flags fd off m eff m' evs Hc Ha H0. exact (arm_grant _ _ _ _ _ (ed_nrrw_occupied_shape i addr len prot flags fd off m Hc Ha H0) eff m' evs). Qed.


(* ========================================================================= *)
(* (5) brk and mremap.                                                         *)

Definition ed_brk_call (i : SyscallInput) (req : word) : Prop :=
  bv_unsigned (in_sysno i) = 214%Z /\ in_arg i 0 = req.

Definition ed_brk_eff (m : Model) (req r : word) : SyscallEffect :=
  mkEffectU r [] (brk_zeros req r (vm_brk (m_vmmaps m)))
    (brk_unmaps r (vm_brk (m_vmmaps m))) [] [].

(* a real grow request: neither the query nor below [min_brk], above the break *)
Definition ed_brk_grow (m : Model) (req : word) : Prop :=
  w_is0 req = false
  /\ (bv_unsigned (min_brk (m_vmmaps m)) <= bv_unsigned req)%Z
  /\ (bv_unsigned (vm_brk (m_vmmaps m)) < bv_unsigned req)%Z.

Definition ed_brk_shrink (m : Model) (req : word) : Prop :=
  w_is0 req = false
  /\ (bv_unsigned (min_brk (m_vmmaps m)) <= bv_unsigned req)%Z
  /\ (bv_unsigned req < bv_unsigned (vm_brk (m_vmmaps m)))%Z.

Lemma ed_brk_call_spec : forall i req, ed_brk_call i req -> forall m o,
  syscall_spec i m o <-> brk_spec req i m o.
Proof.
  intros i req (E & <-) m o. unfold syscall_spec, dispatch. rewrite E. reflexivity.
Qed.

Lemma ed_brk_spec_iff : forall req i m eff m' evs,
  brk_spec req i m (Ok eff m' evs)
  <-> exists r, brk_r_ok m req r = true
       /\ eff = ed_brk_eff m req r /\ m' = with_brk_next m req r /\ evs = [].
Proof.
  intros req i m eff m' evs. unfold brk_spec. rewrite bind_get_model.
  unfold ed_brk_eff, bind, choose, modify, pure. cbv beta iota zeta.
  split; intros H; ed_inv; ed_solve.
Qed.

Lemma ed_brk_refusal_b : forall i req m r, ed_brk_call i req ->
  refusal_b i m r = brk_refusal_b m req r.
Proof. intros i req m r (E & <-). unfold refusal_b. rewrite E. reflexivity. Qed.

Lemma ed_brk_family_off : forall i req, ed_brk_call i req ->
  injected_family_off (alloc_only_cfg false) i = true.
Proof. intros i req (E & _). unfold injected_family_off. rewrite E. reflexivity. Qed.

Lemma ed_brk_move_refusal : forall m req r,
  w_is0 req = false ->
  (bv_unsigned (min_brk (m_vmmaps m)) <= bv_unsigned req)%Z ->
  bv_unsigned req <> bv_unsigned (vm_brk (m_vmmaps m)) ->
  brk_refusal_b m req r = bv_eqb r (vm_brk (m_vmmaps m)).
Proof.
  intros m req r Hw Hmin Hne. unfold brk_refusal_b. cbv zeta.
  rewrite Hw, (proj2 (Z.ltb_ge _ _) Hmin).
  assert (E : bv_eqb req (vm_brk (m_vmmaps m)) = false) by (unfold bv_eqb; apply Z.eqb_neq; exact Hne).
  rewrite E. reflexivity.
Qed.

Lemma ed_brk_grow_r_ok : forall m req r, ed_brk_grow m req ->
  brk_r_ok m req r = (bv_eqb r req || bv_eqb r (vm_brk (m_vmmaps m))) && brk_grow_ok m req r.
Proof.
  intros m req r (Hw & Hmin & Hgt). unfold brk_r_ok. cbv zeta.
  rewrite Hw, (proj2 (Z.ltb_ge _ _) Hmin). cbn [orb].
  rewrite (proj2 (Z.ltb_ge _ _) (Z.lt_le_incl _ _ Hgt)). reflexivity.
Qed.

Lemma ed_brk_shrink_r_ok : forall m req r, ed_brk_shrink m req ->
  brk_r_ok m req r = (bv_eqb r req || bv_eqb r (vm_brk (m_vmmaps m))).
Proof.
  intros m req r (Hw & Hmin & Hlt). unfold brk_r_ok. cbv zeta.
  rewrite Hw, (proj2 (Z.ltb_ge _ _) Hmin). cbn [orb].
  rewrite (proj2 (Z.ltb_lt _ _) Hlt). reflexivity.
Qed.

Lemma ed_brk_grow_ok_keep : forall m req, brk_grow_ok m req (vm_brk (m_vmmaps m)) = true.
Proof.
  intros m req. unfold brk_grow_ok. cbv zeta.
  rewrite (proj2 (Z.ltb_ge (bv_unsigned (vm_brk (m_vmmaps m)))
                            (bv_unsigned (vm_brk (m_vmmaps m)))) (Z.le_refl _)).
  rewrite Bool.andb_false_r. reflexivity.
Qed.

Lemma ed_brk_grow_refusal : forall i req m r, ed_brk_call i req -> ed_brk_grow m req ->
  refusal_b i m r = bv_eqb r (vm_brk (m_vmmaps m)).
Proof.
  intros i req m r Hc (Hw & Hmin & Hgt). rewrite (ed_brk_refusal_b i req m r Hc).
  apply ed_brk_move_refusal; [exact Hw | exact Hmin | lia].
Qed.

(** (i) a real grow: the old-break answer is spurious iff the grow is admissible. *)
Lemma ed_brk_grow_keep_spurious_iff : forall i req m eff,
  ed_brk_call i req -> ed_brk_grow m req ->
  eff_ret eff = vm_brk (m_vmmaps m) ->
  spurious_refusal_cfg (alloc_only_cfg false) i m eff <-> brk_grow_ok m req req = true.
Proof.
  intros i req m eff Hc Hg Hret.
  pose proof (fun r => ed_brk_grow_refusal i req m r Hc Hg) as Hrf.
  assert (Hne : req <> vm_brk (m_vmmaps m)).
  { destruct Hg as (_ & _ & Hgt). intros E. rewrite E in Hgt. lia. }
  split.
  - intros (_ & _ & (eff2 & m2 & evs2 & Hs & Hnr)).
    rewrite (ed_brk_call_spec i req Hc), ed_brk_spec_iff in Hs.
    destruct Hs as (r & Hr & -> & _ & _).
    rewrite Hrf in Hnr. unfold ed_brk_eff in Hnr. cbn [eff_ret] in Hnr.
    rewrite (ed_brk_grow_r_ok m req r Hg), Hnr, orb_false_r in Hr.
    apply andb_true_iff in Hr as [Hr Hok]. apply bv_eqb_eq in Hr. subst r. exact Hok.
  - intros Hok. split; [exact (ed_brk_family_off i req Hc)|].
    split; [rewrite Hrf, Hret; apply ed_bv_eqb_refl|].
    exists (ed_brk_eff m req req), (with_brk_next m req req), []. split.
    + rewrite (ed_brk_call_spec i req Hc), ed_brk_spec_iff.
      exists req. split; [|split; [reflexivity | split; reflexivity]].
      rewrite (ed_brk_grow_r_ok m req req Hg), ed_bv_eqb_refl, Hok. reflexivity.
    + rewrite Hrf. unfold ed_brk_eff. cbn [eff_ret]. apply ed_bv_eqb_false. exact Hne.
Qed.

(** (a) for brk: a kept outcome of a real grow is the grow (admissible) or the
    old break with the grow inadmissible. *)
Lemma ed_brk_grow_inversion : forall i req m eff m' evs,
  ed_brk_call i req -> ed_brk_grow m req ->
  syscall_spec i m (Ok eff m' evs) ->
  ~ spurious_refusal_cfg (alloc_only_cfg false) i m eff ->
  exists r, eff = ed_brk_eff m req r /\ m' = with_brk_next m req r /\ evs = []
    /\ ((r = req /\ brk_grow_ok m req req = true)
        \/ (r = vm_brk (m_vmmaps m) /\ brk_grow_ok m req req = false)).
Proof.
  intros i req m eff m' evs Hc Hg Hs Hns.
  rewrite (ed_brk_call_spec i req Hc), ed_brk_spec_iff in Hs.
  destruct Hs as (r & Hr & Heff & Hm & Hevs).
  exists r. split; [exact Heff | split; [exact Hm | split; [exact Hevs|]]].
  rewrite (ed_brk_grow_r_ok m req r Hg) in Hr.
  apply andb_true_iff in Hr as [Hor Hok]. apply orb_true_iff in Hor as [Hq|Hb];
    apply bv_eqb_eq in Hq || apply bv_eqb_eq in Hb.
  - left. subst r. split; [reflexivity | exact Hok].
  - right. split; [exact Hb|].
    destruct (brk_grow_ok m req req) eqn:G; [exfalso|reflexivity].
    apply Hns. apply (ed_brk_grow_keep_spurious_iff i req m eff Hc Hg); [|exact G].
    rewrite Heff. unfold ed_brk_eff. cbn [eff_ret]. exact Hb.
Qed.

(** (b) for brk: an inadmissible grow forces the old break, which is kept. *)
Lemma ed_brk_grow_forced : forall i req m,
  ed_brk_call i req -> ed_brk_grow m req ->
  brk_grow_ok m req req = false ->
  syscall_spec i m (Ok (ed_brk_eff m req (vm_brk (m_vmmaps m)))
                      (with_brk_next m req (vm_brk (m_vmmaps m))) [])
  /\ ~ spurious_refusal_cfg (alloc_only_cfg false) i m (ed_brk_eff m req (vm_brk (m_vmmaps m))).
Proof.
  intros i req m Hc Hg HG. split.
  - rewrite (ed_brk_call_spec i req Hc), ed_brk_spec_iff.
    exists (vm_brk (m_vmmaps m)). split; [|split; [reflexivity | split; reflexivity]].
    rewrite (ed_brk_grow_r_ok m _ _ Hg), ed_bv_eqb_refl, orb_true_r, ed_brk_grow_ok_keep.
    reflexivity.
  - intros Hsp. apply (ed_brk_grow_keep_spurious_iff i req m _ Hc Hg) in Hsp;
      [rewrite HG in Hsp; discriminate Hsp | reflexivity].
Qed.

(** (c) for brk: the grow, when admissible, is kept. *)
Lemma ed_brk_grow_grant_nonspurious : forall i req m,
  ed_brk_call i req -> ed_brk_grow m req ->
  brk_grow_ok m req req = true ->
  syscall_spec i m (Ok (ed_brk_eff m req req) (with_brk_next m req req) [])
  /\ ~ spurious_refusal_cfg (alloc_only_cfg false) i m (ed_brk_eff m req req).
Proof.
  intros i req m Hc Hg HG. split.
  - rewrite (ed_brk_call_spec i req Hc), ed_brk_spec_iff.
    exists req. split; [|split; [reflexivity | split; reflexivity]].
    rewrite (ed_brk_grow_r_ok m _ _ Hg), ed_bv_eqb_refl, HG. reflexivity.
  - apply spurious_refusal_not_refusal. rewrite (ed_brk_grow_refusal i req m _ Hc Hg).
    unfold ed_brk_eff. cbn [eff_ret]. apply ed_bv_eqb_false.
    destruct Hg as (_ & _ & Hgt). intros E. rewrite E in Hgt. lia.
Qed.

(** A real shrink: the old-break answer is always spurious. *)
Lemma ed_brk_shrink_keep_spurious : forall i req m eff,
  ed_brk_call i req -> ed_brk_shrink m req ->
  eff_ret eff = vm_brk (m_vmmaps m) ->
  spurious_refusal_cfg (alloc_only_cfg false) i m eff.
Proof.
  intros i req m eff Hc Hs Hret.
  assert (Hne : req <> vm_brk (m_vmmaps m)).
  { destruct Hs as (_ & _ & Hlt). intros E. rewrite E in Hlt. lia. }
  assert (Hrf : forall r, refusal_b i m r = bv_eqb r (vm_brk (m_vmmaps m))).
  { intros r. rewrite (ed_brk_refusal_b i req m r Hc).
    destruct Hs as (Hw & Hmin & Hlt). apply ed_brk_move_refusal; [exact Hw | exact Hmin | lia]. }
  split; [exact (ed_brk_family_off i req Hc)|].
  split; [rewrite Hrf, Hret; apply ed_bv_eqb_refl|].
  exists (ed_brk_eff m req req), (with_brk_next m req req), []. split.
  - rewrite (ed_brk_call_spec i req Hc), ed_brk_spec_iff.
    exists req. split; [|split; [reflexivity | split; reflexivity]].
    rewrite (ed_brk_shrink_r_ok m req req Hs), ed_bv_eqb_refl. reflexivity.
  - rewrite Hrf. unfold ed_brk_eff. cbn [eff_ret]. apply ed_bv_eqb_false. exact Hne.
Qed.

(** The query and a request below [min_brk] have no refusal at all. *)
Lemma ed_brk_query_not_refusal : forall i req m r,
  ed_brk_call i req -> w_is0 req = true -> refusal_b i m r = false.
Proof.
  intros i req m r Hc Hw. rewrite (ed_brk_refusal_b i req m r Hc).
  unfold brk_refusal_b. cbv zeta. rewrite Hw. reflexivity.
Qed.

Lemma ed_brk_below_min_not_refusal : forall i req m r,
  ed_brk_call i req ->
  (bv_unsigned req < bv_unsigned (min_brk (m_vmmaps m)))%Z -> refusal_b i m r = false.
Proof.
  intros i req m r Hc Hlt. rewrite (ed_brk_refusal_b i req m r Hc).
  unfold brk_refusal_b. cbv zeta. rewrite (proj2 (Z.ltb_lt _ _) Hlt).
  cbn [negb]. rewrite Bool.andb_false_r. reflexivity.
Qed.

Lemma ed_brk_query_not_spurious : forall i req m eff,
  ed_brk_call i req -> w_is0 req = true ->
  ~ spurious_refusal_cfg (alloc_only_cfg false) i m eff.
Proof.
  intros i req m eff Hc Hw. apply spurious_refusal_not_refusal.
  exact (ed_brk_query_not_refusal i req m _ Hc Hw).
Qed.

Lemma ed_brk_below_min_not_spurious : forall i req m eff,
  ed_brk_call i req ->
  (bv_unsigned req < bv_unsigned (min_brk (m_vmmaps m)))%Z ->
  ~ spurious_refusal_cfg (alloc_only_cfg false) i m eff.
Proof.
  intros i req m eff Hc Hlt. apply spurious_refusal_not_refusal.
  exact (ed_brk_below_min_not_refusal i req m _ Hc Hlt).
Qed.

(* ---- mremap ---- *)

Definition ed_mremap_call (i : SyscallInput) (old old_size new_size flags : word) : Prop :=
  bv_unsigned (in_sysno i) = 216%Z
  /\ in_arg i 0 = old /\ in_arg i 1 = old_size /\ in_arg i 2 = new_size /\ in_arg i 3 = flags.

Definition ed_mremap_arm (m : Model) (old old_size new_size flags : word) : Prop :=
  Z.eqb (bv_unsigned flags) MREMAP_MAYMOVE = true
  /\ Z.eqb (bv_unsigned old mod page_size) 0 = true
  /\ page_align_is0_b new_size = false
  /\ page_align_is0_b old_size = false
  /\ (mremap_source_b (m_vmmaps m) old (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size))) (page_round_up_Z (bv_unsigned old_size))
      && mremap_backing_uniform_b m old (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size)))) = true.

Lemma ed_mremap_call_spec : forall i old old_size new_size flags,
  ed_mremap_call i old old_size new_size flags -> forall m o,
  syscall_spec i m o <-> mremap_spec old old_size new_size flags i m o.
Proof.
  intros i old old_size new_size flags (E & H0 & H1 & H2 & H3) m o. subst.
  unfold syscall_spec, dispatch. rewrite E. reflexivity.
Qed.

Lemma ed_mremap_call_sysno : forall i old old_size new_size flags,
  ed_mremap_call i old old_size new_size flags -> enomem_sysno (bv_unsigned (in_sysno i)).
Proof. intros i old old_size new_size flags (E & _). left. exact E. Qed.

Lemma ed_mremap_old_ne_enomem : forall m old old_size new_size flags,
  ed_mremap_arm m old old_size new_size flags -> old <> errno_ret ENOMEM.
Proof.
  intros m old old_size new_size flags (_ & _ & _ & _ & Hs).
  apply andb_true_iff in Hs as [Hs _]. unfold mremap_source_b in Hs.
  apply andb_true_iff in Hs as [Hs _]. apply andb_true_iff in Hs as [Hs _].
  apply andb_true_iff in Hs as [Hs _]. apply Z.leb_le in Hs.
  exact (ed_below_top_ne_enomem old (m_vmmaps m) _ (ed_nZ_nonneg old_size) Hs).
Qed.

Lemma ed_mremap_fresh_ne_enomem : forall m oZ nZ old old_n dst new_n,
  (0 <= nZ)%Z -> mremap_fresh_b m oZ nZ old old_n dst new_n = true -> dst <> errno_ret ENOMEM.
Proof.
  intros m oZ nZ old old_n dst new_n Hn Hf. unfold mremap_fresh_b in Hf. cbv zeta in Hf.
  apply andb_true_iff in Hf as [Hf _]. apply andb_true_iff in Hf as [Hf _].
  apply andb_true_iff in Hf as [_ Hf]. apply Z.leb_le in Hf.
  exact (ed_below_top_ne_enomem dst (m_vmmaps m) nZ Hn Hf).
Qed.

Lemma ed_mremap_shrink_spec : forall old old_size new_size flags i m eff m' evs,
  ed_mremap_arm m old old_size new_size flags ->
  ((page_round_up_Z (bv_unsigned new_size)) <? (page_round_up_Z (bv_unsigned old_size)))%Z = true ->
  mremap_spec old old_size new_size flags i m (Ok eff m' evs)
  <-> ed_refused m eff m' evs
      \/ (eff = mremap_inplace_effect old (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size))) (Z_to_bv 64 (page_round_up_Z (bv_unsigned new_size))) (page_round_up_Z (bv_unsigned old_size)) (page_round_up_Z (bv_unsigned new_size))
          /\ m' = mremap_model_next m old (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size))) old (Z_to_bv 64 (page_round_up_Z (bv_unsigned new_size))) /\ evs = []).
Proof.
  intros old old_size new_size flags i m eff m' evs (Hfl & Hal & Hn0 & Ho0 & Hsrc) Hlt.
  assert (Heq : ((page_round_up_Z (bv_unsigned old_size)) =? (page_round_up_Z (bv_unsigned new_size)))%Z = false) by (apply Z.eqb_neq; apply Z.ltb_lt in Hlt; lia).
  unfold mremap_spec. ed_spec_tac.
Qed.

Lemma ed_mremap_grow_spec : forall old old_size new_size flags i m eff m' evs,
  ed_mremap_arm m old old_size new_size flags ->
  ((page_round_up_Z (bv_unsigned old_size)) <? (page_round_up_Z (bv_unsigned new_size)))%Z = true ->
  mremap_spec old old_size new_size flags i m (Ok eff m' evs)
  <-> ed_refused m eff m' evs
      \/ (mremap_inplace_grow_b m old (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size))) (Z_to_bv 64 (page_round_up_Z (bv_unsigned new_size))) (page_round_up_Z (bv_unsigned old_size)) (page_round_up_Z (bv_unsigned new_size)) = true
          /\ eff = mremap_inplace_effect old (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size))) (Z_to_bv 64 (page_round_up_Z (bv_unsigned new_size))) (page_round_up_Z (bv_unsigned old_size)) (page_round_up_Z (bv_unsigned new_size))
          /\ m' = mremap_model_next m old (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size))) old (Z_to_bv 64 (page_round_up_Z (bv_unsigned new_size))) /\ evs = [])
      \/ (exists dst, mremap_fresh_b m (page_round_up_Z (bv_unsigned old_size)) (page_round_up_Z (bv_unsigned new_size)) old (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size))) dst (Z_to_bv 64 (page_round_up_Z (bv_unsigned new_size))) = true
          /\ eff = mremap_move_effect old (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size))) dst (page_round_up_Z (bv_unsigned old_size)) (page_round_up_Z (bv_unsigned new_size))
          /\ m' = mremap_model_next m old (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size))) dst (Z_to_bv 64 (page_round_up_Z (bv_unsigned new_size))) /\ evs = []).
Proof.
  intros old old_size new_size flags i m eff m' evs (Hfl & Hal & Hn0 & Ho0 & Hsrc) Hlt.
  apply Z.ltb_lt in Hlt.
  assert (Heq : ((page_round_up_Z (bv_unsigned old_size)) =? (page_round_up_Z (bv_unsigned new_size)))%Z = false) by (apply Z.eqb_neq; lia).
  assert (Hsh : ((page_round_up_Z (bv_unsigned new_size)) <? (page_round_up_Z (bv_unsigned old_size)))%Z = false) by (apply Z.ltb_ge; lia).
  clear Hlt. unfold mremap_spec.
  destruct (mremap_inplace_grow_b m old (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size))) (Z_to_bv 64 (page_round_up_Z (bv_unsigned new_size))) (page_round_up_Z (bv_unsigned old_size)) (page_round_up_Z (bv_unsigned new_size))) eqn:Hip; ed_spec_tac.
Qed.

(** (ii) shrink: the -ENOMEM is always spurious ... *)
Lemma ed_mremap_shrink_enomem_spurious : forall i old old_size new_size flags m eff,
  ed_mremap_call i old old_size new_size flags ->
  ed_mremap_arm m old old_size new_size flags ->
  ((page_round_up_Z (bv_unsigned new_size)) <? (page_round_up_Z (bv_unsigned old_size)))%Z = true ->
  eff_ret eff = errno_ret ENOMEM ->
  spurious_refusal_cfg (alloc_only_cfg false) i m eff.
Proof.
  intros i old old_size new_size flags m eff Hc Ha Hlt Hr.
  apply (ed_spurious_intro i m eff (mremap_inplace_effect old (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size))) (Z_to_bv 64 (page_round_up_Z (bv_unsigned new_size))) (page_round_up_Z (bv_unsigned old_size)) (page_round_up_Z (bv_unsigned new_size)))
           (mremap_model_next m old (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size))) old (Z_to_bv 64 (page_round_up_Z (bv_unsigned new_size)))) []).
  - exact (ed_mremap_call_sysno _ _ _ _ _ Hc).
  - exact Hr.
  - rewrite (ed_mremap_call_spec _ _ _ _ _ Hc), (ed_mremap_shrink_spec _ _ _ _ _ _ _ _ _ Ha Hlt).
    right. split; [reflexivity | split; reflexivity].
  - unfold mremap_inplace_effect. rewrite Hlt. cbn [eff_ret].
    exact (ed_mremap_old_ne_enomem _ _ _ _ _ Ha).
Qed.

(** ... so a kept shrink outcome is the shrink. *)
Lemma ed_mremap_shrink_inversion : forall i old old_size new_size flags m eff m' evs,
  ed_mremap_call i old old_size new_size flags ->
  ed_mremap_arm m old old_size new_size flags ->
  ((page_round_up_Z (bv_unsigned new_size)) <? (page_round_up_Z (bv_unsigned old_size)))%Z = true ->
  syscall_spec i m (Ok eff m' evs) ->
  ~ spurious_refusal_cfg (alloc_only_cfg false) i m eff ->
  eff = mremap_inplace_effect old (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size))) (Z_to_bv 64 (page_round_up_Z (bv_unsigned new_size))) (page_round_up_Z (bv_unsigned old_size)) (page_round_up_Z (bv_unsigned new_size))
  /\ m' = mremap_model_next m old (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size))) old (Z_to_bv 64 (page_round_up_Z (bv_unsigned new_size))) /\ evs = [].
Proof.
  intros i old old_size new_size flags m eff m' evs Hc Ha Hlt Hs Hns.
  rewrite (ed_mremap_call_spec _ _ _ _ _ Hc), (ed_mremap_shrink_spec _ _ _ _ _ _ _ _ _ Ha Hlt) in Hs.
  destruct Hs as [(Heff & _ & _) | Hk]; [exfalso | exact Hk].
  apply Hns. apply (ed_mremap_shrink_enomem_spurious i old old_size new_size flags m eff Hc Ha Hlt).
  rewrite Heff. reflexivity.
Qed.

(** (ii) grow: the -ENOMEM is spurious iff an in-place grow or a fresh
    destination is admissible. *)
Lemma ed_mremap_grow_enomem_spurious_iff : forall i old old_size new_size flags m eff,
  ed_mremap_call i old old_size new_size flags ->
  ed_mremap_arm m old old_size new_size flags ->
  ((page_round_up_Z (bv_unsigned old_size)) <? (page_round_up_Z (bv_unsigned new_size)))%Z = true ->
  eff_ret eff = errno_ret ENOMEM ->
  spurious_refusal_cfg (alloc_only_cfg false) i m eff
  <-> mremap_inplace_grow_b m old (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size))) (Z_to_bv 64 (page_round_up_Z (bv_unsigned new_size))) (page_round_up_Z (bv_unsigned old_size)) (page_round_up_Z (bv_unsigned new_size)) = true
      \/ exists dst, mremap_fresh_b m (page_round_up_Z (bv_unsigned old_size)) (page_round_up_Z (bv_unsigned new_size)) old (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size))) dst (Z_to_bv 64 (page_round_up_Z (bv_unsigned new_size))) = true.
Proof.
  intros i old old_size new_size flags m eff Hc Ha Hlt Hr.
  pose proof (ed_mremap_call_sysno _ _ _ _ _ Hc) as Hno.
  assert (Hsh : ((page_round_up_Z (bv_unsigned new_size)) <? (page_round_up_Z (bv_unsigned old_size)))%Z = false) by (apply Z.ltb_ge; apply Z.ltb_lt in Hlt; lia).
  split.
  - intros (_ & _ & (eff2 & m2 & evs2 & Hs & Hnr)).
    rewrite (ed_mremap_call_spec _ _ _ _ _ Hc), (ed_mremap_grow_spec _ _ _ _ _ _ _ _ _ Ha Hlt) in Hs.
    rewrite (ed_refusal_b i m _ Hno) in Hnr.
    destruct Hs as [(-> & _ & _) | [(Hip & _) | (dst & Hf & _)]].
    + cbn [eff_ret] in Hnr. rewrite ed_bv_eqb_refl in Hnr. discriminate Hnr.
    + left. exact Hip.
    + right. exists dst. exact Hf.
  - intros [Hip | (dst & Hf)].
    + apply (ed_spurious_intro i m eff (mremap_inplace_effect old (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size))) (Z_to_bv 64 (page_round_up_Z (bv_unsigned new_size))) (page_round_up_Z (bv_unsigned old_size)) (page_round_up_Z (bv_unsigned new_size)))
               (mremap_model_next m old (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size))) old (Z_to_bv 64 (page_round_up_Z (bv_unsigned new_size)))) [] Hno Hr).
      * rewrite (ed_mremap_call_spec _ _ _ _ _ Hc), (ed_mremap_grow_spec _ _ _ _ _ _ _ _ _ Ha Hlt).
        right. left. split; [exact Hip | split; [reflexivity | split; reflexivity]].
      * unfold mremap_inplace_effect. rewrite Hsh. cbn [eff_ret].
        exact (ed_mremap_old_ne_enomem _ _ _ _ _ Ha).
    + apply (ed_spurious_intro i m eff (mremap_move_effect old (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size))) dst (page_round_up_Z (bv_unsigned old_size)) (page_round_up_Z (bv_unsigned new_size)))
               (mremap_model_next m old (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size))) dst (Z_to_bv 64 (page_round_up_Z (bv_unsigned new_size)))) [] Hno Hr).
      * rewrite (ed_mremap_call_spec _ _ _ _ _ Hc), (ed_mremap_grow_spec _ _ _ _ _ _ _ _ _ Ha Hlt).
        right. right. exists dst. split; [exact Hf | split; [reflexivity | split; reflexivity]].
      * unfold mremap_move_effect. cbn [eff_ret].
        exact (ed_mremap_fresh_ne_enomem _ _ _ _ _ _ _ (ed_nZ_nonneg new_size) Hf).
Qed.

(** A grow with neither available forces the -ENOMEM, which is kept. *)
Lemma ed_mremap_grow_forced : forall i old old_size new_size flags m,
  ed_mremap_call i old old_size new_size flags ->
  ed_mremap_arm m old old_size new_size flags ->
  ((page_round_up_Z (bv_unsigned old_size)) <? (page_round_up_Z (bv_unsigned new_size)))%Z = true ->
  mremap_inplace_grow_b m old (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size))) (Z_to_bv 64 (page_round_up_Z (bv_unsigned new_size))) (page_round_up_Z (bv_unsigned old_size)) (page_round_up_Z (bv_unsigned new_size)) = false ->
  (forall dst, mremap_fresh_b m (page_round_up_Z (bv_unsigned old_size)) (page_round_up_Z (bv_unsigned new_size)) old (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size))) dst (Z_to_bv 64 (page_round_up_Z (bv_unsigned new_size))) = false) ->
  syscall_spec i m (Ok (mkEffect (errno_ret ENOMEM) [] []) m [])
  /\ ~ spurious_refusal_cfg (alloc_only_cfg false) i m (mkEffect (errno_ret ENOMEM) [] []).
Proof.
  intros i old old_size new_size flags m Hc Ha Hlt Hip Hf. split.
  - rewrite (ed_mremap_call_spec _ _ _ _ _ Hc), (ed_mremap_grow_spec _ _ _ _ _ _ _ _ _ Ha Hlt).
    left. exact (ed_refused_intro m).
  - intros Hsp. apply (ed_mremap_grow_enomem_spurious_iff i old old_size new_size flags m _ Hc Ha Hlt)
      in Hsp; [|reflexivity].
    destruct Hsp as [H | (dst & H)]; [rewrite Hip in H | rewrite Hf in H]; discriminate H.
Qed.

(** A kept grow outcome is an in-place grow, a move, or the forced -ENOMEM. *)
Lemma ed_mremap_grow_inversion : forall i old old_size new_size flags m eff m' evs,
  ed_mremap_call i old old_size new_size flags ->
  ed_mremap_arm m old old_size new_size flags ->
  ((page_round_up_Z (bv_unsigned old_size)) <? (page_round_up_Z (bv_unsigned new_size)))%Z = true ->
  syscall_spec i m (Ok eff m' evs) ->
  ~ spurious_refusal_cfg (alloc_only_cfg false) i m eff ->
  (mremap_inplace_grow_b m old (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size))) (Z_to_bv 64 (page_round_up_Z (bv_unsigned new_size))) (page_round_up_Z (bv_unsigned old_size)) (page_round_up_Z (bv_unsigned new_size)) = true
   /\ eff = mremap_inplace_effect old (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size))) (Z_to_bv 64 (page_round_up_Z (bv_unsigned new_size))) (page_round_up_Z (bv_unsigned old_size)) (page_round_up_Z (bv_unsigned new_size))
   /\ m' = mremap_model_next m old (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size))) old (Z_to_bv 64 (page_round_up_Z (bv_unsigned new_size))) /\ evs = [])
  \/ (exists dst, mremap_fresh_b m (page_round_up_Z (bv_unsigned old_size)) (page_round_up_Z (bv_unsigned new_size)) old (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size))) dst (Z_to_bv 64 (page_round_up_Z (bv_unsigned new_size))) = true
      /\ eff = mremap_move_effect old (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size))) dst (page_round_up_Z (bv_unsigned old_size)) (page_round_up_Z (bv_unsigned new_size))
      /\ m' = mremap_model_next m old (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size))) dst (Z_to_bv 64 (page_round_up_Z (bv_unsigned new_size))) /\ evs = [])
  \/ (ed_refused m eff m' evs
      /\ mremap_inplace_grow_b m old (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size))) (Z_to_bv 64 (page_round_up_Z (bv_unsigned new_size))) (page_round_up_Z (bv_unsigned old_size)) (page_round_up_Z (bv_unsigned new_size)) = false
      /\ forall dst, mremap_fresh_b m (page_round_up_Z (bv_unsigned old_size)) (page_round_up_Z (bv_unsigned new_size)) old (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size))) dst (Z_to_bv 64 (page_round_up_Z (bv_unsigned new_size))) = false).
Proof.
  intros i old old_size new_size flags m eff m' evs Hc Ha Hlt Hs Hns.
  rewrite (ed_mremap_call_spec _ _ _ _ _ Hc), (ed_mremap_grow_spec _ _ _ _ _ _ _ _ _ Ha Hlt) in Hs.
  destruct Hs as [Hrf | [Hip | Hmv]]; [| left; exact Hip | right; left; exact Hmv].
  right. right. split; [exact Hrf|].
  assert (Hno : ~ (mremap_inplace_grow_b m old (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size))) (Z_to_bv 64 (page_round_up_Z (bv_unsigned new_size))) (page_round_up_Z (bv_unsigned old_size)) (page_round_up_Z (bv_unsigned new_size)) = true
                   \/ exists dst, mremap_fresh_b m (page_round_up_Z (bv_unsigned old_size)) (page_round_up_Z (bv_unsigned new_size)) old (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size))) dst (Z_to_bv 64 (page_round_up_Z (bv_unsigned new_size))) = true)).
  { intros Hav. apply Hns.
    apply (ed_mremap_grow_enomem_spurious_iff i old old_size new_size flags m eff Hc Ha Hlt);
      [exact (ed_refused_ret m eff m' evs Hrf) | exact Hav]. }
  split.
  - destruct (mremap_inplace_grow_b m old (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size))) (Z_to_bv 64 (page_round_up_Z (bv_unsigned new_size))) (page_round_up_Z (bv_unsigned old_size)) (page_round_up_Z (bv_unsigned new_size))) eqn:E; [|reflexivity].
    exfalso. apply Hno. left. reflexivity.
  - intros dst. destruct (mremap_fresh_b m (page_round_up_Z (bv_unsigned old_size)) (page_round_up_Z (bv_unsigned new_size)) old (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size))) dst (Z_to_bv 64 (page_round_up_Z (bv_unsigned new_size)))) eqn:E; [|reflexivity].
    exfalso. apply Hno. right. exists dst. exact E.
Qed.
