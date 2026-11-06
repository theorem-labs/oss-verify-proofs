(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Scfg Require Import Fcfg EdDefs.
Import ListNotations.
Open Scope sys_scope.

Lemma scfg_spec_222 : forall i m o,
  bv_unsigned (in_sysno i) = 222%Z ->
  syscall_spec i m o <->
  mmap_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) i m o.
Proof. intros i m o E; unfold syscall_spec, dispatch; rewrite E; reflexivity. Qed.

Lemma scfg_spec_226 : forall i m o,
  bv_unsigned (in_sysno i) = 226%Z ->
  syscall_spec i m o <-> mprotect_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) i m o.
Proof. intros i m o E; unfold syscall_spec, dispatch; rewrite E; reflexivity. Qed.

Lemma errno_ret_ENOMEM_unsigned : bv_unsigned (errno_ret ENOMEM) = (two_pow_64 - 12)%Z.
Proof. vm_compute. reflexivity. Qed.

Lemma bv_eqb_enomem_below : forall r : word,
  (bv_unsigned r < two_pow_64 - 4095)%Z -> bv_eqb r (errno_ret ENOMEM) = false.
Proof.
  intros r H. destruct (bv_eqb r (errno_ret ENOMEM)) eqn:Eb; [|reflexivity].
  apply bv_eqb_eq in Eb. subst r. rewrite errno_ret_ENOMEM_unsigned in H. lia.
Qed.

Lemma refusal_b_222 : forall i m r,
  bv_unsigned (in_sysno i) = 222%Z -> refusal_b i m r = bv_eqb r (errno_ret ENOMEM).
Proof.
  intros i m r E. unfold refusal_b. cbv zeta. rewrite E.
  change (ret_in_errnos mmap_errnos r = bv_eqb r (errno_ret ENOMEM)).
  unfold ret_in_errnos, mmap_errnos. cbn [existsb]. apply orb_false_r.
Qed.

Lemma refusal_b_226 : forall i m r,
  bv_unsigned (in_sysno i) = 226%Z -> refusal_b i m r = bv_eqb r (errno_ret ENOMEM).
Proof.
  intros i m r E. unfold refusal_b. cbv zeta. rewrite E.
  change (ret_in_errnos mprotect_errnos r = bv_eqb r (errno_ret ENOMEM)).
  unfold ret_in_errnos, mprotect_errnos. cbn [existsb]. apply orb_false_r.
Qed.

Lemma refusal_b_222_enomem : forall i m,
  bv_unsigned (in_sysno i) = 222%Z -> refusal_b i m (errno_ret ENOMEM) = true.
Proof. intros i m E. rewrite refusal_b_222 by exact E. apply bv_eqb_eq. reflexivity. Qed.

Lemma refusal_b_226_enomem : forall i m,
  bv_unsigned (in_sysno i) = 226%Z -> refusal_b i m (errno_ret ENOMEM) = true.
Proof. intros i m E. rewrite refusal_b_226 by exact E. apply bv_eqb_eq. reflexivity. Qed.

Lemma refusal_b_222_below : forall i m r,
  bv_unsigned (in_sysno i) = 222%Z ->
  (bv_unsigned r < two_pow_64 - 4095)%Z -> refusal_b i m r = false.
Proof. intros i m r E H. rewrite refusal_b_222 by exact E. apply bv_eqb_enomem_below, H. Qed.

Lemma refusal_b_226_below : forall i m r,
  bv_unsigned (in_sysno i) = 226%Z ->
  (bv_unsigned r < two_pow_64 - 4095)%Z -> refusal_b i m r = false.
Proof. intros i m r E H. rewrite refusal_b_226 by exact E. apply bv_eqb_enomem_below, H. Qed.

Lemma refusal_b_222_eexist : forall i m,
  bv_unsigned (in_sysno i) = 222%Z -> refusal_b i m (errno_ret EEXIST) = false.
Proof. intros i m E. rewrite refusal_b_222 by exact E. vm_compute. reflexivity. Qed.

Lemma refusal_b_222_placed : forall i m (a : word) h nZ,
  bv_unsigned (in_sysno i) = 222%Z ->
  (0 <= nZ)%Z -> (bv_unsigned a + nZ <= alloc_top h)%Z -> refusal_b i m a = false.
Proof.
  intros i m a h nZ E Hn Ha. apply refusal_b_222_below; [exact E|].
  pose proof (alloc_top_room h). unfold stack_max_size, two_pow_64 in *. lia.
Qed.

Lemma alloc_222 : forall i, bv_unsigned (in_sysno i) = 222%Z ->
  In (bv_unsigned (in_sysno i)) alloc_mark_sysnos.
Proof. intros i E. rewrite E. right. right. left. reflexivity. Qed.

Lemma alloc_226 : forall i, bv_unsigned (in_sysno i) = 226%Z ->
  In (bv_unsigned (in_sysno i)) alloc_mark_sysnos.
Proof. intros i E. rewrite E. right. right. right. left. reflexivity. Qed.

Lemma nonspur_cases : forall (b : bool) i m eff,
  In (bv_unsigned (in_sysno i)) alloc_mark_sysnos ->
  (b = false -> exists eff' m' evs',
      syscall_spec i m (Ok eff' m' evs') /\ refusal_b i m (eff_ret eff') = false) ->
  (b = true -> forall eff' m' evs',
      syscall_spec i m (Ok eff' m' evs') -> refusal_b i m (eff_ret eff') = true) ->
  (~ spurious_refusal_cfg fcfg i m eff <-> (refusal_b i m (eff_ret eff) = true -> b = true)).
Proof.
  intros [|] i m eff Ha Hg Hf.
  - split; [intros _ _; reflexivity|]. intros _. apply fcfg_forced_nonspur, Hf. reflexivity.
  - split.
    + intros Hns Hr. exfalso. destruct (Hg eq_refl) as (eff' & m' & evs' & Hs & Hr').
      apply Hns. split; [exact (fcfg_family_off i Ha)|]. split; [exact Hr|].
      exists eff', m', evs'. split; assumption.
    + intros H. apply fcfg_nonref_nonspur.
      destruct (refusal_b i m (eff_ret eff)); [discriminate (H eq_refl)|reflexivity].
Qed.

Lemma nonspur_of_grant : forall i m eff,
  In (bv_unsigned (in_sysno i)) alloc_mark_sysnos ->
  (exists eff' m' evs',
      syscall_spec i m (Ok eff' m' evs') /\ refusal_b i m (eff_ret eff') = false) ->
  (~ spurious_refusal_cfg fcfg i m eff <-> refusal_b i m (eff_ret eff) = false).
Proof.
  intros i m eff Ha Hg.
  etransitivity;
    [exact (nonspur_cases false i m eff Ha (fun _ => Hg) (fun E => False_ind _ (diff_false_true E)))|].
  destruct (refusal_b i m (eff_ret eff)); split; intros H.
  - discriminate (H eq_refl).
  - discriminate H.
  - reflexivity.
  - intros H'. exact H'.
Qed.

Lemma nonspur_refusal_iff : forall (b : bool) i m eff,
  (~ spurious_refusal_cfg fcfg i m eff <-> (refusal_b i m (eff_ret eff) = true -> b = true)) ->
  refusal_b i m (eff_ret eff) = true ->
  (~ spurious_refusal_cfg fcfg i m eff <-> b = true).
Proof.
  intros b i m eff H Hr. split.
  - intros H'. exact (proj1 H H' Hr).
  - intros H'. apply (proj2 H). intros _. exact H'.
Qed.

Lemma bind_ok_nil {A B} : forall (c : Sys A) (k : A -> Sys B) i m x m1 y m2 evs,
  c i m (Ok x m1 []) -> k x i m1 (Ok y m2 evs) -> bind c k i m (Ok y m2 evs).
Proof. intros c k i m x m1 y m2 evs H1 H2. exists x, m1, [], evs. auto. Qed.

Lemma errno_bind_inv {B} : forall es (k : Z -> Sys B) i m y m2 evs,
  bind (errno_from es) k i m (Ok y m2 evs) -> exists e, In e es /\ k e i m (Ok y m2 evs).
Proof.
  intros es k i m y m2 evs (x & m1 & evs1 & evs2 & (e & He & Ee) & Hk & ->).
  injection Ee as -> -> ->. exists e. split; [exact He|exact Hk].
Qed.

Lemma choose_bind_inv {A B} : forall (P : A -> Prop) (k : A -> Sys B) i m y m2 evs,
  bind (choose P) k i m (Ok y m2 evs) -> exists x, P x /\ k x i m (Ok y m2 evs).
Proof.
  intros P k i m y m2 evs (x & m1 & evs1 & evs2 & (x' & Hx & Ee) & Hk & ->).
  injection Ee as -> -> ->. exists x'. split; [exact Hx|exact Hk].
Qed.

Lemma modify_bind_inv {B} : forall f (k : unit -> Sys B) i m y m2 evs,
  bind (modify f) k i m (Ok y m2 evs) -> k tt i (f m) (Ok y m2 evs).
Proof.
  intros f k i m y m2 evs (x & m1 & evs1 & evs2 & Ee & Hk & ->).
  injection Ee as -> -> ->. exact Hk.
Qed.

Lemma pure_inv {A} : forall (x y : A) i m m2 evs,
  pure x i m (Ok y m2 evs) -> y = x /\ m2 = m /\ evs = [].
Proof. intros x y i m m2 evs Ee. injection Ee as -> -> ->. auto. Qed.

Lemma err_ret_inv : forall e i m eff m' evs,
  err_ret e i m (Ok eff m' evs) -> eff = mkEffect (errno_ret e) [] [] /\ m' = m /\ evs = [].
Proof. intros e i m eff m' evs H. exact (pure_inv _ _ i m m' evs H). Qed.

Lemma enomem_arm_refusal : forall i m eff m' evs,
  bv_unsigned (in_sysno i) = 222%Z ->
  (e <- errno_from mmap_errnos ;; err_ret e) i m (Ok eff m' evs) ->
  refusal_b i m (eff_ret eff) = true.
Proof.
  intros i m eff m' evs E Hs. apply errno_bind_inv in Hs as (e & He & Hs).
  apply err_ret_inv in Hs as (-> & _ & _). destruct He as [<-|[]].
  apply refusal_b_222_enomem, E.
Qed.

Lemma enomem_arm_refusal_226 : forall i m eff m' evs,
  bv_unsigned (in_sysno i) = 226%Z ->
  (e <- errno_from mprotect_errnos ;; err_ret e) i m (Ok eff m' evs) ->
  refusal_b i m (eff_ret eff) = true.
Proof.
  intros i m eff m' evs E Hs. apply errno_bind_inv in Hs as (e & He & Hs).
  apply err_ret_inv in Hs as (-> & _ & _). destruct He as [<-|[]].
  apply refusal_b_226_enomem, E.
Qed.

Lemma destroy_arm_refusal : forall i m eff m' evs (f : Model -> Model) us,
  bv_unsigned (in_sysno i) = 222%Z ->
  (e <- errno_from mmap_errnos ;; modify f ;; pure (mkEffectU (errno_ret e) [] [] us [] []))
    i m (Ok eff m' evs) ->
  refusal_b i m (eff_ret eff) = true.
Proof.
  intros i m eff m' evs f us E Hs. apply errno_bind_inv in Hs as (e & He & Hs).
  apply modify_bind_inv in Hs. apply pure_inv in Hs as (-> & _ & _).
  destruct He as [<-|[]]. apply refusal_b_222_enomem, E.
Qed.

Lemma len_page_pos : forall len : word,
  w_is0 len = false -> (0 < page_round_up_Z (bv_unsigned len))%Z.
Proof.
  intros len H. apply w_is0_false_pos in H. unfold page_round_up_Z, page_size.
  pose proof (Z.div_mod (bv_unsigned len + 4096 - 1) 4096 ltac:(lia)).
  pose proof (Z.mod_pos_bound (bv_unsigned len + 4096 - 1) 4096 ltac:(lia)). lia.
Qed.

Lemma fixed_no_overflow : forall (addr : word) nZ h,
  (bv_unsigned addr + nZ <= alloc_top h)%Z ->
  (two_pow_64 <=? bv_unsigned addr + nZ)%Z = false.
Proof.
  intros addr nZ h H. apply Z.leb_gt. pose proof (alloc_top_lt h). lia.
Qed.

Ltac gates :=
  repeat match goal with
  | H : ?b = true |- context [?b] => progress rewrite H
  | H : ?b = false |- context [?b] => progress rewrite H
  end; cbn [negb andb orb].

Ltac gates_in Hs := revert Hs; gates; intros Hs.

Local Lemma region_free_app : forall l1 l2 lo n,
  region_free (l1 ++ l2) lo n = region_free l1 lo n && region_free l2 lo n.
Proof.
  induction l1 as [|[a s] l1 IH]; intros l2 lo n; cbn [app region_free]; [reflexivity|].
  rewrite IH, andb_assoc. reflexivity.
Qed.

Lemma region_free_not_contained : forall maps lo n,
  (0 < bv_unsigned n)%Z -> region_free maps lo n = true -> map_contains maps lo n = false.
Proof.
  intros maps lo n Hn Hf. unfold map_contains.
  destruct (existsb _ maps) eqn:Ex; [|reflexivity].
  apply existsb_exists in Ex as ([a sz] & Hin & Hc). cbn [fst snd] in Hc.
  apply andb_true_iff in Hc as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  pose proof (region_free_In _ _ _ _ _ Hf Hin) as Hno. unfold iv_overlap in Hno.
  apply andb_false_iff in Hno as [N|N]; apply Z.ltb_ge in N; lia.
Qed.

Lemma fixed_n_pos : forall (addr len : word) h,
  w_is0 len = false ->
  (bv_unsigned addr + page_round_up_Z (bv_unsigned len) <= alloc_top h)%Z ->
  (0 < bv_unsigned (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))))%Z.
Proof.
  intros addr len h Hl Hc. pose proof (len_page_pos _ Hl). pose proof (alloc_top_lt h).
  pose proof (bv_unsigned_in_range 64 addr).
  rewrite Z_to_bv_unsigned, bv_wrap_small; [lia|]. unfold bv_modulus, two_pow_64 in *. lia.
Qed.

Ltac fixed_prep Hlen Hce Hal Hpos :=
  pose proof (len_page_pos _ Hlen);
  pose proof (fixed_no_overflow _ _ _ Hce);
  pose proof (proj2 (Z.leb_le _ _) Hce);
  pose proof (proj2 (Z.eqb_eq _ _) Hal);
  pose proof (proj2 (Z.ltb_lt _ _) Hpos).

Ltac free_derive Hrf Hlen Hce :=
  let Hrr := fresh "Hrr" in let Hrm := fresh "Hrm" in
  pose proof Hrf as Hrr; rewrite region_free_app in Hrr; apply andb_true_iff in Hrr as [Hrr Hrm];
  pose proof (region_free_not_contained _ _ _ (fixed_n_pos _ _ _ Hlen Hce) Hrm); clear Hrm.

(* hint-placed rw mmap *)

Lemma mmap_grant_refusable_false_grant : forall i m,
  bv_unsigned (in_sysno i) = 222%Z ->
  mmap_off_aligned_b (in_arg i 5) = true -> mmap_anon_b (in_arg i 3) = true ->
  w_is0 (in_arg i 1) = false ->
  mmap_modeled_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = true ->
  mmap_grant_refusable (in_arg i 3) m (page_round_up_Z (bv_unsigned (in_arg i 1))) = false ->
  exists eff m' evs, syscall_spec i m (Ok eff m' evs) /\ refusal_b i m (eff_ret eff) = false.
Proof.
  intros i m E Hoff Han Hlen Hmod Hr.
  pose proof (len_page_pos _ Hlen) as Hn.
  unfold mmap_grant_refusable in Hr. apply orb_false_iff in Hr as [Hb Hg].
  apply negb_false_iff in Hb. apply negb_false_iff in Hg.
  apply vm_gap_available_iff in Hg as (a & HP).
  pose proof (conj HP Hb) as HPb. clear HP Hb.
  eexists _, _, _. split.
  - apply (proj2 (scfg_spec_222 i m _ E)). unfold mmap_spec. gates.
    apply alt_r. apply (proj2 (bind_get_model _ _ _ _)). cbv beta zeta.
    destruct HPb as ((A1 & A2 & A3 & A4) & Hb).
    eapply bind_ok_nil; [apply (choose_ok _ a); exact (conj A1 (conj A2 (conj A3 (conj A4 Hb))))|].
    eapply bind_ok_nil; [apply modify_ok|]. apply pure_ok.
  - destruct HPb as ((_ & _ & A3 & _) & _).
    cbn [eff_ret]. eapply refusal_b_222_placed; [exact E| |exact A3]. lia.
Qed.

Lemma mmap_grant_refusable_true_forced : forall i m,
  bv_unsigned (in_sysno i) = 222%Z ->
  mmap_off_aligned_b (in_arg i 5) = true -> mmap_anon_b (in_arg i 3) = true ->
  w_is0 (in_arg i 1) = false ->
  mmap_modeled_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = true ->
  mmap_grant_refusable (in_arg i 3) m (page_round_up_Z (bv_unsigned (in_arg i 1))) = true ->
  forall eff m' evs, syscall_spec i m (Ok eff m' evs) -> refusal_b i m (eff_ret eff) = true.
Proof.
  intros i m E Hoff Han Hlen Hmod Hr eff m' evs Hs.
  apply (proj1 (scfg_spec_222 _ _ _ E)) in Hs. unfold mmap_spec in Hs. gates_in Hs.
  unfold alt in Hs. destruct Hs as [Hs|Hs]; [exact (enomem_arm_refusal _ _ _ _ _ E Hs)|].
  apply (proj1 (bind_get_model _ _ _ _)) in Hs. cbv beta zeta in Hs.
  apply choose_bind_inv in Hs as (a & (A1 & A2 & A3 & A4 & A5) & _).
  exfalso. unfold mmap_grant_refusable in Hr. rewrite A5 in Hr. cbn [negb orb] in Hr.
  rewrite (proj2 (vm_gap_available_iff _ _) (ex_intro _ a (conj A1 (conj A2 (conj A3 A4))))) in Hr.
  cbn [negb] in Hr. discriminate Hr.
Qed.

Lemma mmap_grant_nonspur : forall i m eff,
  bv_unsigned (in_sysno i) = 222%Z ->
  mmap_off_aligned_b (in_arg i 5) = true -> mmap_anon_b (in_arg i 3) = true ->
  w_is0 (in_arg i 1) = false ->
  mmap_modeled_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = true ->
  (~ spurious_refusal_cfg fcfg i m eff <->
   (refusal_b i m (eff_ret eff) = true ->
    mmap_grant_refusable (in_arg i 3) m (page_round_up_Z (bv_unsigned (in_arg i 1))) = true)).
Proof.
  intros i m eff E Hoff Han Hlen Hmod. apply (nonspur_cases _ i m eff (alloc_222 i E)).
  - apply mmap_grant_refusable_false_grant; assumption.
  - apply mmap_grant_refusable_true_forced; assumption.
Qed.

Lemma mmap_grant_refusal_nonspur_iff : forall i m eff,
  bv_unsigned (in_sysno i) = 222%Z ->
  mmap_off_aligned_b (in_arg i 5) = true -> mmap_anon_b (in_arg i 3) = true ->
  w_is0 (in_arg i 1) = false ->
  mmap_modeled_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = true ->
  refusal_b i m (eff_ret eff) = true ->
  (~ spurious_refusal_cfg fcfg i m eff <->
   mmap_grant_refusable (in_arg i 3) m (page_round_up_Z (bv_unsigned (in_arg i 1))) = true).
Proof. intros i m eff E Hoff Han Hlen Hmod. apply nonspur_refusal_iff, mmap_grant_nonspur; assumption. Qed.

(* PROT_NONE reserve *)

Lemma mmap_reserve_refusable_false_grant : forall i m,
  bv_unsigned (in_sysno i) = 222%Z ->
  mmap_off_aligned_b (in_arg i 5) = true -> mmap_anon_b (in_arg i 3) = true ->
  w_is0 (in_arg i 1) = false ->
  mmap_modeled_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_noaccess_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = true ->
  mmap_reserve_refusable m (page_round_up_Z (bv_unsigned (in_arg i 1))) = false ->
  exists eff m' evs, syscall_spec i m (Ok eff m' evs) /\ refusal_b i m (eff_ret eff) = false.
Proof.
  intros i m E Hoff Han Hlen Hmod Hna Hr.
  pose proof (len_page_pos _ Hlen) as Hn.
  unfold mmap_reserve_refusable in Hr. apply negb_false_iff in Hr.
  apply vm_gap_available_iff in Hr as (a & HP).
  eexists _, _, _. split.
  - apply (proj2 (scfg_spec_222 i m _ E)). unfold mmap_spec. gates.
    apply alt_r. apply (proj2 (bind_get_model _ _ _ _)). cbv beta zeta.
    eapply bind_ok_nil; [apply (choose_ok _ a); exact HP|].
    eapply bind_ok_nil; [apply modify_ok|]. apply pure_ok.
  - destruct HP as (_ & _ & A3 & _).
    cbn [eff_ret]. eapply refusal_b_222_placed; [exact E| |exact A3]. lia.
Qed.

Lemma mmap_reserve_refusable_true_forced : forall i m,
  bv_unsigned (in_sysno i) = 222%Z ->
  mmap_off_aligned_b (in_arg i 5) = true -> mmap_anon_b (in_arg i 3) = true ->
  w_is0 (in_arg i 1) = false ->
  mmap_modeled_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_noaccess_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = true ->
  mmap_reserve_refusable m (page_round_up_Z (bv_unsigned (in_arg i 1))) = true ->
  forall eff m' evs, syscall_spec i m (Ok eff m' evs) -> refusal_b i m (eff_ret eff) = true.
Proof.
  intros i m E Hoff Han Hlen Hmod Hna Hr eff m' evs Hs.
  apply (proj1 (scfg_spec_222 _ _ _ E)) in Hs. unfold mmap_spec in Hs. gates_in Hs.
  unfold alt in Hs. destruct Hs as [Hs|Hs]; [exact (enomem_arm_refusal _ _ _ _ _ E Hs)|].
  apply (proj1 (bind_get_model _ _ _ _)) in Hs. cbv beta zeta in Hs.
  apply choose_bind_inv in Hs as (a & (A1 & A2 & A3 & A4) & _).
  exfalso. unfold mmap_reserve_refusable in Hr.
  rewrite (proj2 (vm_gap_available_iff _ _) (ex_intro _ a (conj A1 (conj A2 (conj A3 A4))))) in Hr.
  cbn [negb] in Hr. discriminate Hr.
Qed.

Lemma mmap_reserve_nonspur : forall i m eff,
  bv_unsigned (in_sysno i) = 222%Z ->
  mmap_off_aligned_b (in_arg i 5) = true -> mmap_anon_b (in_arg i 3) = true ->
  w_is0 (in_arg i 1) = false ->
  mmap_modeled_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_noaccess_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = true ->
  (~ spurious_refusal_cfg fcfg i m eff <->
   (refusal_b i m (eff_ret eff) = true ->
    mmap_reserve_refusable m (page_round_up_Z (bv_unsigned (in_arg i 1))) = true)).
Proof.
  intros i m eff E Hoff Han Hlen Hmod Hna. apply (nonspur_cases _ i m eff (alloc_222 i E)).
  - apply mmap_reserve_refusable_false_grant; assumption.
  - apply mmap_reserve_refusable_true_forced; assumption.
Qed.

Lemma mmap_reserve_refusal_nonspur_iff : forall i m eff,
  bv_unsigned (in_sysno i) = 222%Z ->
  mmap_off_aligned_b (in_arg i 5) = true -> mmap_anon_b (in_arg i 3) = true ->
  w_is0 (in_arg i 1) = false ->
  mmap_modeled_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_noaccess_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = true ->
  refusal_b i m (eff_ret eff) = true ->
  (~ spurious_refusal_cfg fcfg i m eff <->
   mmap_reserve_refusable m (page_round_up_Z (bv_unsigned (in_arg i 1))) = true).
Proof. intros i m eff E Hoff Han Hlen Hmod Hna. apply nonspur_refusal_iff, mmap_reserve_nonspur; assumption. Qed.

(* MAP_FIXED PROT_NONE over an existing mapping (never refusable) *)

Lemma mmap_fixed_none_commit_grant : forall i m,
  bv_unsigned (in_sysno i) = 222%Z ->
  mmap_off_aligned_b (in_arg i 5) = true -> mmap_anon_b (in_arg i 3) = true ->
  w_is0 (in_arg i 1) = false ->
  mmap_modeled_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_noaccess_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_fixed_noaccess_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = true ->
  (bv_unsigned (in_arg i 0) + page_round_up_Z (bv_unsigned (in_arg i 1)) <= alloc_top (m_vmmaps m))%Z ->
  (bv_unsigned (in_arg i 0) mod page_size = 0)%Z ->
  (0 < bv_unsigned (in_arg i 0))%Z ->
  region_free (vm_reserved (m_vmmaps m)) (in_arg i 0)
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1)))) = true ->
  map_contains (vm_maps (m_vmmaps m)) (in_arg i 0)
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1)))) = true ->
  exists eff m' evs, syscall_spec i m (Ok eff m' evs) /\ refusal_b i m (eff_ret eff) = false.
Proof.
  intros i m E Hoff Han Hlen Hmod Hna Hfx Hce Hal Hpos Hrf Hmc.
  pose proof (len_page_pos _ Hlen) as Hn.
  pose proof (fixed_no_overflow _ _ _ Hce) as Hov.
  pose proof (proj2 (Z.leb_le _ _) Hce) as Hce'.
  pose proof (proj2 (Z.eqb_eq _ _) Hal) as Hal'.
  pose proof (proj2 (Z.ltb_lt _ _) Hpos) as Hpos'.
  eexists _, _, _. split.
  - apply (proj2 (scfg_spec_222 i m _ E)). unfold mmap_spec. gates. cbv zeta. gates.
    apply (proj2 (bind_get_model _ _ _ _)). cbv beta zeta. gates.
    apply alt_r, alt_l. eapply bind_ok_nil; [apply modify_ok|]. apply pure_ok.
  - cbn [eff_ret]. eapply refusal_b_222_placed; [exact E| |exact Hce]. lia.
Qed.

Lemma mmap_fixed_none_commit_nonspur : forall i m eff,
  bv_unsigned (in_sysno i) = 222%Z ->
  mmap_off_aligned_b (in_arg i 5) = true -> mmap_anon_b (in_arg i 3) = true ->
  w_is0 (in_arg i 1) = false ->
  mmap_modeled_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_noaccess_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_fixed_noaccess_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = true ->
  (bv_unsigned (in_arg i 0) + page_round_up_Z (bv_unsigned (in_arg i 1)) <= alloc_top (m_vmmaps m))%Z ->
  (bv_unsigned (in_arg i 0) mod page_size = 0)%Z ->
  (0 < bv_unsigned (in_arg i 0))%Z ->
  region_free (vm_reserved (m_vmmaps m)) (in_arg i 0)
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1)))) = true ->
  map_contains (vm_maps (m_vmmaps m)) (in_arg i 0)
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1)))) = true ->
  (~ spurious_refusal_cfg fcfg i m eff <-> refusal_b i m (eff_ret eff) = false).
Proof.
  intros i m eff E Hoff Han Hlen Hmod Hna Hfx Hce Hal Hpos Hrf Hmc.
  apply (nonspur_of_grant i m eff (alloc_222 i E)).
  apply mmap_fixed_none_commit_grant; assumption.
Qed.

(* mprotect PROT_NONE -> rw over a reserved range *)

Lemma mprotect_refusable_false_grant : forall i m,
  bv_unsigned (in_sysno i) = 226%Z ->
  mprotect_grows_conflict_b (in_arg i 2) = false ->
  (bv_unsigned (in_arg i 0) mod page_size = 0)%Z ->
  w_is0 (in_arg i 1) = false ->
  (bv_unsigned (in_arg i 0) + page_round_up_Z (bv_unsigned (in_arg i 1)) < two_pow_64)%Z ->
  mprotect_modeled_b (in_arg i 2) = true ->
  map_contains (vm_noaccess (m_vmmaps m)) (in_arg i 0)
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1)))) = true ->
  map_contains (vm_maps (m_vmmaps m)) (in_arg i 0)
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1)))) = true ->
  mprotect_refusable m (in_arg i 0) (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1)))) = false ->
  exists eff m' evs, syscall_spec i m (Ok eff m' evs) /\ refusal_b i m (eff_ret eff) = false.
Proof.
  intros i m E Hgc Hal Hlen Hnw Hmod Hna Hma Hr.
  pose proof (proj2 (Z.eqb_eq _ _) Hal) as Hal'.
  pose proof (proj2 (Z.leb_gt _ _) Hnw) as Hnw'.
  eexists _, _, _. split.
  - apply (proj2 (scfg_spec_226 i m _ E)). unfold mprotect_spec. gates.
    apply (proj2 (bind_get_model _ _ _ _)). cbv beta zeta. gates.
    unfold mprotect_refusable in Hr. apply negb_false_iff in Hr.
    apply alt_r. eapply bind_ok_nil; [apply (choose_ok _ tt); exact Hr|].
    eapply bind_ok_nil; [apply modify_ok|]. apply pure_ok.
  - cbn [eff_ret]. apply refusal_b_226_below; [exact E|].
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. unfold two_pow_64. lia.
Qed.

Lemma mprotect_refusable_true_forced : forall i m,
  bv_unsigned (in_sysno i) = 226%Z ->
  mprotect_grows_conflict_b (in_arg i 2) = false ->
  (bv_unsigned (in_arg i 0) mod page_size = 0)%Z ->
  w_is0 (in_arg i 1) = false ->
  (bv_unsigned (in_arg i 0) + page_round_up_Z (bv_unsigned (in_arg i 1)) < two_pow_64)%Z ->
  mprotect_modeled_b (in_arg i 2) = true ->
  map_contains (vm_noaccess (m_vmmaps m)) (in_arg i 0)
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1)))) = true ->
  map_contains (vm_maps (m_vmmaps m)) (in_arg i 0)
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1)))) = true ->
  mprotect_refusable m (in_arg i 0) (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1)))) = true ->
  forall eff m' evs, syscall_spec i m (Ok eff m' evs) -> refusal_b i m (eff_ret eff) = true.
Proof.
  intros i m E Hgc Hal Hlen Hnw Hmod Hna Hma Hr eff m' evs Hs.
  pose proof (proj2 (Z.eqb_eq _ _) Hal) as Hal'.
  pose proof (proj2 (Z.leb_gt _ _) Hnw) as Hnw'.
  apply (proj1 (scfg_spec_226 _ _ _ E)) in Hs. unfold mprotect_spec in Hs. gates_in Hs.
  apply (proj1 (bind_get_model _ _ _ _)) in Hs. cbv beta zeta in Hs. gates_in Hs.
  unfold alt in Hs. destruct Hs as [Hs|Hs]; [exact (enomem_arm_refusal_226 _ _ _ _ _ E Hs)|].
  apply choose_bind_inv in Hs as (u & Hb & _).
  exfalso. unfold mprotect_refusable in Hr. rewrite Hb in Hr. cbn [negb] in Hr. discriminate Hr.
Qed.

Lemma mprotect_nonspur : forall i m eff,
  bv_unsigned (in_sysno i) = 226%Z ->
  mprotect_grows_conflict_b (in_arg i 2) = false ->
  (bv_unsigned (in_arg i 0) mod page_size = 0)%Z ->
  w_is0 (in_arg i 1) = false ->
  (bv_unsigned (in_arg i 0) + page_round_up_Z (bv_unsigned (in_arg i 1)) < two_pow_64)%Z ->
  mprotect_modeled_b (in_arg i 2) = true ->
  map_contains (vm_noaccess (m_vmmaps m)) (in_arg i 0)
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1)))) = true ->
  map_contains (vm_maps (m_vmmaps m)) (in_arg i 0)
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1)))) = true ->
  (~ spurious_refusal_cfg fcfg i m eff <->
   (refusal_b i m (eff_ret eff) = true ->
    mprotect_refusable m (in_arg i 0) (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1)))) = true)).
Proof.
  intros i m eff E Hgc Hal Hlen Hnw Hmod Hna Hma. apply (nonspur_cases _ i m eff (alloc_226 i E)).
  - apply mprotect_refusable_false_grant; assumption.
  - apply mprotect_refusable_true_forced; assumption.
Qed.

Lemma mprotect_refusal_nonspur_iff : forall i m eff,
  bv_unsigned (in_sysno i) = 226%Z ->
  mprotect_grows_conflict_b (in_arg i 2) = false ->
  (bv_unsigned (in_arg i 0) mod page_size = 0)%Z ->
  w_is0 (in_arg i 1) = false ->
  (bv_unsigned (in_arg i 0) + page_round_up_Z (bv_unsigned (in_arg i 1)) < two_pow_64)%Z ->
  mprotect_modeled_b (in_arg i 2) = true ->
  map_contains (vm_noaccess (m_vmmaps m)) (in_arg i 0)
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1)))) = true ->
  map_contains (vm_maps (m_vmmaps m)) (in_arg i 0)
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1)))) = true ->
  refusal_b i m (eff_ret eff) = true ->
  (~ spurious_refusal_cfg fcfg i m eff <->
   mprotect_refusable m (in_arg i 0) (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1)))) = true).
Proof. intros i m eff E Hgc Hal Hlen Hnw Hmod Hna Hma. apply nonspur_refusal_iff, mprotect_nonspur; assumption. Qed.

(* MAP_FIXED PROT_NONE over a free range (never refusable) *)
Lemma mmap_fixed_none_fresh_grant : forall i m,
  bv_unsigned (in_sysno i) = 222%Z ->
  mmap_off_aligned_b (in_arg i 5) = true -> mmap_anon_b (in_arg i 3) = true ->
  w_is0 (in_arg i 1) = false ->
  mmap_modeled_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_noaccess_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_fixed_noaccess_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = true ->
  (bv_unsigned (in_arg i 0) + page_round_up_Z (bv_unsigned (in_arg i 1)) <= alloc_top (m_vmmaps m))%Z ->
  (bv_unsigned (in_arg i 0) mod page_size = 0)%Z ->
  (0 < bv_unsigned (in_arg i 0))%Z ->
  region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) (in_arg i 0)
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1)))) = true ->
  exists eff m' evs, syscall_spec i m (Ok eff m' evs) /\ refusal_b i m (eff_ret eff) = false.
Proof.
  intros i m E Hoff Han Hlen Hmod Hna Hfx Hce Hal Hpos Hrf.
  fixed_prep Hlen Hce Hal Hpos.
  free_derive Hrf Hlen Hce.
  eexists _, _, _. split.
  -
    apply (proj2 (scfg_spec_222 i m _ E)). unfold mmap_spec. gates. cbv zeta. gates.
    apply (proj2 (bind_get_model _ _ _ _)). cbv beta zeta. gates.
    apply alt_r. eapply bind_ok_nil; [apply (choose_ok _ (in_arg i 0)); reflexivity|].
    eapply bind_ok_nil; [apply modify_ok|]. apply pure_ok.
  - cbn [eff_ret]. eapply refusal_b_222_placed; [exact E| |exact Hce]. lia.
Qed.

Lemma mmap_fixed_none_fresh_nonspur : forall i m eff,
  bv_unsigned (in_sysno i) = 222%Z ->
  mmap_off_aligned_b (in_arg i 5) = true -> mmap_anon_b (in_arg i 3) = true ->
  w_is0 (in_arg i 1) = false ->
  mmap_modeled_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_noaccess_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_fixed_noaccess_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = true ->
  (bv_unsigned (in_arg i 0) + page_round_up_Z (bv_unsigned (in_arg i 1)) <= alloc_top (m_vmmaps m))%Z ->
  (bv_unsigned (in_arg i 0) mod page_size = 0)%Z ->
  (0 < bv_unsigned (in_arg i 0))%Z ->
  region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) (in_arg i 0)
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1)))) = true ->
  (~ spurious_refusal_cfg fcfg i m eff <-> refusal_b i m (eff_ret eff) = false).
Proof.
  intros i m eff E Hoff Han Hlen Hmod Hna Hfx Hce Hal Hpos Hrf. apply (nonspur_of_grant i m eff (alloc_222 i E)).
  apply mmap_fixed_none_fresh_grant; assumption.
Qed.

(* MAP_FIXED PROT_NONE spanning mappings and gaps (never refusable) *)
Lemma mmap_fixed_none_span_grant : forall i m,
  bv_unsigned (in_sysno i) = 222%Z ->
  mmap_off_aligned_b (in_arg i 5) = true -> mmap_anon_b (in_arg i 3) = true ->
  w_is0 (in_arg i 1) = false ->
  mmap_modeled_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_noaccess_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_fixed_noaccess_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = true ->
  (bv_unsigned (in_arg i 0) + page_round_up_Z (bv_unsigned (in_arg i 1)) <= alloc_top (m_vmmaps m))%Z ->
  (bv_unsigned (in_arg i 0) mod page_size = 0)%Z ->
  (0 < bv_unsigned (in_arg i 0))%Z ->
  region_free (vm_reserved (m_vmmaps m)) (in_arg i 0)
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1)))) = true ->
  map_contains (vm_maps (m_vmmaps m)) (in_arg i 0)
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1)))) = false ->
  region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) (in_arg i 0)
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1)))) = false ->
  exists eff m' evs, syscall_spec i m (Ok eff m' evs) /\ refusal_b i m (eff_ret eff) = false.
Proof.
  intros i m E Hoff Han Hlen Hmod Hna Hfx Hce Hal Hpos Hrr Hmc Hrf.
  fixed_prep Hlen Hce Hal Hpos.
  eexists _, _, _. split.
  -
    apply (proj2 (scfg_spec_222 i m _ E)). unfold mmap_spec. gates. cbv zeta. gates.
    apply (proj2 (bind_get_model _ _ _ _)). cbv beta zeta. gates.
    apply alt_r, alt_l. eapply bind_ok_nil; [apply modify_ok|]. apply pure_ok.
  - cbn [eff_ret]. eapply refusal_b_222_placed; [exact E| |exact Hce]. lia.
Qed.

Lemma mmap_fixed_none_span_nonspur : forall i m eff,
  bv_unsigned (in_sysno i) = 222%Z ->
  mmap_off_aligned_b (in_arg i 5) = true -> mmap_anon_b (in_arg i 3) = true ->
  w_is0 (in_arg i 1) = false ->
  mmap_modeled_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_noaccess_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_fixed_noaccess_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = true ->
  (bv_unsigned (in_arg i 0) + page_round_up_Z (bv_unsigned (in_arg i 1)) <= alloc_top (m_vmmaps m))%Z ->
  (bv_unsigned (in_arg i 0) mod page_size = 0)%Z ->
  (0 < bv_unsigned (in_arg i 0))%Z ->
  region_free (vm_reserved (m_vmmaps m)) (in_arg i 0)
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1)))) = true ->
  map_contains (vm_maps (m_vmmaps m)) (in_arg i 0)
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1)))) = false ->
  region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) (in_arg i 0)
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1)))) = false ->
  (~ spurious_refusal_cfg fcfg i m eff <-> refusal_b i m (eff_ret eff) = false).
Proof.
  intros i m eff E Hoff Han Hlen Hmod Hna Hfx Hce Hal Hpos Hrr Hmc Hrf. apply (nonspur_of_grant i m eff (alloc_222 i E)).
  apply mmap_fixed_none_span_grant; assumption.
Qed.

(* MAP_FIXED rw over a free range *)
Lemma mmap_fixed_fresh_refusable_false_grant : forall i m,
  bv_unsigned (in_sysno i) = 222%Z ->
  mmap_off_aligned_b (in_arg i 5) = true -> mmap_anon_b (in_arg i 3) = true ->
  w_is0 (in_arg i 1) = false ->
  mmap_modeled_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_noaccess_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_fixed_noaccess_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_fixed_rw_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = true ->
  (bv_unsigned (in_arg i 0) + page_round_up_Z (bv_unsigned (in_arg i 1)) <= alloc_top (m_vmmaps m))%Z ->
  (bv_unsigned (in_arg i 0) mod page_size = 0)%Z ->
  (0 < bv_unsigned (in_arg i 0))%Z ->
  region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) (in_arg i 0)
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1)))) = true ->
  mmap_fixed_fresh_refusable (in_arg i 3) m (page_round_up_Z (bv_unsigned (in_arg i 1))) = false ->
  exists eff m' evs, syscall_spec i m (Ok eff m' evs) /\ refusal_b i m (eff_ret eff) = false.
Proof.
  intros i m E Hoff Han Hlen Hmod Hna Hfx Hfrw Hce Hal Hpos Hrf Hr.
  fixed_prep Hlen Hce Hal Hpos.
  free_derive Hrf Hlen Hce.
  eexists _, _, _. split.
  -
    apply (proj2 (scfg_spec_222 i m _ E)). unfold mmap_spec. gates. cbv zeta. gates.
    apply (proj2 (bind_get_model _ _ _ _)). cbv beta zeta. gates.
    unfold mmap_fixed_fresh_refusable in Hr. apply negb_false_iff in Hr.
    apply alt_r.
    eapply bind_ok_nil; [apply (choose_ok _ (in_arg i 0)); split; [reflexivity|exact Hr]|].
    eapply bind_ok_nil; [apply modify_ok|]. apply pure_ok.
  - cbn [eff_ret]. eapply refusal_b_222_placed; [exact E| |exact Hce]. lia.
Qed.

Lemma mmap_fixed_fresh_refusable_true_forced : forall i m,
  bv_unsigned (in_sysno i) = 222%Z ->
  mmap_off_aligned_b (in_arg i 5) = true -> mmap_anon_b (in_arg i 3) = true ->
  w_is0 (in_arg i 1) = false ->
  mmap_modeled_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_noaccess_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_fixed_noaccess_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_fixed_rw_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = true ->
  (bv_unsigned (in_arg i 0) + page_round_up_Z (bv_unsigned (in_arg i 1)) <= alloc_top (m_vmmaps m))%Z ->
  (bv_unsigned (in_arg i 0) mod page_size = 0)%Z ->
  (0 < bv_unsigned (in_arg i 0))%Z ->
  region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) (in_arg i 0)
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1)))) = true ->
  mmap_fixed_fresh_refusable (in_arg i 3) m (page_round_up_Z (bv_unsigned (in_arg i 1))) = true ->
  forall eff m' evs, syscall_spec i m (Ok eff m' evs) -> refusal_b i m (eff_ret eff) = true.
Proof.
  intros i m E Hoff Han Hlen Hmod Hna Hfx Hfrw Hce Hal Hpos Hrf Hr eff m' evs Hs.
  fixed_prep Hlen Hce Hal Hpos.
  free_derive Hrf Hlen Hce.
  apply (proj1 (scfg_spec_222 _ _ _ E)) in Hs. unfold mmap_spec in Hs. gates_in Hs. cbv zeta in Hs. gates_in Hs.
  apply (proj1 (bind_get_model _ _ _ _)) in Hs. cbv beta zeta in Hs. gates_in Hs.
  unfold alt in Hs. destruct Hs as [Hs|Hs]; [exact (enomem_arm_refusal _ _ _ _ _ E Hs)|].
  apply choose_bind_inv in Hs as (a & (_ & Hb) & _).
  exfalso. unfold mmap_fixed_fresh_refusable in Hr. rewrite Hb in Hr. cbn [negb] in Hr. discriminate Hr.
Qed.

Lemma mmap_fixed_fresh_nonspur : forall i m eff,
  bv_unsigned (in_sysno i) = 222%Z ->
  mmap_off_aligned_b (in_arg i 5) = true -> mmap_anon_b (in_arg i 3) = true ->
  w_is0 (in_arg i 1) = false ->
  mmap_modeled_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_noaccess_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_fixed_noaccess_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_fixed_rw_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = true ->
  (bv_unsigned (in_arg i 0) + page_round_up_Z (bv_unsigned (in_arg i 1)) <= alloc_top (m_vmmaps m))%Z ->
  (bv_unsigned (in_arg i 0) mod page_size = 0)%Z ->
  (0 < bv_unsigned (in_arg i 0))%Z ->
  region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) (in_arg i 0)
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1)))) = true ->
  (~ spurious_refusal_cfg fcfg i m eff <->
   (refusal_b i m (eff_ret eff) = true ->
    mmap_fixed_fresh_refusable (in_arg i 3) m (page_round_up_Z (bv_unsigned (in_arg i 1))) = true)).
Proof.
  intros i m eff E Hoff Han Hlen Hmod Hna Hfx Hfrw Hce Hal Hpos Hrf. apply (nonspur_cases _ i m eff (alloc_222 i E)).
  - apply mmap_fixed_fresh_refusable_false_grant; assumption.
  - apply mmap_fixed_fresh_refusable_true_forced; assumption.
Qed.

Lemma mmap_fixed_fresh_refusal_nonspur_iff : forall i m eff,
  bv_unsigned (in_sysno i) = 222%Z ->
  mmap_off_aligned_b (in_arg i 5) = true -> mmap_anon_b (in_arg i 3) = true ->
  w_is0 (in_arg i 1) = false ->
  mmap_modeled_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_noaccess_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_fixed_noaccess_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_fixed_rw_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = true ->
  (bv_unsigned (in_arg i 0) + page_round_up_Z (bv_unsigned (in_arg i 1)) <= alloc_top (m_vmmaps m))%Z ->
  (bv_unsigned (in_arg i 0) mod page_size = 0)%Z ->
  (0 < bv_unsigned (in_arg i 0))%Z ->
  region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) (in_arg i 0)
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1)))) = true ->
  refusal_b i m (eff_ret eff) = true ->
  (~ spurious_refusal_cfg fcfg i m eff <->
   mmap_fixed_fresh_refusable (in_arg i 3) m (page_round_up_Z (bv_unsigned (in_arg i 1))) = true).
Proof. intros i m eff E Hoff Han Hlen Hmod Hna Hfx Hfrw Hce Hal Hpos Hrf. apply nonspur_refusal_iff, mmap_fixed_fresh_nonspur; assumption. Qed.

(* MAP_FIXED rw over an existing mapping (contained commit) *)
Lemma mmap_fixed_commit_refusable_false_grant : forall i m,
  bv_unsigned (in_sysno i) = 222%Z ->
  mmap_off_aligned_b (in_arg i 5) = true -> mmap_anon_b (in_arg i 3) = true ->
  w_is0 (in_arg i 1) = false ->
  mmap_modeled_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_noaccess_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_fixed_noaccess_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_fixed_rw_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = true ->
  (bv_unsigned (in_arg i 0) + page_round_up_Z (bv_unsigned (in_arg i 1)) <= alloc_top (m_vmmaps m))%Z ->
  (bv_unsigned (in_arg i 0) mod page_size = 0)%Z ->
  (0 < bv_unsigned (in_arg i 0))%Z ->
  region_free (vm_reserved (m_vmmaps m)) (in_arg i 0)
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1)))) = true ->
  map_contains (vm_maps (m_vmmaps m)) (in_arg i 0)
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1)))) = true ->
  mmap_fixed_commit_refusable (in_arg i 3) m (in_arg i 0)
       (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1)))) = false ->
  exists eff m' evs, syscall_spec i m (Ok eff m' evs) /\ refusal_b i m (eff_ret eff) = false.
Proof.
  intros i m E Hoff Han Hlen Hmod Hna Hfx Hfrw Hce Hal Hpos Hrr Hmc Hr.
  fixed_prep Hlen Hce Hal Hpos.
  eexists _, _, _. split.
  -
    apply (proj2 (scfg_spec_222 i m _ E)). unfold mmap_spec. gates. cbv zeta. gates.
    apply (proj2 (bind_get_model _ _ _ _)). cbv beta zeta. gates.
    unfold mmap_fixed_commit_refusable in Hr. apply negb_false_iff in Hr.
    apply alt_r, alt_l. eapply bind_ok_nil; [apply (choose_ok _ tt); exact Hr|].
    eapply bind_ok_nil; [apply modify_ok|]. apply pure_ok.
  - cbn [eff_ret]. eapply refusal_b_222_placed; [exact E| |exact Hce]. lia.
Qed.

Lemma mmap_fixed_commit_refusable_true_forced : forall i m,
  bv_unsigned (in_sysno i) = 222%Z ->
  mmap_off_aligned_b (in_arg i 5) = true -> mmap_anon_b (in_arg i 3) = true ->
  w_is0 (in_arg i 1) = false ->
  mmap_modeled_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_noaccess_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_fixed_noaccess_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_fixed_rw_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = true ->
  (bv_unsigned (in_arg i 0) + page_round_up_Z (bv_unsigned (in_arg i 1)) <= alloc_top (m_vmmaps m))%Z ->
  (bv_unsigned (in_arg i 0) mod page_size = 0)%Z ->
  (0 < bv_unsigned (in_arg i 0))%Z ->
  region_free (vm_reserved (m_vmmaps m)) (in_arg i 0)
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1)))) = true ->
  map_contains (vm_maps (m_vmmaps m)) (in_arg i 0)
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1)))) = true ->
  mmap_fixed_commit_refusable (in_arg i 3) m (in_arg i 0)
       (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1)))) = true ->
  forall eff m' evs, syscall_spec i m (Ok eff m' evs) -> refusal_b i m (eff_ret eff) = true.
Proof.
  intros i m E Hoff Han Hlen Hmod Hna Hfx Hfrw Hce Hal Hpos Hrr Hmc Hr eff m' evs Hs.
  fixed_prep Hlen Hce Hal Hpos.
  apply (proj1 (scfg_spec_222 _ _ _ E)) in Hs. unfold mmap_spec in Hs. gates_in Hs. cbv zeta in Hs. gates_in Hs.
  apply (proj1 (bind_get_model _ _ _ _)) in Hs. cbv beta zeta in Hs. gates_in Hs.
  unfold alt in Hs. destruct Hs as [Hs|[Hs|Hs]].
  - exact (enomem_arm_refusal _ _ _ _ _ E Hs).
  - apply choose_bind_inv in Hs as (u & Hb & _).
    exfalso. unfold mmap_fixed_commit_refusable in Hr. rewrite Hb in Hr. cbn [negb] in Hr. discriminate Hr.
  - exact (destroy_arm_refusal _ _ _ _ _ _ _ E Hs).
Qed.

Lemma mmap_fixed_commit_nonspur : forall i m eff,
  bv_unsigned (in_sysno i) = 222%Z ->
  mmap_off_aligned_b (in_arg i 5) = true -> mmap_anon_b (in_arg i 3) = true ->
  w_is0 (in_arg i 1) = false ->
  mmap_modeled_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_noaccess_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_fixed_noaccess_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_fixed_rw_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = true ->
  (bv_unsigned (in_arg i 0) + page_round_up_Z (bv_unsigned (in_arg i 1)) <= alloc_top (m_vmmaps m))%Z ->
  (bv_unsigned (in_arg i 0) mod page_size = 0)%Z ->
  (0 < bv_unsigned (in_arg i 0))%Z ->
  region_free (vm_reserved (m_vmmaps m)) (in_arg i 0)
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1)))) = true ->
  map_contains (vm_maps (m_vmmaps m)) (in_arg i 0)
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1)))) = true ->
  (~ spurious_refusal_cfg fcfg i m eff <->
   (refusal_b i m (eff_ret eff) = true ->
    mmap_fixed_commit_refusable (in_arg i 3) m (in_arg i 0)
       (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1)))) = true)).
Proof.
  intros i m eff E Hoff Han Hlen Hmod Hna Hfx Hfrw Hce Hal Hpos Hrr Hmc. apply (nonspur_cases _ i m eff (alloc_222 i E)).
  - apply mmap_fixed_commit_refusable_false_grant; assumption.
  - apply mmap_fixed_commit_refusable_true_forced; assumption.
Qed.

Lemma mmap_fixed_commit_refusal_nonspur_iff : forall i m eff,
  bv_unsigned (in_sysno i) = 222%Z ->
  mmap_off_aligned_b (in_arg i 5) = true -> mmap_anon_b (in_arg i 3) = true ->
  w_is0 (in_arg i 1) = false ->
  mmap_modeled_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_noaccess_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_fixed_noaccess_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_fixed_rw_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = true ->
  (bv_unsigned (in_arg i 0) + page_round_up_Z (bv_unsigned (in_arg i 1)) <= alloc_top (m_vmmaps m))%Z ->
  (bv_unsigned (in_arg i 0) mod page_size = 0)%Z ->
  (0 < bv_unsigned (in_arg i 0))%Z ->
  region_free (vm_reserved (m_vmmaps m)) (in_arg i 0)
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1)))) = true ->
  map_contains (vm_maps (m_vmmaps m)) (in_arg i 0)
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1)))) = true ->
  refusal_b i m (eff_ret eff) = true ->
  (~ spurious_refusal_cfg fcfg i m eff <->
   mmap_fixed_commit_refusable (in_arg i 3) m (in_arg i 0)
       (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1)))) = true).
Proof. intros i m eff E Hoff Han Hlen Hmod Hna Hfx Hfrw Hce Hal Hpos Hrr Hmc. apply nonspur_refusal_iff, mmap_fixed_commit_nonspur; assumption. Qed.

(* MAP_FIXED rw spanning mappings and gaps *)
Lemma mmap_fixed_span_refusable_false_grant : forall i m,
  bv_unsigned (in_sysno i) = 222%Z ->
  mmap_off_aligned_b (in_arg i 5) = true -> mmap_anon_b (in_arg i 3) = true ->
  w_is0 (in_arg i 1) = false ->
  mmap_modeled_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_noaccess_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_fixed_noaccess_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_fixed_rw_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = true ->
  (bv_unsigned (in_arg i 0) + page_round_up_Z (bv_unsigned (in_arg i 1)) <= alloc_top (m_vmmaps m))%Z ->
  (bv_unsigned (in_arg i 0) mod page_size = 0)%Z ->
  (0 < bv_unsigned (in_arg i 0))%Z ->
  region_free (vm_reserved (m_vmmaps m)) (in_arg i 0)
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1)))) = true ->
  map_contains (vm_maps (m_vmmaps m)) (in_arg i 0)
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1)))) = false ->
  region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) (in_arg i 0)
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1)))) = false ->
  mmap_fixed_span_refusable (in_arg i 3) m (in_arg i 0)
       (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1)))) = false ->
  exists eff m' evs, syscall_spec i m (Ok eff m' evs) /\ refusal_b i m (eff_ret eff) = false.
Proof.
  intros i m E Hoff Han Hlen Hmod Hna Hfx Hfrw Hce Hal Hpos Hrr Hmc Hrf Hr.
  fixed_prep Hlen Hce Hal Hpos.
  eexists _, _, _. split.
  -
    apply (proj2 (scfg_spec_222 i m _ E)). unfold mmap_spec. gates. cbv zeta. gates.
    apply (proj2 (bind_get_model _ _ _ _)). cbv beta zeta. gates.
    unfold mmap_fixed_span_refusable in Hr. apply negb_false_iff in Hr.
    apply alt_r, alt_l. eapply bind_ok_nil; [apply (choose_ok _ tt); exact Hr|].
    eapply bind_ok_nil; [apply modify_ok|]. apply pure_ok.
  - cbn [eff_ret]. eapply refusal_b_222_placed; [exact E| |exact Hce]. lia.
Qed.

Lemma mmap_fixed_span_refusable_true_forced : forall i m,
  bv_unsigned (in_sysno i) = 222%Z ->
  mmap_off_aligned_b (in_arg i 5) = true -> mmap_anon_b (in_arg i 3) = true ->
  w_is0 (in_arg i 1) = false ->
  mmap_modeled_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_noaccess_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_fixed_noaccess_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_fixed_rw_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = true ->
  (bv_unsigned (in_arg i 0) + page_round_up_Z (bv_unsigned (in_arg i 1)) <= alloc_top (m_vmmaps m))%Z ->
  (bv_unsigned (in_arg i 0) mod page_size = 0)%Z ->
  (0 < bv_unsigned (in_arg i 0))%Z ->
  region_free (vm_reserved (m_vmmaps m)) (in_arg i 0)
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1)))) = true ->
  map_contains (vm_maps (m_vmmaps m)) (in_arg i 0)
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1)))) = false ->
  region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) (in_arg i 0)
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1)))) = false ->
  mmap_fixed_span_refusable (in_arg i 3) m (in_arg i 0)
       (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1)))) = true ->
  forall eff m' evs, syscall_spec i m (Ok eff m' evs) -> refusal_b i m (eff_ret eff) = true.
Proof.
  intros i m E Hoff Han Hlen Hmod Hna Hfx Hfrw Hce Hal Hpos Hrr Hmc Hrf Hr eff m' evs Hs.
  fixed_prep Hlen Hce Hal Hpos.
  apply (proj1 (scfg_spec_222 _ _ _ E)) in Hs. unfold mmap_spec in Hs. gates_in Hs. cbv zeta in Hs. gates_in Hs.
  apply (proj1 (bind_get_model _ _ _ _)) in Hs. cbv beta zeta in Hs. gates_in Hs.
  unfold alt in Hs. destruct Hs as [Hs|[Hs|Hs]].
  - exact (enomem_arm_refusal _ _ _ _ _ E Hs).
  - apply choose_bind_inv in Hs as (u & Hb & _).
    exfalso. unfold mmap_fixed_span_refusable in Hr. rewrite Hb in Hr. cbn [negb] in Hr. discriminate Hr.
  - exact (destroy_arm_refusal _ _ _ _ _ _ _ E Hs).
Qed.

Lemma mmap_fixed_span_nonspur : forall i m eff,
  bv_unsigned (in_sysno i) = 222%Z ->
  mmap_off_aligned_b (in_arg i 5) = true -> mmap_anon_b (in_arg i 3) = true ->
  w_is0 (in_arg i 1) = false ->
  mmap_modeled_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_noaccess_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_fixed_noaccess_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_fixed_rw_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = true ->
  (bv_unsigned (in_arg i 0) + page_round_up_Z (bv_unsigned (in_arg i 1)) <= alloc_top (m_vmmaps m))%Z ->
  (bv_unsigned (in_arg i 0) mod page_size = 0)%Z ->
  (0 < bv_unsigned (in_arg i 0))%Z ->
  region_free (vm_reserved (m_vmmaps m)) (in_arg i 0)
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1)))) = true ->
  map_contains (vm_maps (m_vmmaps m)) (in_arg i 0)
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1)))) = false ->
  region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) (in_arg i 0)
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1)))) = false ->
  (~ spurious_refusal_cfg fcfg i m eff <->
   (refusal_b i m (eff_ret eff) = true ->
    mmap_fixed_span_refusable (in_arg i 3) m (in_arg i 0)
       (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1)))) = true)).
Proof.
  intros i m eff E Hoff Han Hlen Hmod Hna Hfx Hfrw Hce Hal Hpos Hrr Hmc Hrf. apply (nonspur_cases _ i m eff (alloc_222 i E)).
  - apply mmap_fixed_span_refusable_false_grant; assumption.
  - apply mmap_fixed_span_refusable_true_forced; assumption.
Qed.

Lemma mmap_fixed_span_refusal_nonspur_iff : forall i m eff,
  bv_unsigned (in_sysno i) = 222%Z ->
  mmap_off_aligned_b (in_arg i 5) = true -> mmap_anon_b (in_arg i 3) = true ->
  w_is0 (in_arg i 1) = false ->
  mmap_modeled_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_noaccess_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_fixed_noaccess_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_fixed_rw_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = true ->
  (bv_unsigned (in_arg i 0) + page_round_up_Z (bv_unsigned (in_arg i 1)) <= alloc_top (m_vmmaps m))%Z ->
  (bv_unsigned (in_arg i 0) mod page_size = 0)%Z ->
  (0 < bv_unsigned (in_arg i 0))%Z ->
  region_free (vm_reserved (m_vmmaps m)) (in_arg i 0)
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1)))) = true ->
  map_contains (vm_maps (m_vmmaps m)) (in_arg i 0)
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1)))) = false ->
  region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) (in_arg i 0)
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1)))) = false ->
  refusal_b i m (eff_ret eff) = true ->
  (~ spurious_refusal_cfg fcfg i m eff <->
   mmap_fixed_span_refusable (in_arg i 3) m (in_arg i 0)
       (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1)))) = true).
Proof. intros i m eff E Hoff Han Hlen Hmod Hna Hfx Hfrw Hce Hal Hpos Hrr Hmc Hrf. apply nonspur_refusal_iff, mmap_fixed_span_nonspur; assumption. Qed.

(* MAP_FIXED_NOREPLACE PROT_NONE over a free range (never refusable) *)
Lemma mmap_noreplace_none_free_grant : forall i m,
  bv_unsigned (in_sysno i) = 222%Z ->
  mmap_off_aligned_b (in_arg i 5) = true -> mmap_anon_b (in_arg i 3) = true ->
  w_is0 (in_arg i 1) = false ->
  mmap_modeled_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_noaccess_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_fixed_noaccess_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_fixed_rw_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_noreplace_noaccess_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = true ->
  (bv_unsigned (in_arg i 0) + page_round_up_Z (bv_unsigned (in_arg i 1)) <= alloc_top (m_vmmaps m))%Z ->
  (bv_unsigned (in_arg i 0) mod page_size = 0)%Z ->
  (0 < bv_unsigned (in_arg i 0))%Z ->
  region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) (in_arg i 0)
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1)))) = true ->
  exists eff m' evs, syscall_spec i m (Ok eff m' evs) /\ refusal_b i m (eff_ret eff) = false.
Proof.
  intros i m E Hoff Han Hlen Hmod Hna Hfx Hfrw Hnna Hce Hal Hpos Hrf.
  fixed_prep Hlen Hce Hal Hpos.
  eexists _, _, _. split.
  -
    apply (proj2 (scfg_spec_222 i m _ E)). unfold mmap_spec. gates. cbv zeta. gates.
    apply (proj2 (bind_get_model _ _ _ _)). cbv beta zeta. gates.
    apply alt_r. eapply bind_ok_nil; [apply (choose_ok _ (in_arg i 0)); reflexivity|].
    eapply bind_ok_nil; [apply modify_ok|]. apply pure_ok.
  - cbn [eff_ret]. eapply refusal_b_222_placed; [exact E| |exact Hce]. lia.
Qed.

Lemma mmap_noreplace_none_free_nonspur : forall i m eff,
  bv_unsigned (in_sysno i) = 222%Z ->
  mmap_off_aligned_b (in_arg i 5) = true -> mmap_anon_b (in_arg i 3) = true ->
  w_is0 (in_arg i 1) = false ->
  mmap_modeled_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_noaccess_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_fixed_noaccess_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_fixed_rw_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_noreplace_noaccess_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = true ->
  (bv_unsigned (in_arg i 0) + page_round_up_Z (bv_unsigned (in_arg i 1)) <= alloc_top (m_vmmaps m))%Z ->
  (bv_unsigned (in_arg i 0) mod page_size = 0)%Z ->
  (0 < bv_unsigned (in_arg i 0))%Z ->
  region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) (in_arg i 0)
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1)))) = true ->
  (~ spurious_refusal_cfg fcfg i m eff <-> refusal_b i m (eff_ret eff) = false).
Proof.
  intros i m eff E Hoff Han Hlen Hmod Hna Hfx Hfrw Hnna Hce Hal Hpos Hrf. apply (nonspur_of_grant i m eff (alloc_222 i E)).
  apply mmap_noreplace_none_free_grant; assumption.
Qed.

(* MAP_FIXED_NOREPLACE PROT_NONE over an occupied range: -EEXIST answers, never refusable *)
Lemma mmap_noreplace_none_occ_grant : forall i m,
  bv_unsigned (in_sysno i) = 222%Z ->
  mmap_off_aligned_b (in_arg i 5) = true -> mmap_anon_b (in_arg i 3) = true ->
  w_is0 (in_arg i 1) = false ->
  mmap_modeled_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_noaccess_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_fixed_noaccess_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_fixed_rw_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_noreplace_noaccess_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = true ->
  (bv_unsigned (in_arg i 0) + page_round_up_Z (bv_unsigned (in_arg i 1)) <= alloc_top (m_vmmaps m))%Z ->
  (bv_unsigned (in_arg i 0) mod page_size = 0)%Z ->
  (0 < bv_unsigned (in_arg i 0))%Z ->
  region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) (in_arg i 0)
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1)))) = false ->
  exists eff m' evs, syscall_spec i m (Ok eff m' evs) /\ refusal_b i m (eff_ret eff) = false.
Proof.
  intros i m E Hoff Han Hlen Hmod Hna Hfx Hfrw Hnna Hce Hal Hpos Hrf.
  fixed_prep Hlen Hce Hal Hpos.
  eexists _, _, _. split.
  -
    apply (proj2 (scfg_spec_222 i m _ E)). unfold mmap_spec. gates. cbv zeta. gates.
    apply (proj2 (bind_get_model _ _ _ _)). cbv beta zeta. gates.
    apply alt_r. unfold err_ret, ret_only. apply pure_ok.
  - cbn [eff_ret]. apply refusal_b_222_eexist, E.
Qed.

Lemma mmap_noreplace_none_occ_nonspur : forall i m eff,
  bv_unsigned (in_sysno i) = 222%Z ->
  mmap_off_aligned_b (in_arg i 5) = true -> mmap_anon_b (in_arg i 3) = true ->
  w_is0 (in_arg i 1) = false ->
  mmap_modeled_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_noaccess_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_fixed_noaccess_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_fixed_rw_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_noreplace_noaccess_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = true ->
  (bv_unsigned (in_arg i 0) + page_round_up_Z (bv_unsigned (in_arg i 1)) <= alloc_top (m_vmmaps m))%Z ->
  (bv_unsigned (in_arg i 0) mod page_size = 0)%Z ->
  (0 < bv_unsigned (in_arg i 0))%Z ->
  region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) (in_arg i 0)
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1)))) = false ->
  (~ spurious_refusal_cfg fcfg i m eff <-> refusal_b i m (eff_ret eff) = false).
Proof.
  intros i m eff E Hoff Han Hlen Hmod Hna Hfx Hfrw Hnna Hce Hal Hpos Hrf. apply (nonspur_of_grant i m eff (alloc_222 i E)).
  apply mmap_noreplace_none_occ_grant; assumption.
Qed.

(* MAP_FIXED_NOREPLACE rw over a free range *)
Lemma mmap_noreplace_rw_free_refusable_false_grant : forall i m,
  bv_unsigned (in_sysno i) = 222%Z ->
  mmap_off_aligned_b (in_arg i 5) = true -> mmap_anon_b (in_arg i 3) = true ->
  w_is0 (in_arg i 1) = false ->
  mmap_modeled_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_noaccess_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_fixed_noaccess_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_fixed_rw_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_noreplace_noaccess_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_noreplace_rw_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = true ->
  (bv_unsigned (in_arg i 0) + page_round_up_Z (bv_unsigned (in_arg i 1)) <= alloc_top (m_vmmaps m))%Z ->
  (bv_unsigned (in_arg i 0) mod page_size = 0)%Z ->
  (0 < bv_unsigned (in_arg i 0))%Z ->
  region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) (in_arg i 0)
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1)))) = true ->
  mmap_fixed_fresh_refusable (in_arg i 3) m (page_round_up_Z (bv_unsigned (in_arg i 1))) = false ->
  exists eff m' evs, syscall_spec i m (Ok eff m' evs) /\ refusal_b i m (eff_ret eff) = false.
Proof.
  intros i m E Hoff Han Hlen Hmod Hna Hfx Hfrw Hnna Hnrw Hce Hal Hpos Hrf Hr.
  fixed_prep Hlen Hce Hal Hpos.
  eexists _, _, _. split.
  -
    apply (proj2 (scfg_spec_222 i m _ E)). unfold mmap_spec. gates. cbv zeta. gates.
    apply (proj2 (bind_get_model _ _ _ _)). cbv beta zeta. gates.
    unfold mmap_fixed_fresh_refusable in Hr. apply negb_false_iff in Hr.
    apply alt_r.
    eapply bind_ok_nil; [apply (choose_ok _ (in_arg i 0)); split; [reflexivity|exact Hr]|].
    eapply bind_ok_nil; [apply modify_ok|]. apply pure_ok.
  - cbn [eff_ret]. eapply refusal_b_222_placed; [exact E| |exact Hce]. lia.
Qed.

Lemma mmap_noreplace_rw_free_refusable_true_forced : forall i m,
  bv_unsigned (in_sysno i) = 222%Z ->
  mmap_off_aligned_b (in_arg i 5) = true -> mmap_anon_b (in_arg i 3) = true ->
  w_is0 (in_arg i 1) = false ->
  mmap_modeled_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_noaccess_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_fixed_noaccess_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_fixed_rw_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_noreplace_noaccess_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_noreplace_rw_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = true ->
  (bv_unsigned (in_arg i 0) + page_round_up_Z (bv_unsigned (in_arg i 1)) <= alloc_top (m_vmmaps m))%Z ->
  (bv_unsigned (in_arg i 0) mod page_size = 0)%Z ->
  (0 < bv_unsigned (in_arg i 0))%Z ->
  region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) (in_arg i 0)
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1)))) = true ->
  mmap_fixed_fresh_refusable (in_arg i 3) m (page_round_up_Z (bv_unsigned (in_arg i 1))) = true ->
  forall eff m' evs, syscall_spec i m (Ok eff m' evs) -> refusal_b i m (eff_ret eff) = true.
Proof.
  intros i m E Hoff Han Hlen Hmod Hna Hfx Hfrw Hnna Hnrw Hce Hal Hpos Hrf Hr eff m' evs Hs.
  fixed_prep Hlen Hce Hal Hpos.
  apply (proj1 (scfg_spec_222 _ _ _ E)) in Hs. unfold mmap_spec in Hs. gates_in Hs. cbv zeta in Hs. gates_in Hs.
  apply (proj1 (bind_get_model _ _ _ _)) in Hs. cbv beta zeta in Hs. gates_in Hs.
  unfold alt in Hs. destruct Hs as [Hs|Hs]; [exact (enomem_arm_refusal _ _ _ _ _ E Hs)|].
  apply choose_bind_inv in Hs as (a & (_ & Hb) & _).
  exfalso. unfold mmap_fixed_fresh_refusable in Hr. rewrite Hb in Hr. cbn [negb] in Hr. discriminate Hr.
Qed.

Lemma mmap_noreplace_rw_free_nonspur : forall i m eff,
  bv_unsigned (in_sysno i) = 222%Z ->
  mmap_off_aligned_b (in_arg i 5) = true -> mmap_anon_b (in_arg i 3) = true ->
  w_is0 (in_arg i 1) = false ->
  mmap_modeled_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_noaccess_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_fixed_noaccess_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_fixed_rw_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_noreplace_noaccess_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_noreplace_rw_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = true ->
  (bv_unsigned (in_arg i 0) + page_round_up_Z (bv_unsigned (in_arg i 1)) <= alloc_top (m_vmmaps m))%Z ->
  (bv_unsigned (in_arg i 0) mod page_size = 0)%Z ->
  (0 < bv_unsigned (in_arg i 0))%Z ->
  region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) (in_arg i 0)
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1)))) = true ->
  (~ spurious_refusal_cfg fcfg i m eff <->
   (refusal_b i m (eff_ret eff) = true ->
    mmap_fixed_fresh_refusable (in_arg i 3) m (page_round_up_Z (bv_unsigned (in_arg i 1))) = true)).
Proof.
  intros i m eff E Hoff Han Hlen Hmod Hna Hfx Hfrw Hnna Hnrw Hce Hal Hpos Hrf. apply (nonspur_cases _ i m eff (alloc_222 i E)).
  - apply mmap_noreplace_rw_free_refusable_false_grant; assumption.
  - apply mmap_noreplace_rw_free_refusable_true_forced; assumption.
Qed.

Lemma mmap_noreplace_rw_free_refusal_nonspur_iff : forall i m eff,
  bv_unsigned (in_sysno i) = 222%Z ->
  mmap_off_aligned_b (in_arg i 5) = true -> mmap_anon_b (in_arg i 3) = true ->
  w_is0 (in_arg i 1) = false ->
  mmap_modeled_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_noaccess_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_fixed_noaccess_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_fixed_rw_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_noreplace_noaccess_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_noreplace_rw_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = true ->
  (bv_unsigned (in_arg i 0) + page_round_up_Z (bv_unsigned (in_arg i 1)) <= alloc_top (m_vmmaps m))%Z ->
  (bv_unsigned (in_arg i 0) mod page_size = 0)%Z ->
  (0 < bv_unsigned (in_arg i 0))%Z ->
  region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) (in_arg i 0)
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1)))) = true ->
  refusal_b i m (eff_ret eff) = true ->
  (~ spurious_refusal_cfg fcfg i m eff <->
   mmap_fixed_fresh_refusable (in_arg i 3) m (page_round_up_Z (bv_unsigned (in_arg i 1))) = true).
Proof. intros i m eff E Hoff Han Hlen Hmod Hna Hfx Hfrw Hnna Hnrw Hce Hal Hpos Hrf. apply nonspur_refusal_iff, mmap_noreplace_rw_free_nonspur; assumption. Qed.

(* MAP_FIXED_NOREPLACE rw over an occupied range: -EEXIST answers, never refusable *)
Lemma mmap_noreplace_rw_occ_grant : forall i m,
  bv_unsigned (in_sysno i) = 222%Z ->
  mmap_off_aligned_b (in_arg i 5) = true -> mmap_anon_b (in_arg i 3) = true ->
  w_is0 (in_arg i 1) = false ->
  mmap_modeled_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_noaccess_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_fixed_noaccess_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_fixed_rw_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_noreplace_noaccess_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_noreplace_rw_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = true ->
  (bv_unsigned (in_arg i 0) + page_round_up_Z (bv_unsigned (in_arg i 1)) <= alloc_top (m_vmmaps m))%Z ->
  (bv_unsigned (in_arg i 0) mod page_size = 0)%Z ->
  (0 < bv_unsigned (in_arg i 0))%Z ->
  region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) (in_arg i 0)
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1)))) = false ->
  exists eff m' evs, syscall_spec i m (Ok eff m' evs) /\ refusal_b i m (eff_ret eff) = false.
Proof.
  intros i m E Hoff Han Hlen Hmod Hna Hfx Hfrw Hnna Hnrw Hce Hal Hpos Hrf.
  fixed_prep Hlen Hce Hal Hpos.
  eexists _, _, _. split.
  -
    apply (proj2 (scfg_spec_222 i m _ E)). unfold mmap_spec. gates. cbv zeta. gates.
    apply (proj2 (bind_get_model _ _ _ _)). cbv beta zeta. gates.
    apply alt_r. unfold err_ret, ret_only. apply pure_ok.
  - cbn [eff_ret]. apply refusal_b_222_eexist, E.
Qed.

Lemma mmap_noreplace_rw_occ_nonspur : forall i m eff,
  bv_unsigned (in_sysno i) = 222%Z ->
  mmap_off_aligned_b (in_arg i 5) = true -> mmap_anon_b (in_arg i 3) = true ->
  w_is0 (in_arg i 1) = false ->
  mmap_modeled_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_noaccess_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_fixed_noaccess_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_fixed_rw_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_noreplace_noaccess_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_noreplace_rw_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = true ->
  (bv_unsigned (in_arg i 0) + page_round_up_Z (bv_unsigned (in_arg i 1)) <= alloc_top (m_vmmaps m))%Z ->
  (bv_unsigned (in_arg i 0) mod page_size = 0)%Z ->
  (0 < bv_unsigned (in_arg i 0))%Z ->
  region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) (in_arg i 0)
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1)))) = false ->
  (~ spurious_refusal_cfg fcfg i m eff <-> refusal_b i m (eff_ret eff) = false).
Proof.
  intros i m eff E Hoff Han Hlen Hmod Hna Hfx Hfrw Hnna Hnrw Hce Hal Hpos Hrf. apply (nonspur_of_grant i m eff (alloc_222 i E)).
  apply mmap_noreplace_rw_occ_grant; assumption.
Qed.

(* MAP_FIXED rw contained commit: the destructive -ENOMEM is an outcome whatever the budget says *)
Lemma mmap_fixed_commit_destroy_outcome : forall i m,
  bv_unsigned (in_sysno i) = 222%Z ->
  mmap_off_aligned_b (in_arg i 5) = true -> mmap_anon_b (in_arg i 3) = true ->
  w_is0 (in_arg i 1) = false ->
  mmap_modeled_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_noaccess_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_fixed_noaccess_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_fixed_rw_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = true ->
  (bv_unsigned (in_arg i 0) + page_round_up_Z (bv_unsigned (in_arg i 1)) <= alloc_top (m_vmmaps m))%Z ->
  (bv_unsigned (in_arg i 0) mod page_size = 0)%Z ->
  (0 < bv_unsigned (in_arg i 0))%Z ->
  region_free (vm_reserved (m_vmmaps m)) (in_arg i 0)
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1)))) = true ->
  map_contains (vm_maps (m_vmmaps m)) (in_arg i 0)
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1)))) = true ->
  syscall_spec i m
    (Ok (mkEffectU (errno_ret ENOMEM) [] [] [(in_arg i 0, (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1)))))] [] [])
      (with_mmap_destroyed (in_arg i 0) (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1))))
      (mmap_fixed_destroyed_next (m_vmmaps m) (in_arg i 0) (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1))))) m) []).
Proof.
  intros i m E Hoff Han Hlen Hmod Hna Hfx Hfrw Hce Hal Hpos Hrr Hmc.
  fixed_prep Hlen Hce Hal Hpos.
    apply (proj2 (scfg_spec_222 i m _ E)). unfold mmap_spec. gates. cbv zeta. gates.
    apply (proj2 (bind_get_model _ _ _ _)). cbv beta zeta. gates.
    apply alt_r, alt_r. eapply bind_ok_nil; [apply (choose_ok _ ENOMEM); left; reflexivity|].
    eapply bind_ok_nil; [apply modify_ok|]. apply pure_ok.
Qed.

Lemma mmap_fixed_commit_refused_outcomes : forall i m,
  bv_unsigned (in_sysno i) = 222%Z ->
  mmap_off_aligned_b (in_arg i 5) = true -> mmap_anon_b (in_arg i 3) = true ->
  w_is0 (in_arg i 1) = false ->
  mmap_modeled_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_noaccess_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_fixed_noaccess_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_fixed_rw_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = true ->
  (bv_unsigned (in_arg i 0) + page_round_up_Z (bv_unsigned (in_arg i 1)) <= alloc_top (m_vmmaps m))%Z ->
  (bv_unsigned (in_arg i 0) mod page_size = 0)%Z ->
  (0 < bv_unsigned (in_arg i 0))%Z ->
  region_free (vm_reserved (m_vmmaps m)) (in_arg i 0)
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1)))) = true ->
  map_contains (vm_maps (m_vmmaps m)) (in_arg i 0)
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1)))) = true ->
  mmap_fixed_commit_refusable (in_arg i 3) m (in_arg i 0)
       (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1)))) = true ->
  forall eff m' evs, syscall_spec i m (Ok eff m' evs) ->
  (eff = mkEffect (errno_ret ENOMEM) [] [] /\ m' = m /\ evs = [])
  \/ (eff = mkEffectU (errno_ret ENOMEM) [] [] [(in_arg i 0, (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1)))))] [] []
      /\ m' = with_mmap_destroyed (in_arg i 0) (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1))))
      (mmap_fixed_destroyed_next (m_vmmaps m) (in_arg i 0) (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1))))) m
      /\ evs = []).
Proof.
  intros i m E Hoff Han Hlen Hmod Hna Hfx Hfrw Hce Hal Hpos Hrr Hmc Hr eff m' evs Hs.
  fixed_prep Hlen Hce Hal Hpos.
  apply (proj1 (scfg_spec_222 _ _ _ E)) in Hs. unfold mmap_spec in Hs. gates_in Hs. cbv zeta in Hs. gates_in Hs.
  apply (proj1 (bind_get_model _ _ _ _)) in Hs. cbv beta zeta in Hs. gates_in Hs.
  unfold alt in Hs. destruct Hs as [Hs|[Hs|Hs]].
  - left. apply errno_bind_inv in Hs as (e & He & Hs). destruct He as [<-|[]].
    exact (err_ret_inv _ _ _ _ _ _ Hs).
  - apply choose_bind_inv in Hs as (u & Hb & _).
    exfalso. unfold mmap_fixed_commit_refusable in Hr. rewrite Hb in Hr. cbn [negb] in Hr. discriminate Hr.
  - right. apply errno_bind_inv in Hs as (e & He & Hs). destruct He as [<-|[]].
    apply modify_bind_inv in Hs. exact (pure_inv _ _ _ _ _ _ Hs).
Qed.

(* MAP_FIXED rw span: the destructive -ENOMEM is an outcome whatever the budget says *)
Lemma mmap_fixed_span_destroy_outcome : forall i m,
  bv_unsigned (in_sysno i) = 222%Z ->
  mmap_off_aligned_b (in_arg i 5) = true -> mmap_anon_b (in_arg i 3) = true ->
  w_is0 (in_arg i 1) = false ->
  mmap_modeled_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_noaccess_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_fixed_noaccess_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_fixed_rw_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = true ->
  (bv_unsigned (in_arg i 0) + page_round_up_Z (bv_unsigned (in_arg i 1)) <= alloc_top (m_vmmaps m))%Z ->
  (bv_unsigned (in_arg i 0) mod page_size = 0)%Z ->
  (0 < bv_unsigned (in_arg i 0))%Z ->
  region_free (vm_reserved (m_vmmaps m)) (in_arg i 0)
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1)))) = true ->
  map_contains (vm_maps (m_vmmaps m)) (in_arg i 0)
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1)))) = false ->
  region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) (in_arg i 0)
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1)))) = false ->
  syscall_spec i m
    (Ok (mkEffectU (errno_ret ENOMEM) [] [] [(in_arg i 0, (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1)))))] [] [])
      (with_mmap_destroyed (in_arg i 0) (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1))))
      (mmap_fixed_destroyed_next (m_vmmaps m) (in_arg i 0) (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1))))) m) []).
Proof.
  intros i m E Hoff Han Hlen Hmod Hna Hfx Hfrw Hce Hal Hpos Hrr Hmc Hrf.
  fixed_prep Hlen Hce Hal Hpos.
    apply (proj2 (scfg_spec_222 i m _ E)). unfold mmap_spec. gates. cbv zeta. gates.
    apply (proj2 (bind_get_model _ _ _ _)). cbv beta zeta. gates.
    apply alt_r, alt_r. eapply bind_ok_nil; [apply (choose_ok _ ENOMEM); left; reflexivity|].
    eapply bind_ok_nil; [apply modify_ok|]. apply pure_ok.
Qed.

Lemma mmap_fixed_span_refused_outcomes : forall i m,
  bv_unsigned (in_sysno i) = 222%Z ->
  mmap_off_aligned_b (in_arg i 5) = true -> mmap_anon_b (in_arg i 3) = true ->
  w_is0 (in_arg i 1) = false ->
  mmap_modeled_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_noaccess_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_fixed_noaccess_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_fixed_rw_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = true ->
  (bv_unsigned (in_arg i 0) + page_round_up_Z (bv_unsigned (in_arg i 1)) <= alloc_top (m_vmmaps m))%Z ->
  (bv_unsigned (in_arg i 0) mod page_size = 0)%Z ->
  (0 < bv_unsigned (in_arg i 0))%Z ->
  region_free (vm_reserved (m_vmmaps m)) (in_arg i 0)
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1)))) = true ->
  map_contains (vm_maps (m_vmmaps m)) (in_arg i 0)
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1)))) = false ->
  region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) (in_arg i 0)
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1)))) = false ->
  mmap_fixed_span_refusable (in_arg i 3) m (in_arg i 0)
       (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1)))) = true ->
  forall eff m' evs, syscall_spec i m (Ok eff m' evs) ->
  (eff = mkEffect (errno_ret ENOMEM) [] [] /\ m' = m /\ evs = [])
  \/ (eff = mkEffectU (errno_ret ENOMEM) [] [] [(in_arg i 0, (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1)))))] [] []
      /\ m' = with_mmap_destroyed (in_arg i 0) (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1))))
      (mmap_fixed_destroyed_next (m_vmmaps m) (in_arg i 0) (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1))))) m
      /\ evs = []).
Proof.
  intros i m E Hoff Han Hlen Hmod Hna Hfx Hfrw Hce Hal Hpos Hrr Hmc Hrf Hr eff m' evs Hs.
  fixed_prep Hlen Hce Hal Hpos.
  apply (proj1 (scfg_spec_222 _ _ _ E)) in Hs. unfold mmap_spec in Hs. gates_in Hs. cbv zeta in Hs. gates_in Hs.
  apply (proj1 (bind_get_model _ _ _ _)) in Hs. cbv beta zeta in Hs. gates_in Hs.
  unfold alt in Hs. destruct Hs as [Hs|[Hs|Hs]].
  - left. apply errno_bind_inv in Hs as (e & He & Hs). destruct He as [<-|[]].
    exact (err_ret_inv _ _ _ _ _ _ Hs).
  - apply choose_bind_inv in Hs as (u & Hb & _).
    exfalso. unfold mmap_fixed_span_refusable in Hr. rewrite Hb in Hr. cbn [negb] in Hr. discriminate Hr.
  - right. apply errno_bind_inv in Hs as (e & He & Hs). destruct He as [<-|[]].
    apply modify_bind_inv in Hs. exact (pure_inv _ _ _ _ _ _ Hs).
Qed.

(* the statement shapes Lib/NodesM consumes *)

Lemma mmap_rw_nonspur : forall i m eff,
  bv_unsigned (in_sysno i) = 222%Z ->
  mmap_off_aligned_b (in_arg i 5) = true -> mmap_anon_b (in_arg i 3) = true -> w_is0 (in_arg i 1) = false ->
  mmap_modeled_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = true ->
  (~ spurious_refusal_cfg fcfg i m eff <->
   (refusal_b i m (eff_ret eff) = true ->
    mmap_grant_refusable (in_arg i 3) m (page_round_up_Z (bv_unsigned (in_arg i 1))) = true)).
Proof. exact mmap_grant_nonspur. Qed.

Lemma mmap_fixed_noaccess_nonspur : forall i m eff,
  bv_unsigned (in_sysno i) = 222%Z ->
  mmap_off_aligned_b (in_arg i 5) = true -> mmap_anon_b (in_arg i 3) = true -> w_is0 (in_arg i 1) = false ->
  mmap_modeled_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_noaccess_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = false ->
  mmap_fixed_noaccess_b (in_arg i 2) (in_arg i 3) (in_arg i 5) = true ->
  let h := m_vmmaps m in
  let nZ := page_round_up_Z (bv_unsigned (in_arg i 1)) in
  let n := Z_to_bv 64 nZ in
  (bv_unsigned (in_arg i 0) + nZ <= alloc_top h)%Z ->
  (bv_unsigned (in_arg i 0) mod page_size = 0)%Z ->
  (0 < bv_unsigned (in_arg i 0))%Z ->
  region_free (vm_reserved h) (in_arg i 0) n = true ->
  map_contains (vm_maps h) (in_arg i 0) n = true ->
  (~ spurious_refusal_cfg fcfg i m eff <-> refusal_b i m (eff_ret eff) = false).
Proof. exact mmap_fixed_none_commit_nonspur. Qed.

Lemma mprotect_expose_nonspur : forall i m eff,
  bv_unsigned (in_sysno i) = 226%Z ->
  mprotect_grows_conflict_b (in_arg i 2) = false ->
  (bv_unsigned (in_arg i 0) mod page_size = 0)%Z ->
  w_is0 (in_arg i 1) = false ->
  (bv_unsigned (in_arg i 0) + page_round_up_Z (bv_unsigned (in_arg i 1)) < two_pow_64)%Z ->
  mprotect_modeled_b (in_arg i 2) = true ->
  let h := m_vmmaps m in
  let n := Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1))) in
  map_contains (vm_noaccess h) (in_arg i 0) n = true ->
  map_contains (vm_maps h) (in_arg i 0) n = true ->
  (~ spurious_refusal_cfg fcfg i m eff <->
   (refusal_b i m (eff_ret eff) = true -> mprotect_refusable m (in_arg i 0) n = true)).
Proof. exact mprotect_nonspur. Qed.
