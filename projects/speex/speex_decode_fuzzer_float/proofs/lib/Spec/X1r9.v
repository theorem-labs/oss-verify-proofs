(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run Monad.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1c5 X1by X1bs X1c2 X1bn X1c7.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1pe.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib Require Import TopLevel.
Import ListNotations.
Open Scope Z_scope.

Lemma live_bytes_app : forall l1 l2, live_bytes (l1 ++ l2) = live_bytes l1 + live_bytes l2.
Proof. induction l1 as [|[a n] l1 IH]; intros l2; cbn; [reflexivity| rewrite IH; lia]. Qed.
Lemma live_bytes_nonneg : forall l, 0 <= live_bytes l.
Proof. induction l as [|[a n] l IH]; cbn; [lia|]. pose proof (bv_unsigned_in_range 64 n). lia. Qed.

Lemma bv_wrap64_le : forall x, 0 <= x -> bv_unsigned (Z_to_bv 64 x) <= x.
Proof. intros x Hx. rewrite Z_to_bv_unsigned. unfold bv_wrap. apply Z.mod_le; [exact Hx|]. unfold bv_modulus. lia. Qed.

Lemma live_bytes_iv_subtract_le : forall a sz lo hi, lo <= hi -> live_bytes (iv_subtract a sz lo hi) <= bv_unsigned sz.
Proof.
intros a sz lo hi Hlh. unfold iv_subtract.
pose proof (bv_unsigned_in_range 64 a). pose proof (bv_unsigned_in_range 64 sz). unfold bv_modulus in *.
destruct (Z.ltb_spec (bv_unsigned a) lo); destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)); cbn -[Z_to_bv bv_unsigned Z.sub Z.add Z.min Z.max Z.le].
- pose proof (bv_wrap64_le (Z.min (bv_unsigned sz) (lo - bv_unsigned a)) ltac:(lia)).
pose proof (bv_wrap64_le (bv_unsigned a + bv_unsigned sz - Z.max (bv_unsigned a) hi) ltac:(lia)). lia.
- pose proof (bv_wrap64_le (Z.min (bv_unsigned sz) (lo - bv_unsigned a)) ltac:(lia)). lia.
- pose proof (bv_wrap64_le (bv_unsigned a + bv_unsigned sz - Z.max (bv_unsigned a) hi) ltac:(lia)). lia.
- lia.
Qed.

Lemma live_bytes_maps_subtract_le : forall maps lo hi, lo <= hi -> live_bytes (maps_subtract maps lo hi) <= live_bytes maps.
Proof.
induction maps as [|[a n] maps IH]; intros lo hi Hlh; cbn [maps_subtract]; [cbn; lia|].
rewrite live_bytes_app. cbn [live_bytes]. pose proof (live_bytes_iv_subtract_le a n lo hi Hlh). specialize (IH lo hi Hlh). lia.
Qed.

Lemma live_bytes_maps_subtract_all_le : forall cuts maps, live_bytes (maps_subtract_all maps cuts) <= live_bytes maps.
Proof.
induction cuts as [|[a n] cuts IH]; intros maps; cbn [maps_subtract_all]; [lia|].
eapply Z.le_trans; [apply IH|]. apply live_bytes_maps_subtract_le. pose proof (bv_unsigned_in_range 64 n). lia.
Qed.

Lemma backing_le_live : forall mo, mem_quiet mo -> vm_backing_used mo <= live_bytes (vm_maps (m_vmmaps mo)).
Proof.
intros mo [Hl Hm]. unfold vm_backing_used. rewrite Hl, Hm. cbn [maps_subtract_all length Z.of_nat].
unfold vm_backed_maps. pose proof (live_bytes_maps_subtract_all_le (vm_noaccess (m_vmmaps mo)) (vm_maps (m_vmmaps mo))). lia.
Qed.

Lemma nroom_grant_not_refusable : forall B len mo,
mem_quiet mo -> B <= vm_limit (m_vmmaps mo) ->
nroom B (NMmap 0 len (PROT_READ + PROT_WRITE) (MAP_PRIVATE + MAP_ANONYMOUS)) mo ->
mmap_grant_refusable (Z_to_bv 64 (MAP_PRIVATE + MAP_ANONYMOUS)) mo (mmap_len len) = false.
Proof.
intros B len mo Hq HB Hr. destruct (Hr eq_refl eq_refl) as [Hfit Hgap].
unfold mmap_grant_refusable. rewrite Hgap. cbn [negb orb]. rewrite orb_false_r. apply negb_false_iff.
unfold mmap_noreserve_backed_ok.
replace (mmap_noreserve_b (Z_to_bv 64 (MAP_PRIVATE + MAP_ANONYMOUS))) with false by reflexivity.
apply Z.leb_le. pose proof (backing_le_live mo Hq). lia.
Qed.

Lemma mprotect_not_refusable_of_live : forall mo a n,
mem_quiet mo -> live_bytes (vm_maps (m_vmmaps mo)) <= vm_limit (m_vmmaps mo) ->
mprotect_refusable mo a n = false.
Proof.
intros mo a n [Hl Hm] Hlive. unfold mprotect_refusable, mprotect_budget_ok, vm_backing_within_limit. apply negb_false_iff. apply Z.leb_le.
set (mo' := mprotect_model_next mo a n).
assert (Hq' : mem_quiet mo') by (subst mo'; unfold mprotect_model_next; destruct mo as [? [? ? ?] ? ? ? ? ?]; split; assumption).
pose proof (backing_le_live mo' Hq') as Hb.
assert (E1 : vm_maps (m_vmmaps mo') = vm_maps (m_vmmaps mo)) by (subst mo'; unfold mprotect_model_next; rewrite m_vmmaps_with_vmmaps; reflexivity).
assert (E2 : vm_limit (m_vmmaps mo') = vm_limit (m_vmmaps mo)) by (subst mo'; unfold mprotect_model_next; rewrite m_vmmaps_with_vmmaps; reflexivity).
rewrite E1 in Hb. rewrite E2. lia.
Qed.

Lemma nroom_reserve_not_refusable : forall B len mo,
nroom B (NMmap 0 len PROT_NONE (MAP_PRIVATE + MAP_ANONYMOUS)) mo ->
mmap_reserve_refusable mo (mmap_len len) = false.
Proof.
intros B len mo Hr. destruct (Hr eq_refl eq_refl) as [_ Hgap].
unfold mmap_reserve_refusable. rewrite Hgap. reflexivity.
Qed.

Definition nomat (mo : Model) : Prop := m_vm_materialized mo = [].

Lemma nomat_with_vmmaps : forall h mo, nomat mo -> nomat (with_vmmaps h mo).
Proof. intros h [? [? ? ?] ? ? ? ? ?] H. exact H. Qed.
Lemma nomat_with_fds : forall f mo, nomat mo -> nomat (with_fds f mo).
Proof. intros f [? [? ? ?] ? ? ? ? ?] H. exact H. Qed.
Lemma nomat_with_tid : forall t mo, nomat mo -> nomat (with_tid t mo).
Proof. intros t [? [? ? ?] ? ? ? ? ?] H. exact H. Qed.
Lemma nomat_vm_add_lazy : forall a n mo, nomat mo -> nomat (vm_add_lazy a n mo).
Proof. intros a n [? [? ? ?] ? ? ? ? ?] H. exact H. Qed.
Lemma nomat_vm_forget_range : forall lo hi mo, nomat mo -> nomat (vm_forget_range lo hi mo).
Proof. intros lo hi [? [? ? mt] ? ? ? ? ?] H. unfold nomat in *. cbn in *. subst mt. reflexivity. Qed.
Lemma nomat_forget_vm_ranges : forall rs mo, nomat mo -> nomat (forget_vm_ranges rs mo).
Proof. induction rs as [|[a n] rs IH]; intros mo H; cbn; [exact H|]. apply IH. apply nomat_vm_forget_range. exact H. Qed.
Lemma nomat_with_mmap_backing : forall flags a n mo, nomat mo -> nomat (with_mmap_backing flags a n mo).
Proof. intros. unfold with_mmap_backing. destruct (mmap_noreserve_b flags); [apply nomat_vm_add_lazy|]; assumption. Qed.
Lemma nomat_with_mmap_replacement : forall flags a n mo, nomat mo -> nomat (with_mmap_replacement flags a n mo).
Proof. intros. unfold with_mmap_replacement. apply nomat_with_mmap_backing. apply nomat_vm_forget_range. assumption. Qed.
Lemma nomat_with_mmap_destroyed : forall a n h mo, nomat mo -> nomat (with_mmap_destroyed a n h mo).
Proof. intros. unfold with_mmap_destroyed. apply nomat_vm_forget_range. apply nomat_with_vmmaps. assumption. Qed.
Lemma nomat_with_brk_next : forall mo req r, nomat mo -> nomat (with_brk_next mo req r).
Proof. intros. unfold with_brk_next. apply nomat_forget_vm_ranges. apply nomat_with_vmmaps. assumption. Qed.
Lemma nomat_mprotect_model_next : forall mo a n, nomat mo -> nomat (mprotect_model_next mo a n).
Proof. intros. unfold mprotect_model_next. apply nomat_with_vmmaps. assumption. Qed.

Definition NM {A} (m : Model) (s : Sys A) : Prop := forall i x m' evs, s i m (Ok x m' evs) -> nomat m -> nomat m'.
Section NMKit.
Local Notation bind := Monad.bind.
#[using="Type"] Lemma NM_pure {A} m (x : A) : NM m (pure x).
Proof. intros i y m' evs H. unfold pure in H. injection H as ? ? ?; subst. exact (fun q => q). Qed.
#[using="Type"] Lemma NM_err_ret m e : NM m (err_ret e). Proof. apply NM_pure. Qed.
#[using="Type"] Lemma NM_ret_only m r : NM m (ret_only r). Proof. apply NM_pure. Qed.
#[using="Type"] Lemma NM_unmodeled {A} m : NM m (@unmodeled A). Proof. intros i y m' evs H. discriminate H. Qed.
#[using="Type"] Lemma NM_bind {A B} m (s : Sys A) (k : A -> Sys B) :
(forall i x m1 e1, s i m (Ok x m1 e1) -> (nomat m -> nomat m1) /\ NM m1 (k x)) -> NM m (bind s k).
Proof.
intros H i y m' evs Hb Q. unfold bind in Hb. destruct Hb as (x & m1 & e1 & e2 & H1 & H2 & ->).
destruct (H _ _ _ _ H1) as [N1 K]. exact (K _ _ _ _ H2 (N1 Q)).
Qed.
#[using="Type"] Lemma NM_bind_get_model {B} m (k : Model -> Sys B) : NM m (k m) -> NM m (bind get_model k).
Proof. intros H. apply NM_bind. intros i x m1 e1 E. unfold get_model in E. injection E as ? ? ?; subst. auto. Qed.
#[using="Type"] Lemma NM_bind_get_vmmaps {B} m (k : VmMaps -> Sys B) : NM m (k (m_vmmaps m)) -> NM m (bind get_vmmaps k).
Proof. intros H. apply NM_bind. intros i x m1 e1 E. unfold get_vmmaps in E. injection E as ? ? ?; subst. auto. Qed.
#[using="Type"] Lemma NM_bind_choose {A B} m (P : A -> Prop) (k : A -> Sys B) : (forall x, P x -> NM m (k x)) -> NM m (bind (choose P) k).
Proof. intros H. apply NM_bind. intros i x m1 e1 E. unfold choose in E. destruct E as (y & Py & E). injection E as ? ? ?; subst. auto. Qed.
#[using="Type"] Lemma NM_bind_errno_from {B} m l (k : Z -> Sys B) : (forall e, In e l -> NM m (k e)) -> NM m (bind (errno_from l) k).
Proof. intros H. unfold errno_from. apply NM_bind_choose. exact H. Qed.
#[using="Type"] Lemma NM_bind_modify {B} m F (k : unit -> Sys B) : (nomat m -> nomat (F m)) -> NM (F m) (k tt) -> NM m (bind (modify F) k).
Proof. intros HF H. apply NM_bind. intros i x m1 e1 E. unfold modify in E. injection E as ? ? ?; subst. auto. Qed.
#[using="Type"] Lemma NM_alt {A} m (a b : Sys A) : NM m a -> NM m b -> NM m (alt a b).
Proof. intros Ha Hb i x m' evs [H|H]; [apply (Ha _ _ _ _ H)| apply (Hb _ _ _ _ H)]. Qed.
End NMKit.

Ltac nomat_tac :=
let Q := fresh "Q" in intros Q;
repeat first [ exact Q | apply nomat_with_mmap_backing | apply nomat_with_mmap_replacement | apply nomat_with_mmap_destroyed
| apply nomat_with_vmmaps | apply nomat_with_brk_next | apply nomat_mprotect_model_next | apply nomat_vm_forget_range
| apply nomat_forget_vm_ranges | apply nomat_with_fds | apply nomat_with_tid ].

Ltac nm_tac :=
cbv beta zeta;
lazymatch goal with
| |- NM _ (Monad.bind get_model _) => apply NM_bind_get_model; nm_tac
| |- NM _ (Monad.bind get_vmmaps _) => apply NM_bind_get_vmmaps; nm_tac
| |- NM _ (Monad.bind (choose _) _) => apply NM_bind_choose; intros ? ?; nm_tac
| |- NM _ (Monad.bind (errno_from _) _) => apply NM_bind_errno_from; intros ? ?; nm_tac
| |- NM _ (Monad.bind (modify _) _) => apply NM_bind_modify; [nomat_tac | nm_tac]
| |- NM _ (Monad.bind ?s _) => let h := sp_head s in progress unfold h; nm_tac
| |- NM _ (alt _ _) => apply NM_alt; nm_tac
| |- NM _ (match ?b with true => _ | false => _ end) => destruct b eqn:?; nm_tac
| |- NM _ (match ?x with _ => _ end) => destruct x eqn:?; nm_tac
| |- NM _ (pure _) => apply NM_pure
| |- NM _ (ret_only _) => apply NM_ret_only
| |- NM _ (err_ret _) => apply NM_err_ret
| |- NM _ unmodeled => apply NM_unmodeled
| |- NM _ ?s => let h := sp_head s in first [progress unfold h; nm_tac | fail 2 "nm_tac stuck:" s]
end.

Lemma mmap_spec_NM : forall addr len prot flags fd off m, NM m (mmap_spec addr len prot flags fd off).
Proof. intros. nm_tac. Qed.

Lemma mmap_spec_nomat : forall addr len prot flags fd off i m rsp m',
mmap_spec addr len prot flags fd off i m (Ok rsp m' []) -> nomat m -> nomat m'.
Proof. intros addr len prot flags fd off i m rsp m' H Q. exact (mmap_spec_NM addr len prot flags fd off m _ _ _ _ H Q). Qed.

Theorem nstep_nomat : forall n mo rsp mo' evs, nstep n mo rsp mo' evs -> nomat mo -> nomat mo'.
Proof.
intros n mo rsp mo' evs Hst. destruct n.
- destruct Hst as [-> _]. auto.
- destruct Hst as [-> _]. auto.
- cbn [nstep] in Hst. destruct Hst as [-> Hst].
assert (Hor : forall ent eff mo1, open_result mo ent eff mo1 -> nomat mo -> nomat mo1).
{ intros ent eff mo1 [(e & _ & _ & ->)|(_ & _ & ->)]; [auto| apply nomat_with_fds]. }
destruct (path_max <=? length path)%nat; [destruct Hst as [_ ->]; auto|].
destruct path as [|c p]; [destruct Hst as [_ ->]; auto|].
destruct (path_eqb (c :: p) dot_path); [eapply Hor; exact Hst|].
destruct (fs_lookup (m_fs mo) (c :: p)); [eapply Hor; exact Hst| destruct Hst as [_ ->]; auto].
- cbn [nstep] in Hst. destruct Hst as [-> Hst].
destruct (fd_lookup (m_fds mo) (Z_to_bv 64 fd)) as [[c|p o|p o|p o|p o| |s0|pp w|nrd nwr| ]|]; try (destruct Hst as [_ ->]; auto; fail); try contradiction.
destruct (fs_lookup (m_fs mo) p); [|contradiction]. destruct Hst as [_ ->]. apply nomat_with_fds.
- cbn [nstep] in Hst. destruct Hst as (-> & _ & Hst). destruct (fd_lookup (m_fds mo) (Z_to_bv 64 fd)); destruct Hst as [_ ->]; [apply nomat_with_fds| auto].
- destruct Hst as (-> & _ & ->). auto.
- cbn [nstep] in Hst. destruct Hst as (-> & t & _ & Ht). destruct (m_tid mo); destruct Ht as [_ ->]; [auto| apply nomat_with_tid].
- destruct Hst.
- apply nstep_brk_iff in Hst as (-> & r & _ & _ & -> & ->). apply nomat_with_brk_next.
- apply nstep_mmap_spec in Hst as [-> Hst]. intros Q. eapply mmap_spec_nomat; [exact (proj1 Hst)| exact Q].
- apply nstep_munmap_iff in Hst as [-> Hst]. unfold munmap_out in Hst. cbv zeta in Hst.
repeat match type of Hst with (if ?c then _ else _) => destruct c end;
first [apply Ok_inj in Hst as (-> & -> & _) | exfalso; exact (Unmodeled_Ok _ _ _ (eq_sym Hst))]; auto; apply nomat_with_mmap_destroyed.
- apply nstep_mprotect_spec in Hst as [-> Hst]. apply mprotect_outcome in Hst. unfold mprotect_out in Hst. cbv zeta in Hst.
repeat match type of Hst with (if ?c then _ else _) => destruct c | _ \/ _ => destruct Hst as [(? & ? & ? & Hst)|(? & Hst)] end;
first [apply Ok_inj in Hst as (-> & -> & _) | exfalso; exact (Unmodeled_Ok _ _ _ (eq_sym Hst))]; auto; apply nomat_mprotect_model_next.
Qed.

Lemma mem_quiet_of : forall mo, minv mo -> nomat mo -> mem_quiet mo.
Proof. intros mo Hm Hn. split; [apply (minv_nolazy mo Hm)| exact Hn]. Qed.
