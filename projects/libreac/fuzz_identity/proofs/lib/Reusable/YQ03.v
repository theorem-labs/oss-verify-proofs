(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from projects/cgif/cgif_file_fuzzer/proofs/lib/YQ03.v, with its module paths changed. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Run Specs.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import SyscallTable.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YQ00.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope. Open Scope bv_scope. Open Scope sys_scope.
Set Default Proof Mode "Classic".
Ltac sim_destruct e ::= destruct e eqn:?.
Section Mm.
Variable L0 L : Z.
Hypothesis HLE : L <= L0.
Lemma within_limit_mono : forall m, vm_limit (m_vmmaps m) = L0 ->
vm_backing_within_limit (relim L m) = true -> vm_backing_within_limit m = true.
Proof.
intros m HM. unfold vm_backing_within_limit. rewrite rr_vm_backing_used, rr_m_vmmaps, rr_vm_limit, HM.
intros H. apply Z.leb_le in H. apply Z.leb_le. lia.
Qed.
Lemma dir_fwd_alt_r {A} : forall i m (c c1' c2' : Sys A), DIR L0 L true i m c c2' -> DIR L0 L true i m c (alt c1' c2').
Proof. intros i m c c1' c2' H o Ho. destruct (H o Ho) as (o0 & H0 & R). exists o0. split; [right; exact H0 | exact R]. Qed.
Lemma dir_bwd_alt_r {A} : forall i m (c1 c2 c' : Sys A), DIR L0 L false i m c2 c' -> DIR L0 L false i m (alt c1 c2) c'.
Proof. intros i m c1 c2 c' H o Ho. destruct (H o Ho) as (o0 & H0 & R). exists o0. split; [right; exact H0 | exact R]. Qed.
Ltac crunch_guard G :=
autorewrite with relim_rw in G; lazy beta zeta in G;
repeat match goal with
| H : ?x = true |- _ => lazymatch x with true => fail | _ => rewrite H in G end
| H : ?x = false |- _ => tryif constr_eq H G then fail else (lazymatch x with false => fail | _ => rewrite H in G end)
| H : ?x = Some _ |- _ => rewrite H in G
| H : ?x = None |- _ => lazymatch x with None => fail | _ => rewrite H in G end
end;
lazy beta iota zeta in G.
Lemma mprotect_model_next_relim : forall m a n, mprotect_model_next (relim L m) a n = relim L (mprotect_model_next m a n).
Proof. intros m a n. unfold mprotect_model_next. commute. Qed.
Lemma mprotect_budget_ok_relim : forall m a n, vm_limit (m_vmmaps m) = L0 ->
mprotect_budget_ok (relim L m) a n = true -> mprotect_budget_ok m a n = true.
Proof.
intros m a n HM. unfold mprotect_budget_ok. rewrite mprotect_model_next_relim. apply within_limit_mono.
unfold mprotect_model_next. mok.
Qed.
Lemma mprotect_gate_off : forall i m,
mprotect_budget_refused_b (in_arg i 0) (in_arg i 1) (in_arg i 2) (relim L m) = false ->
mprotect_grows_conflict_b (in_arg i 2) = false -> negb (bv_unsigned (in_arg i 0) mod page_size =? 0) = false ->
w_is0 (in_arg i 1) = false -> (two_pow_64 <=? bv_unsigned (in_arg i 0) + page_round_up_Z (bv_unsigned (in_arg i 1))) = false ->
mprotect_modeled_b (in_arg i 2) = true ->
(map_contains (vm_noaccess (m_vmmaps m)) (in_arg i 0) (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1)))) &&
map_contains (vm_maps (m_vmmaps m)) (in_arg i 0) (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1)))))%bool = true ->
mprotect_budget_ok (relim L m) (in_arg i 0) (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1)))) = true.
Proof.
intros i m GD E0 E1 E2 E3 E4 E5. unfold mprotect_budget_refused_b in GD. rewrite E0, E1, E2, E3, E4 in GD. lazy zeta in GD.
rewrite rr_m_vmmaps, rr_vm_noaccess, rr_vm_maps in GD. rewrite E5 in GD.
destruct (mprotect_budget_ok (relim L m) (in_arg i 0) (Z_to_bv 64 (page_round_up_Z (bv_unsigned (in_arg i 1))))); [reflexivity | discriminate GD].
Qed.
Lemma sim_mprotect : forall (d : bool) i m, MOK L0 m ->
mprotect_budget_refused_b (in_arg i 0) (in_arg i 1) (in_arg i 2) (relim L m) = false ->
DIR L0 L d i m (mprotect_spec (in_arg i 0) (in_arg i 1) (in_arg i 2)) (mprotect_spec (in_arg i 0) (in_arg i 1) (in_arg i 2)).
Proof.
intros d i m HM GD. sim_arm m HM.
all: lazymatch goal with
| E5 : (map_contains _ _ _ && map_contains _ _ _)%bool = true, E4 : mprotect_modeled_b _ = true,
E3 : (two_pow_64 <=? _) = false, E1 : w_is0 _ = false, E0 : negb _ = false, E : mprotect_grows_conflict_b _ = false |- _ =>
pose proof (mprotect_gate_off i m GD E E0 E1 E3 E4 E5) as GOFF
end.
-
destruct d; intros _ H; [exact (mprotect_budget_ok_relim _ _ _ HM H) | exact GOFF].
Qed.
Lemma forget_vm_ranges_relim : forall rs m, forget_vm_ranges rs (relim L m) = relim L (forget_vm_ranges rs m).
Proof. induction rs as [|[a n] rs IH]; intros m; [reflexivity|]. cbn [forget_vm_ranges]. rewrite <- IH. reflexivity. Qed.
Lemma forget_vm_ranges_limit : forall rs m, vm_limit (m_vmmaps (forget_vm_ranges rs m)) = vm_limit (m_vmmaps m).
Proof. induction rs as [|[a n] rs IH]; intros m; [reflexivity|]. cbn [forget_vm_ranges]. rewrite IH. reflexivity. Qed.
Lemma with_brk_next_relim : forall m req r, with_brk_next (relim L m) req r = relim L (with_brk_next m req r).
Proof. intros. unfold with_brk_next. rewrite <- forget_vm_ranges_relim. reflexivity. Qed.
Lemma with_brk_next_limit : forall m req r, vm_limit (m_vmmaps (with_brk_next m req r)) = vm_limit (m_vmmaps m).
Proof. intros. unfold with_brk_next. rewrite forget_vm_ranges_limit. reflexivity. Qed.
Lemma brk_budget_ok_mono : forall m r, vm_limit (m_vmmaps m) = L0 -> brk_budget_ok (relim L m) r = true -> brk_budget_ok m r = true.
Proof.
intros m r HM. unfold brk_budget_ok. rewrite rr_vm_backing_used, rr_m_vmmaps, rr_vm_limit, rr_vm_brk, HM.
intros H. apply Z.leb_le in H. apply Z.leb_le. lia.
Qed.
Lemma brk_r_ok_fwd : forall m req r, vm_limit (m_vmmaps m) = L0 -> brk_r_ok (relim L m) req r = true -> brk_r_ok m req r = true.
Proof.
intros m req r HM. unfold brk_r_ok, brk_grow_ok, min_brk. autorewrite with relim_rw.
destruct (w_is0 req || (bv_unsigned req <? bv_unsigned (vm_start_brk (m_vmmaps m))))%bool; [intros H; exact H|].
destruct (bv_unsigned req <? bv_unsigned (vm_brk (m_vmmaps m))); [intros H; exact H|].
destruct ((0 <? bv_unsigned (vm_brk (m_vmmaps m))) && (bv_unsigned (vm_brk (m_vmmaps m)) <? bv_unsigned r))%bool; [|intros H; exact H].
rewrite !andb_true_iff. intros (H1 & H2 & H3). repeat split; try assumption. exact (brk_budget_ok_mono _ _ HM H3).
Qed.
Lemma brk_r_ok_bwd : forall m req r, vm_limit (m_vmmaps m) = L0 -> brk_budget_refused_b (relim L m) req = false ->
brk_r_ok m req r = true -> brk_r_ok (relim L m) req r = true.
Proof.
intros m req r HM GD. unfold brk_r_ok, brk_grow_ok, min_brk. unfold brk_budget_refused_b, min_brk in GD. autorewrite with relim_rw in GD. autorewrite with relim_rw.
destruct (w_is0 req || (bv_unsigned req <? bv_unsigned (vm_start_brk (m_vmmaps m))))%bool eqn:E1; [intros H; exact H|]. cbn [negb andb] in GD.
destruct (bv_unsigned req <? bv_unsigned (vm_brk (m_vmmaps m))) eqn:E2; [intros H; exact H|].
destruct ((0 <? bv_unsigned (vm_brk (m_vmmaps m))) && (bv_unsigned (vm_brk (m_vmmaps m)) <? bv_unsigned r))%bool eqn:E3; [|intros H; exact H].
rewrite !andb_true_iff. intros (H1 & H2 & H3). repeat split; try assumption.
apply andb_true_iff in E3. destruct E3 as [E3a E3b]. rewrite E3a in GD. cbn [andb] in GD.
apply orb_true_iff in H1.
destruct H1 as [H1|H1]; [apply bv_eqb_eq in H1; subst r | apply bv_eqb_eq in H1; subst r; rewrite Z.ltb_irrefl in E3b; discriminate].
rewrite E3b in GD; cbn [andb] in GD; destruct (brk_budget_ok (relim L m) req); [reflexivity | discriminate].
Qed.
Lemma sim_brk : forall (d : bool) i m, MOK L0 m ->
(d = false -> brk_budget_refused_b (relim L m) (in_arg i 0) = false) ->
DIR L0 L d i m (brk_spec (in_arg i 0)) (brk_spec (in_arg i 0)).
Proof.
intros d i m HM GD. unfold MOK in HM. unfold brk_spec.
apply dir_bind_get_model; rw_proj.
apply dir_bind_choose.
{ destruct d; intros x; [apply brk_r_ok_fwd; exact HM | apply brk_r_ok_bwd; [exact HM | exact (GD eq_refl)]]. }
intros x Hx. apply dir_bind.
{ apply dir_modify; [apply with_brk_next_relim | unfold MOK; rewrite with_brk_next_limit; exact HM]. }
intros u m1 HM1. apply dir_pure; [reflexivity | exact HM1].
Qed.
Lemma vm_forget_range_relim : forall lo hi m, vm_forget_range lo hi (relim L m) = relim L (vm_forget_range lo hi m).
Proof. reflexivity. Qed.
Lemma vm_add_lazy_relim : forall a n m, vm_add_lazy a n (relim L m) = relim L (vm_add_lazy a n m).
Proof. reflexivity. Qed.
Lemma with_mmap_backing_relim : forall f a n m, with_mmap_backing f a n (relim L m) = relim L (with_mmap_backing f a n m).
Proof. intros. unfold with_mmap_backing. destruct (mmap_noreserve_b f); reflexivity. Qed.
Lemma with_mmap_replacement_relim : forall f a n m, with_mmap_replacement f a n (relim L m) = relim L (with_mmap_replacement f a n m).
Proof. intros. unfold with_mmap_replacement. rewrite vm_forget_range_relim. apply with_mmap_backing_relim. Qed.
Lemma with_vmmaps_relim : forall h m, with_vmmaps (relimV L h) (relim L m) = relim L (with_vmmaps h m).
Proof. reflexivity. Qed.
Lemma mmap_fixed_rw_next_relim : forall h a n, mmap_fixed_rw_next (relimV L h) a n = relimV L (mmap_fixed_rw_next h a n).
Proof. reflexivity. Qed.
Lemma mmap_fixed_rw_span_next_relim : forall h a n, mmap_fixed_rw_span_next (relimV L h) a n = relimV L (mmap_fixed_rw_span_next h a n).
Proof. reflexivity. Qed.
Lemma with_mmap_backing_limit : forall f a n m, vm_limit (m_vmmaps (with_mmap_backing f a n m)) = vm_limit (m_vmmaps m).
Proof. intros. unfold with_mmap_backing. destruct (mmap_noreserve_b f); reflexivity. Qed.
Lemma with_mmap_replacement_limit : forall f a n m, vm_limit (m_vmmaps (with_mmap_replacement f a n m)) = vm_limit (m_vmmaps m).
Proof. intros. unfold with_mmap_replacement. rewrite with_mmap_backing_limit. reflexivity. Qed.
Lemma mmap_noreserve_backed_ok_mono : forall f m nZ, vm_limit (m_vmmaps m) = L0 ->
mmap_noreserve_backed_ok f (relim L m) nZ = true -> mmap_noreserve_backed_ok f m nZ = true.
Proof.
intros f m nZ HM. unfold mmap_noreserve_backed_ok. rewrite rr_vm_backing_used, rr_m_vmmaps, rr_vm_limit, HM.
destruct (mmap_noreserve_b f); [intros H; exact H|]. intros H. apply Z.leb_le in H. apply Z.leb_le. lia.
Qed.
Lemma mmap_fixed_rw_budget_ok_mono : forall f m a n, vm_limit (m_vmmaps m) = L0 ->
mmap_fixed_rw_budget_ok f (relim L m) a n = true -> mmap_fixed_rw_budget_ok f m a n = true.
Proof.
intros f m a n HM. unfold mmap_fixed_rw_budget_ok. rewrite rr_m_vmmaps, mmap_fixed_rw_next_relim, with_vmmaps_relim, with_mmap_replacement_relim.
apply within_limit_mono. rewrite with_mmap_replacement_limit. exact HM.
Qed.
Lemma mmap_fixed_rw_span_budget_ok_mono : forall f m a n, vm_limit (m_vmmaps m) = L0 ->
mmap_fixed_rw_span_budget_ok f (relim L m) a n = true -> mmap_fixed_rw_span_budget_ok f m a n = true.
Proof.
intros f m a n HM. unfold mmap_fixed_rw_span_budget_ok. rewrite rr_m_vmmaps, mmap_fixed_rw_span_next_relim, with_vmmaps_relim, with_mmap_replacement_relim.
apply within_limit_mono. rewrite with_mmap_replacement_limit. exact HM.
Qed.
Ltac gate_fwd mono HM := intros ? Hx; repeat match type of Hx with _ /\ _ => destruct Hx as [? Hx] end; repeat split; try assumption; exact (mono Hx) || (eapply mono; [exact HM | exact Hx]).
Ltac gate_bwd GD mark := intros ? Hx; repeat match type of Hx with _ /\ _ => destruct Hx as [? Hx] end; repeat split; try assumption;
lazymatch goal with |- ?g = true => destruct g eqn:?; [reflexivity | exfalso; unfold mark in GD; crunch_guard GD; try discriminate GD] end.
Lemma sim_mmap : forall (d : bool) i m, MOK L0 m ->
mmap_budget_refused_b (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) (relim L m) = false ->
DIR L0 L d i m (mmap_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5))
(mmap_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5)).
Proof.
intros d i m HM GD. sim_arm m HM.
all: destruct d; [ first [ gate_fwd (mmap_noreserve_backed_ok_mono (in_arg i 3) m) HM
| gate_fwd (mmap_fixed_rw_budget_ok_mono (in_arg i 3) m) HM
| gate_fwd (mmap_fixed_rw_span_budget_ok_mono (in_arg i 3) m) HM ]
| gate_bwd GD mmap_budget_refused_b ].
Qed.
Definition MV_OK (m : Model) : Prop :=
forall old old_size new_size dst : word,
let h := m_vmmaps m in
let old_nZ := page_round_up_Z (bv_unsigned old_size) in
let new_nZ := page_round_up_Z (bv_unsigned new_size) in
let old_n := Z_to_bv 64 old_nZ in
let new_n := Z_to_bv 64 new_nZ in
(mremap_source_b h old old_n old_nZ && mremap_backing_uniform_b m old old_n)%bool = true ->
(old_nZ < new_nZ)%Z ->
negb (bv_eqb dst old) = true -> (bv_unsigned dst mod page_size = 0)%Z -> (0 < bv_unsigned dst)%Z ->
(bv_unsigned dst + new_nZ <= alloc_top h)%Z -> region_free (vm_reserved h ++ vm_maps h) dst new_n = true ->
(vm_backing_used (mremap_model_next m old old_n dst new_n) <= mremap_move_charge m old old_n new_n)%Z.
Lemma mremap_model_next_relim : forall m old old_n dst new_n,
mremap_model_next (relim L m) old old_n dst new_n = relim L (mremap_model_next m old old_n dst new_n).
Proof. intros. reflexivity. Qed.
Lemma mremap_model_next_limit : forall m old old_n dst new_n,
vm_limit (m_vmmaps (mremap_model_next m old old_n dst new_n)) = vm_limit (m_vmmaps m).
Proof. intros. reflexivity. Qed.
Lemma mremap_move_charge_relim : forall m old old_n new_n,
mremap_move_charge (relim L m) old old_n new_n = mremap_move_charge m old old_n new_n.
Proof. intros. reflexivity. Qed.
Lemma mremap_final_budget_b_mono : forall m old old_n dst new_n, vm_limit (m_vmmaps m) = L0 ->
mremap_final_budget_b (relim L m) old old_n dst new_n = true -> mremap_final_budget_b m old old_n dst new_n = true.
Proof.
intros m old old_n dst new_n HM. unfold mremap_final_budget_b. rewrite mremap_model_next_relim. apply within_limit_mono.
rewrite mremap_model_next_limit. exact HM.
Qed.
Lemma mremap_inplace_grow_b_mono : forall m old old_n new_n oz nz, vm_limit (m_vmmaps m) = L0 ->
mremap_inplace_grow_b (relim L m) old old_n new_n oz nz = true -> mremap_inplace_grow_b m old old_n new_n oz nz = true.
Proof.
intros m old old_n new_n oz nz HM. unfold mremap_inplace_grow_b. autorewrite with relim_rw.
rewrite !andb_true_iff. intros ((H1 & H2) & H3). repeat split; try assumption. exact (mremap_final_budget_b_mono _ _ _ _ _ HM H3).
Qed.
Lemma mremap_fresh_b_mono : forall m oz nz old old_n dst new_n, vm_limit (m_vmmaps m) = L0 ->
mremap_fresh_b (relim L m) oz nz old old_n dst new_n = true -> mremap_fresh_b m oz nz old old_n dst new_n = true.
Proof.
intros m oz nz old old_n dst new_n HM. unfold mremap_fresh_b. autorewrite with relim_rw.
rewrite !andb_true_iff. intros (((((H1 & H2) & H3) & H4) & H5) & H6). repeat split; try assumption. exact (mremap_final_budget_b_mono _ _ _ _ _ HM H6).
Qed.
Lemma mremap_grow_marks : forall m old old_size new_size flags,
mremap_budget_refused_b old old_size new_size flags (relim L m) = false ->
negb (bv_unsigned flags =? MREMAP_MAYMOVE) = false ->
negb (bv_unsigned old mod page_size =? 0) = false ->
page_align_is0_b new_size = false -> page_align_is0_b old_size = false ->
(mremap_source_b (m_vmmaps m) old (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size))) (page_round_up_Z (bv_unsigned old_size))
&& mremap_backing_uniform_b m old (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size))))%bool = true ->
(page_round_up_Z (bv_unsigned new_size) <=? page_round_up_Z (bv_unsigned old_size)) = false ->
mremap_final_budget_b (relim L m) old (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size))) old (Z_to_bv 64 (page_round_up_Z (bv_unsigned new_size))) = true
/\ mremap_move_charge m old (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size))) (Z_to_bv 64 (page_round_up_Z (bv_unsigned new_size))) <= L.
Proof.
intros m old old_size new_size flags GD E1 E2 E3 E4 E5 E6.
unfold mremap_budget_refused_b in GD. rewrite E1, E2, E3, E4 in GD. lazy zeta in GD.
replace (mremap_source_b (m_vmmaps (relim L m))) with (mremap_source_b (m_vmmaps m)) in GD by reflexivity.
replace (mremap_backing_uniform_b (relim L m)) with (mremap_backing_uniform_b m) in GD by reflexivity.
rewrite E5 in GD. cbn [negb] in GD. rewrite E6 in GD.
apply negb_false_iff in GD. apply andb_true_iff in GD. destruct GD as [G1 G2]. split; [exact G1|].
unfold mremap_move_budget_b in G2. rewrite mremap_move_charge_relim, rr_m_vmmaps, rr_vm_limit in G2. apply Z.leb_le in G2. exact G2.
Qed.
Ltac sim_hook ::=
lazymatch goal with |- DIR _ _ _ _ _ (if mremap_inplace_grow_b _ _ _ _ _ _ then _ else _) _ => fail 1 end.
Lemma sim_mremap : forall (d : bool) i m, MOK L0 m -> (d = false -> MV_OK m) ->
(d = false -> mremap_budget_refused_b (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) (relim L m) = false) ->
DIR L0 L d i m (mremap_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3)) (mremap_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3)).
Proof.
intros d i m HM MV GD. sim_arm m HM.
set (osz := in_arg i 1) in *. set (nsz := in_arg i 2) in *. set (old := in_arg i 0) in *. set (flags := in_arg i 3) in *.
set (oz := page_round_up_Z (bv_unsigned osz)) in *. set (nz := page_round_up_Z (bv_unsigned nsz)) in *.
lazymatch goal with FL : negb (bv_unsigned flags =? MREMAP_MAYMOVE) = false |- _ =>
lazymatch goal with AL : negb (bv_unsigned old mod page_size =? 0) = false |- _ =>
lazymatch goal with NZ : page_align_is0_b nsz = false |- _ =>
lazymatch goal with OZ : page_align_is0_b osz = false |- _ =>
lazymatch goal with SRC : context [map_has _ _ _] |- _ =>
lazymatch goal with UNI : context [map_contains (m_vm_lazy m) _ _] |- _ =>
lazymatch goal with NEQ : (oz =? nz) = false |- _ =>
lazymatch goal with NLT : (nz <? oz) = false |- _ =>
assert (SU : (mremap_source_b (m_vmmaps m) old (Z_to_bv 64 oz) oz && mremap_backing_uniform_b m old (Z_to_bv 64 oz))%bool = true)
by (unfold mremap_source_b, mremap_backing_uniform_b; rewrite SRC; exact UNI);
assert (NLE : (nz <=? oz) = false) by (apply Z.leb_gt; apply Z.eqb_neq in NEQ; apply Z.ltb_ge in NLT; lia);
assert (LT : (oz < nz)%Z) by (apply Z.eqb_neq in NEQ; apply Z.ltb_ge in NLT; lia);
pose proof FL as gFL; pose proof AL as gAL; pose proof NZ as gNZ; pose proof OZ as gOZ;
clear SRC UNI
end end end end end end end end.
destruct d.
-
destruct (mremap_inplace_grow_b (relim L m) old (Z_to_bv 64 oz) (Z_to_bv 64 nz) oz nz) eqn:EL.
+ rewrite (mremap_inplace_grow_b_mono _ _ _ _ _ _ HM EL). sim.
all: intros x Hx; exact (mremap_fresh_b_mono _ _ _ _ _ _ _ HM Hx).
+ destruct (mremap_inplace_grow_b m old (Z_to_bv 64 oz) (Z_to_bv 64 nz) oz nz).
* apply dir_fwd_alt_r. sim. all: intros x Hx; exact (mremap_fresh_b_mono _ _ _ _ _ _ _ HM Hx).
* sim. all: intros x Hx; exact (mremap_fresh_b_mono _ _ _ _ _ _ _ HM Hx).
-
specialize (GD eq_refl). specialize (MV eq_refl).
destruct (mremap_grow_marks m old osz nsz flags GD gFL gAL gNZ gOZ SU NLE) as [GF GM].
assert (FRESH : forall x, mremap_fresh_b m oz nz old (Z_to_bv 64 oz) x (Z_to_bv 64 nz) = true ->
mremap_fresh_b (relim L m) oz nz old (Z_to_bv 64 oz) x (Z_to_bv 64 nz) = true).
{ intros x Hx. unfold mremap_fresh_b in Hx |- *. autorewrite with relim_rw.
rewrite !andb_true_iff in Hx. destruct Hx as (((((H1 & H2) & H3) & H4) & H5) & H6).
rewrite H1, H2, H3, H4, H5. cbn [andb].
unfold mremap_final_budget_b, vm_backing_within_limit. rewrite mremap_model_next_relim, rr_vm_backing_used, rr_m_vmmaps, rr_vm_limit.
apply Z.leb_le. etransitivity; [|exact GM].
apply (MV old osz nsz x SU LT); try assumption.
+ apply Z.eqb_eq in H2. exact H2.
+ apply Z.ltb_lt in H3. exact H3.
+ apply Z.leb_le in H4. exact H4. }
destruct (mremap_inplace_grow_b m old (Z_to_bv 64 oz) (Z_to_bv 64 nz) oz nz) eqn:E0.
+ assert (EL : mremap_inplace_grow_b (relim L m) old (Z_to_bv 64 oz) (Z_to_bv 64 nz) oz nz = true).
{ unfold mremap_inplace_grow_b in E0 |- *. autorewrite with relim_rw. rewrite !andb_true_iff in E0. destruct E0 as ((E0a & E0b) & _).
rewrite E0a, E0b. cbn [andb]. cbv delta [oz nz]. exact GF. }
rewrite EL. sim. all: exact FRESH.
+ destruct (mremap_inplace_grow_b (relim L m) old (Z_to_bv 64 oz) (Z_to_bv 64 nz) oz nz).
* apply dir_bwd_alt_r. sim. all: exact FRESH.
* sim. all: exact FRESH.
Qed.
End Mm.
