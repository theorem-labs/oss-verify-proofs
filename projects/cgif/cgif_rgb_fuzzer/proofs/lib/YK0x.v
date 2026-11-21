(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (munmap's refused -ENOMEM answer as a second child of the munmap node; the MAP_NORESERVE mmap lemmas over Linux's own placement, with the place_declined_b premise on the producers and on each mmap of the two-mmap chain; the write node's copy-in through a lazy ledger it misses, and its access_okb premise; each system-call node's sys_rob part; RomBase, RomWrite and Placement imports; blank lines removed). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import Placement.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK16 YK0o YK11 YK0j YK0v YK15 YK0k YK0t YK1g YK18.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import RomBase RomWrite.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations.
Open Scope bv_scope.
Section d.
Context {fx : FPState}.
Lemma materialize_syscall_effect_nil :
  forall (m : Model) (r : word) (zs us : list (word * word)),
  materialize_model_accesses m
    (syscall_effect_accesses (mkEffectU r [] zs us [] []))
  = Some m.
Proof. intros m r zs us. exact (materialize_model_accesses_nil m). Qed.
Lemma materialize_munmap_eff_nil : forall (m : Model) (ms : machine_state),
materialize_model_accesses m (syscall_effect_accesses (munmap_eff ms))
= Some m.
Proof. intros m ms. exact (materialize_model_accesses_nil m). Qed.
(* Model NoReserve.v (08b1429): the write effect's copyin through a disjoint ledger. *)
Lemma materialize_syscall_effect_copyin_disjoint :
  forall (m : Model) (r : word) (a : word) (n : nat),
  accesses_outside_lazy [(a, n)] (m_vm_lazy m) ->
  materialize_model_accesses m
    (syscall_effect_accesses (with_copyins [(a, n)] (mkEffect r [] [])))
  = Some m.
Proof.
  intros m r a n Hout.
  exact (materialize_model_accesses_disjoint m [(a, n)] Hout).
Qed.
Lemma access_outside_range_mono : forall (a : word) (n n' : nat) (lo sz : word),
  (n' <= n)%nat ->
  access_outside_range a n lo sz ->
  access_outside_range a n' lo sz.
Proof.
  intros a n n' lo sz Hle [Hnw Hd].
  split; [lia | destruct Hd as [Hd | Hd]; [left; lia | right; exact Hd]].
Qed.
Lemma accesses_outside_lazy_shrink :
  forall (a : word) (len n : nat) (lazy : list (word * word)),
  (n <= len)%nat ->
  accesses_outside_lazy [(a, len)] lazy ->
  accesses_outside_lazy [(a, n)] lazy.
Proof.
  intros a len n lazy Hle Hout a' n' lo sz Hin Hlz.
  destruct Hin as [Hin | []]. injection Hin as Ha Hn. subst a' n'.
  apply (access_outside_range_mono a len n lo sz Hle).
  apply (Hout a len lo sz); [left; reflexivity | exact Hlz].
Qed.
Definition mmap_model_noreserve (a n : word) (m : Model) : Model :=
vm_add_lazy a n (mmap_model a n m).
Definition mmap_args_ok_noreserve (ms : machine_state) : Prop :=
ms_gpr ms 1 <> Z_to_bv 64 0 /\ ms_gpr ms 2 = Z_to_bv 64 3
/\ ms_gpr ms 3 = Z_to_bv 64 16418 /\ ms_gpr ms 4 = Z_to_bv 64 (-1)
/\ ms_gpr ms 5 = Z_to_bv 64 0.
Lemma mmap_args_ok_noreserve_gates : forall ms,
mmap_args_ok_noreserve ms ->
mmap_off_aligned_b (ms_gpr ms 5) = true /\
mmap_anon_b (ms_gpr ms 3) = true /\
w_is0 (ms_gpr ms 1) = false /\
mmap_modeled_b (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 5)
= true.
Proof.
intros ms (H1 & H2 & H3 & H4 & H5).
split; [unfold mmap_off_aligned_b; rewrite H5; reflexivity|].
split; [unfold mmap_anon_b; rewrite H3; reflexivity|].
split; [unfold w_is0; apply bv_eqb_neq; exact H1|].
unfold mmap_modeled_b. rewrite H2, H3, H5. reflexivity.
Qed.
Definition grant_ok_nr (hint : word) (m : Model) (a : word) (n : Z) : bool :=
linux_place_is (m_vmmaps m) (kb_thp (m_kernel m)) hint n a
&& (bv_unsigned a mod page_size =? 0)%Z && (0 <? bv_unsigned a)%Z
&& (bv_unsigned a + n <=? alloc_top (m_vmmaps m))%Z
&& region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 n).
Lemma grant_ok_nr_intro : forall hint m a n,
(0 < n)%Z -> (n mod page_size = 0)%Z ->
linux_place_is (m_vmmaps m) (kb_thp (m_kernel m)) hint n a = true ->
grant_ok_nr hint m a n = true.
Proof.
intros hint m a n Hn Hnal Hpl.
destruct (linux_place_is_admissible _ _ _ _ _ Hn Hnal Hpl)
as (Hal & Hpos & Htop & Hfree).
unfold grant_ok_nr. rewrite Hpl, Hfree.
rewrite (proj2 (Z.eqb_eq _ _) Hal), (proj2 (Z.ltb_lt _ _) Hpos),
(proj2 (Z.leb_le _ _) Htop).
reflexivity.
Qed.
Lemma grant_ok_nr_place : forall hint m a n,
grant_ok_nr hint m a n = true ->
linux_place_is (m_vmmaps m) (kb_thp (m_kernel m)) hint n a = true.
Proof.
intros hint m a n H. unfold grant_ok_nr in H.
rewrite !andb_true_iff in H. tauto.
Qed.
Lemma grant_ok_nr_unpack : forall hint m a n,
grant_ok_nr hint m a n = true ->
(bv_unsigned a mod page_size = 0)%Z /\ (0 < bv_unsigned a)%Z /\
(bv_unsigned a + n <= alloc_top (m_vmmaps m))%Z /\
region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 n) = true.
Proof.
intros hint m a n H. unfold grant_ok_nr in H.
rewrite !andb_true_iff in H.
destruct H as [[[[_ H1] H2] H3] H4].
apply Z.eqb_eq in H1. apply Z.ltb_lt in H2. apply Z.leb_le in H3.
auto 6.
Qed.
Lemma grant_nr_not_errno : forall hint model a n,
(0 <= n)%Z -> grant_ok_nr hint model a n = true ->
errno_ret_in mmap_errnos a = false.
Proof.
intros hint model a n Hn Hg.
destruct (grant_ok_nr_unpack _ _ _ _ Hg) as (_ & _ & Hce & _).
apply errno_ret_in_below; [reflexivity|].
alloc_top_bounds. unfold two_pow_64 in *. lia.
Qed.
(* The revision's decline (Mmap.place_declined_b) sits AHEAD of the [match eff]
in the freely-placed arm, so it gates the errno refusal too: this PRODUCER is
false as it stood even though it returns a refusal. Same premise, same place as
[mmap_succ_ok_noreserve]'s. *)
Lemma mmap_fail_ok_noreserve : forall segs ms x8 model e,
bv_unsigned x8 = 222%Z -> mmap_args_ok_noreserve ms -> In e mmap_errnos ->
place_declined_b (m_kernel model) (m_vmmaps model) (ms_gpr ms 0)
  (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = false ->
syscall_spec (sys_input segs ms x8) model
(Ok (mkEffect (errno_ret e) [] []) model []).
Proof.
intros segs ms x8 model e Hno Ha HIn Hdecl.
destruct (mmap_args_ok_noreserve_gates ms Ha) as [Hoff [Hanon [Hl Hmb]]].
apply (proj2 (syscall_spec_mmap _ _ _ _ _ Hno)). apply check_mmap_sound_ok.
unfold check_mmap, check_mmap_fixed_overflow. cbv beta.
rewrite Hoff, Hanon, Hl, Hmb. cbn [negb]. cbv beta iota zeta.
rewrite Hdecl. cbv beta iota zeta.
rewrite errno_ret_in_intro by assumption. reflexivity.
Qed.
(* Model NoReserve.v (08b1429): the NORESERVE bit, read back where it changes answers. *)
Lemma mmap_noreserve_b_flags : mmap_noreserve_b (Z_to_bv 64 16418) = true.
Proof. reflexivity. Qed.
(* The revision declines a hint it cannot place (Mmap.place_declined_b, outside
the [alt]), so a PRODUCER is false as it stood: it must say that this call is
one the model answers. [grant_ok_nr] does not give it -- the condition is about
the HINT, not the chosen address. *)
Lemma mmap_succ_ok_noreserve : forall segs ms x8 model a,
bv_unsigned x8 = 222%Z ->
mmap_args_ok_noreserve ms ->
place_declined_b (m_kernel model) (m_vmmaps model) (ms_gpr ms 0)
  (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = false ->
grant_ok_nr (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true ->
syscall_spec (sys_input segs ms x8) model
(Ok (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])
(mmap_model_noreserve a (page_round_up (ms_gpr ms 1)) model) []).
Proof.
intros segs ms x8 model a Hno Ha Hdecl Hg.
destruct (mmap_args_ok_noreserve_gates ms Ha) as [Hoff [Hanon [Hl Hmb]]].
destruct Ha as (_ & _ & Hflags & _ & _).
apply (proj2 (syscall_spec_mmap _ _ _ _ _ Hno)). apply check_mmap_sound_ok.
unfold check_mmap, check_mmap_fixed_overflow. cbv beta.
rewrite Hoff, Hanon, Hl, Hmb. cbn [negb]. cbv beta iota zeta.
rewrite Hdecl. cbv beta iota zeta.
rewrite (grant_nr_not_errno (ms_gpr ms 0) model a
(page_round_up_Z (bv_unsigned (ms_gpr ms 1))));
[ | apply page_round_up_Z_nonneg; pose proof (u64_range (ms_gpr ms 1)); lia
| exact Hg ].
pose proof (grant_ok_nr_place _ _ _ _ Hg) as Hp.
rewrite Hflags.
unfold mmap_noreserve_backed_ok, with_mmap_backing.
rewrite mmap_noreserve_b_flags.
rewrite Hp. cbn [andb].
unfold page_round_up. cbn [listNN_eqb]. rewrite !bv_eqb_refl.
reflexivity.
Qed.
Lemma mmap_ok_inv_noreserve : forall segs ms x8 model eff model' evs,
bv_unsigned x8 = 222%Z ->
mmap_args_ok_noreserve ms ->
syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ->
evs = [] /\
((exists e, In e mmap_errnos /\ eff = mkEffect (errno_ret e) [] []
/\ model' = model) \/
(exists a, grant_ok_nr (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true
/\ eff = mkEffect a [] [(a, page_round_up (ms_gpr ms 1))]
/\ model' = mmap_model_noreserve a (page_round_up (ms_gpr ms 1)) model)).
Proof.
intros segs ms x8 model eff model' evs Hno Ha Hspec.
destruct (mmap_args_ok_noreserve_gates ms Ha) as [Hoff [Hanon [Hl Hmb]]].
destruct Ha as (_ & _ & Hflags & _ & _).
apply (proj1 (syscall_spec_mmap _ _ _ _ _ Hno)) in Hspec.
apply check_mmap_complete_ok in Hspec.
unfold check_mmap, check_mmap_fixed_overflow in Hspec. cbv beta in Hspec.
rewrite Hoff, Hanon, Hl, Hmb in Hspec. cbn [negb] in Hspec.
rewrite Hflags in Hspec.
(* A CONSUMER needs no premise: [CheckUnmodeled] is a different constructor
from [CheckOk], so the revision's decline branch dies by discrimination and
the statement keeps its full strength. *)
destruct (place_declined_b (m_kernel model) (m_vmmaps model) (ms_gpr ms 0)
(page_round_up_Z (bv_unsigned (ms_gpr ms 1)))) eqn:Hdecl; [discriminate|].
unfold mmap_noreserve_backed_ok, with_mmap_backing in Hspec.
rewrite mmap_noreserve_b_flags in Hspec.
destruct eff as [r ws zs us cs copyins].
cbv beta iota zeta in Hspec.
destruct ws as [|w ws]; [|discriminate].
destruct us as [|u us]; [|discriminate].
destruct cs as [|c cs]; [|discriminate].
destruct copyins as [|copyin copyins]; [|discriminate].
destruct (errno_ret_in mmap_errnos r) eqn:Herr; rewrite ?Herr in Hspec;
cbv beta iota in Hspec.
- destruct zs as [|z zs]; [|discriminate].
inversion Hspec; subst.
split; [reflexivity|]. left.
apply errno_ret_in_true in Herr. destruct Herr as (e & HIn & ->).
exists e. auto.
- rewrite andb_true_r in Hspec.
destruct (linux_place_is (m_vmmaps model) (kb_thp (m_kernel model))
(ms_gpr ms 0) (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) r)
eqn:Hcond; rewrite ?Hcond in Hspec.
2:{ rewrite andb_false_l in Hspec. discriminate. }
destruct (listNN_eqb zs
[(r, Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1))))]) eqn:Hzs;
rewrite ?Hzs in Hspec.
2:{ rewrite andb_false_r in Hspec. discriminate. }
cbn [andb] in Hspec.
apply listNN_eqb_eq in Hzs. subst zs.
inversion Hspec; subst.
split; [reflexivity|]. right.
exists r. split; [|split].
+ exact (grant_ok_nr_intro _ _ _ _ (proj1 (mmap_grant_len_ok _ Hl))
(proj2 (mmap_grant_len_ok _ Hl)) Hcond).
+ unfold page_round_up. reflexivity.
+ reflexivity.
Qed.
(* A NO-UNMODELED statement is false as it stood: the revision answers
[unmodeled] for a hint it declines. The premise says this call is not one of
those; everything below it is the old proof. *)
Lemma mmap_no_unmodeled_noreserve : forall segs ms x8 model,
bv_unsigned x8 = 222%Z ->
mmap_args_ok_noreserve ms ->
place_declined_b (m_kernel model) (m_vmmaps model) (ms_gpr ms 0)
  (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = false ->
~ syscall_spec (sys_input segs ms x8) model Unmodeled.
Proof.
intros segs ms x8 model Hno Ha Hdecl Hspec.
destruct (mmap_args_ok_noreserve_gates ms Ha) as [Hoff [Hanon [Hl Hmb]]].
apply (proj1 (syscall_spec_mmap _ _ _ _ _ Hno)) in Hspec.
apply (check_mmap_complete_unmodeled _ _ _ _ _ _ _ _ (mkEffect (Z_to_bv 64 0) [] [])) in Hspec.
unfold check_mmap, check_mmap_fixed_overflow in Hspec. cbv beta in Hspec.
rewrite Hoff, Hanon, Hl, Hmb in Hspec. cbn [negb] in Hspec.
rewrite Hdecl in Hspec.
cbv beta iota zeta in Hspec.
assert (E : errno_ret_in mmap_errnos (Z_to_bv 64 0) = false) by reflexivity.
rewrite E in Hspec. cbv beta iota in Hspec.
match type of Hspec with (if ?b then _ else _) = _ => destruct b end;
discriminate.
Qed.
Section f.
Variable segs : list Segment.
Lemma sstep_munmap_inv_lazy : forall ms model x8 evs st,
m_halted model = None ->
ms_svc_pending ms = Some x8 ->
bv_unsigned x8 = 215%Z ->
munmap_args_ok ms model ->
sstep segs (mkCfg ms model) evs st ->
evs = [] /\
((exists e, In e munmap_errnos /\
st = SNext (mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model)) \/
st = SNext (mkCfg (advance_past_svc (apply_effect ms (munmap_eff ms)))
(munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model))).
Proof.
intros ms model x8 evs st Hh Hsvc Hno Hargs Hss.
inversion Hss; subst; try congruence.
-
match goal with
| H2 : ms_svc_pending ms = Some ?x,
H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0) |- _ =>
assert (Hx : x = x8) by congruence; subst x;
destruct (munmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3)
as (Hevs & Hcase);
subst evs0
end.
split; [reflexivity|].
destruct Hcase as [(e & HIn & -> & ->) | (-> & ->)].
+ left. exists e.
match goal with
| Hmat : materialize_model_accesses model _ = Some _ |- _ =>
rewrite materialize_syscall_effect_nil in Hmat;
inversion Hmat; subst
end.
split; [assumption |].
rewrite apply_effect_no_write. reflexivity.
+ right.
match goal with
| Hmat : materialize_model_accesses
(munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) _ = Some _ |- _ =>
rewrite materialize_munmap_eff_nil in Hmat;
inversion Hmat; subst
end.
reflexivity.
-
exfalso.
match goal with
| H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
Hmat : materialize_model_accesses ?model' _ = None |- _ =>
assert (Hx : x = x8) by congruence; subst x;
destruct (munmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3)
as (_ & Hcase);
destruct Hcase as [(? & ? & -> & ->) | (-> & ->)];
[ rewrite materialize_syscall_effect_nil in Hmat
| rewrite materialize_munmap_eff_nil in Hmat ];
discriminate
end.
-
exfalso.
match goal with
| H2 : ms_svc_pending ms = Some ?x,
H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
H6 : m_halted ?model' = Some ?code |- _ =>
assert (Hx : x = x8) by congruence; subst x;
destruct (munmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3)
as (_ & Hcase);
destruct Hcase as [(? & ? & _ & ->) | (_ & ->)];
[ rewrite Hh in H6 | rewrite munmap_model_halted, Hh in H6 ];
discriminate
end.
-
exfalso.
match goal with
| H2 : ms_svc_pending ms = Some ?x,
H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
H6 : m_killed ?model' = Some _ |- _ =>
assert (Hx : x = x8) by congruence; subst x;
destruct (munmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3)
as (_ & Hcase);
destruct Hcase as [(? & ? & _ & ->) | (_ & ->)];
[ rewrite (m_killed_of_m_halted_none _ Hh) in H6
| rewrite m_killed_of_m_halted_none in H6;
[| rewrite munmap_model_halted; exact Hh] ];
discriminate
end.
-
exfalso.
match goal with
| H2 : ms_svc_pending ms = Some ?x,
H3 : syscall_spec (sys_input segs ms ?x) model Unmodeled |- _ =>
assert (Hx : x = x8) by congruence; subst x;
exact (munmap_no_unmodeled segs ms x8 model Hno Hargs H3)
end.
Qed.
Lemma node_munmap_lazy : forall ms model x8,
m_halted model = None ->
ms_svc_pending ms = Some x8 ->
bv_unsigned x8 = 215%Z ->
munmap_args_ok ms model ->
node_ok segs (mkCfg ms model) ({e : Z | In e munmap_errnos} + unit)
(fun _ => [])
(fun i => match i with
| inl (exist _ e _) =>
mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model
| inr _ =>
mkCfg (advance_past_svc (apply_effect ms (munmap_eff ms)))
(munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1))
model)
end).
Proof.
intros ms model x8 Hh Hsvc Hno Hargs. split; [| split].
- intros [[e He] | []]; cbn.
+ rewrite <- (apply_effect_no_write ms (errno_ret e)).
apply (sstep_syscall segs ms model x8 (mkEffect (errno_ret e) [] [])
model model []).
* exact Hh.
* exact Hsvc.
* apply munmap_fail_ok; assumption.
* exact Hh.
* apply materialize_syscall_effect_nil.
+ apply (sstep_syscall segs ms model x8 (munmap_eff ms)
(munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)
(munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) []).
* exact Hh.
* exact Hsvc.
* apply munmap_ok; assumption.
* rewrite munmap_model_halted; exact Hh.
* apply materialize_munmap_eff_nil.
- intros e st Hss.
destruct (sstep_munmap_inv_lazy ms model x8 e st Hh Hsvc Hno Hargs Hss)
as [-> [(er & Her & ->) | ->]].
+ exists (inl (exist _ er Her)). split; reflexivity.
+ exists (inr tt). split; reflexivity.
- exact (sys_rob_memfree segs ms model x8 Hsvc ltac:(rewrite Hno; exact memfree_215)).
Qed.
Lemma srz_munmap_lazy : forall ms model x8 T,
m_halted model = None ->
ms_svc_pending ms = Some x8 ->
bv_unsigned x8 = 215%Z ->
munmap_args_ok ms model ->
(forall e, In e munmap_errnos ->
srealizes segs (mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model) T) ->
srealizes segs (mkCfg (advance_past_svc (apply_effect ms (munmap_eff ms)))
(munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)) T ->
srealizes segs (mkCfg ms model) T.
Proof.
intros ms model x8 T Hh Hsvc Hno Hargs Hfail Hc.
apply (srz_silent_all segs (mkCfg ms model) ({e : Z | In e munmap_errnos} + unit)
(fun i => match i with
| inl (exist _ e _) =>
mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model
| inr _ =>
mkCfg (advance_past_svc (apply_effect ms (munmap_eff ms)))
(munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1))
model)
end) T (inr tt));
[apply (node_munmap_lazy ms model x8); assumption |].
intros [[e He] | []]; cbn; [exact (Hfail e He) | exact Hc].
Qed.
Lemma sstep_write_next_inv_disjoint : forall ms model x8 buf evs c',
m_halted model = None ->
accesses_outside_lazy [(ms_gpr ms 1, length buf)] (m_vm_lazy model) ->
fd1chan model ->
ms_svc_pending ms = Some x8 ->
bv_unsigned x8 = 64%Z ->
ms_gpr ms 0 = Z_to_bv 64 1 ->
ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
(1 <= length buf)%nat ->
sstep segs (mkCfg ms model) evs (SNext c') ->
exists n, (1 <= n)%nat /\ (n <= length buf)%nat /\
evs = map (WriteEv (Z_to_bv 64 1)) (firstn n buf) /\
c' = mkCfg (advance_past_svc (set_gpr0 ms (len_word (firstn n buf)))) model.
Proof.
intros ms model x8 buf evs c' Hh Hout Hfd Hsvc Hno Hg Hr Hok Hnb Hss.
inversion Hss; subst; try congruence.
-
match goal with
| H2 : ms_svc_pending ms = Some ?x, H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0) |- _ =>
assert (Hx : x = x8) by congruence; subst x;
destruct (write1_ok_inv segs ms x8 model eff model' evs0 buf Hfd Hno Hg Hr Hok Hnb H3)
as (n & Hn1 & Hn2 & Heff & Hm & Hevs);
subst eff model' evs0; exists n
end.
match goal with
| Hmat : materialize_model_accesses model _ = Some ?model'' |- _ =>
rewrite (materialize_syscall_effect_copyin_disjoint model _ _ n
(accesses_outside_lazy_shrink _ _ n _ Hn2 Hout)) in Hmat;
inversion Hmat; subst model''
end.
rewrite apply_effect_copyins_no_write. repeat split; auto.
-
exfalso.
match goal with
| H2 : ms_svc_pending ms = Some ?x,
H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
H6 : m_halted ?model' = Some ?code |- _ =>
assert (Hx : x = x8) by congruence; subst x;
destruct (write1_ok_inv segs ms x8 model eff model' evs0 buf Hfd Hno Hg Hr Hok Hnb H3)
as (n & _ & _ & _ & Hm & _);
subst model'; rewrite Hh in H6; discriminate
end.
-
exfalso.
match goal with
| H2 : ms_svc_pending ms = Some ?x,
H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
H6 : m_killed ?model' = Some _ |- _ =>
assert (Hx : x = x8) by congruence; subst x;
destruct (write1_ok_inv segs ms x8 model eff model' evs0 buf Hfd Hno Hg Hr Hok Hnb H3)
as (n & _ & _ & _ & Hm & _);
subst model'; rewrite (m_killed_of_m_halted_none _ Hh) in H6; discriminate
end.
Qed.
Lemma sstep_write_inv_disjoint : forall ms model x8 buf evs st,
m_halted model = None ->
accesses_outside_lazy [(ms_gpr ms 1, length buf)] (m_vm_lazy model) ->
fd1chan model ->
ms_svc_pending ms = Some x8 ->
bv_unsigned x8 = 64%Z ->
ms_gpr ms 0 = Z_to_bv 64 1 ->
ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
buf_modeled buf ->
(1 <= length buf)%nat ->
sstep segs (mkCfg ms model) evs st ->
exists n, (1 <= n)%nat /\ (n <= length buf)%nat /\
evs = map (WriteEv (Z_to_bv 64 1)) (firstn n buf) /\
st = SNext (mkCfg (advance_past_svc (set_gpr0 ms (len_word (firstn n buf)))) model).
Proof.
intros ms model x8 buf evs st Hh Hout Hfd Hsvc Hno Hg Hr Hok Hcnt Hnb Hss.
destruct st as [c'|].
- destruct (sstep_write_next_inv_disjoint ms model x8 buf evs c'
Hh Hout Hfd Hsvc Hno Hg Hr Hok Hnb Hss) as (n & Hn1 & Hn2 & Hevs & Hc').
exists n. repeat split; [exact Hn1 | exact Hn2 | exact Hevs | now rewrite Hc'].
-
exfalso. inversion Hss; subst; try congruence.
+ match goal with
| H2 : ms_svc_pending ms = Some ?x,
H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
Hmat : materialize_model_accesses ?model' _ = None |- _ =>
assert (Hx : x = x8) by congruence; subst x;
destruct (write1_ok_inv segs ms x8 model eff model' evs0 buf
Hfd Hno Hg Hr Hok Hnb H3)
as (n & _ & Hn2 & Heff & Hm & _);
subst eff model';
rewrite (materialize_syscall_effect_copyin_disjoint model _ _ n
(accesses_outside_lazy_shrink _ _ n _ Hn2 Hout)) in Hmat;
discriminate
end.
+ match goal with
| H2 : ms_svc_pending ms = Some ?x,
H3 : syscall_spec (sys_input segs ms ?x) model Unmodeled |- _ =>
assert (Hx : x = x8) by congruence; subst x;
apply (write1_no_unmodeled segs ms x8 model buf Hfd Hno Hg Hr Hcnt Hnb H3)
end.
Qed.
Lemma node_write1_disjoint : forall ms model x8 buf,
m_halted model = None ->
accesses_outside_lazy [(ms_gpr ms 1, length buf)] (m_vm_lazy model) ->
fd1chan model ->
ms_svc_pending ms = Some x8 ->
bv_unsigned x8 = 64%Z ->
ms_gpr ms 0 = Z_to_bv 64 1 ->
ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
buf_modeled buf ->
(1 <= length buf)%nat ->
node_ok segs (mkCfg ms model) (wr_index buf)
(fun i => map (WriteEv (Z_to_bv 64 1)) (firstn (proj1_sig i) buf))
(fun i => mkCfg (advance_past_svc
(set_gpr0 ms (len_word (firstn (proj1_sig i) buf))))
model).
Proof.
intros ms model x8 buf Hh Hout Hfd Hsvc Hno Hg Hr Hok Hbm Hnb. split; [| split].
- intros [n [Hn1 Hn2]]. cbn [proj1_sig].
rewrite <- (apply_effect_copyins_no_write ms (len_word (firstn n buf))
[(ms_gpr ms 1, n)]).
apply (sstep_syscall segs ms model x8
(with_copyins [(ms_gpr ms 1, n)]
(mkEffect (len_word (firstn n buf)) [] [])) model
model (map (WriteEv (Z_to_bv 64 1)) (firstn n buf))).
+ exact Hh.
+ exact Hsvc.
+ apply write1_ok_n; assumption.
+ exact Hh.
+ apply materialize_syscall_effect_copyin_disjoint.
exact (accesses_outside_lazy_shrink _ _ n _ Hn2 Hout).
- intros e st Hss.
destruct (sstep_write_inv_disjoint ms model x8 buf e st
Hh Hout Hfd Hsvc Hno Hg Hr Hok Hbm Hnb Hss)
as (n & Hn1 & Hn2 & -> & ->).
exists (exist _ n (conj Hn1 Hn2)). split; reflexivity.
- exact (write_ch_rob segs ms model x8 (Z_to_bv 64 1) (Z_to_bv 64 1) buf (fd1chan_fdchan model Hfd)
ltac:(reflexivity) Hsvc Hno Hg Hr Hbm).
Qed.
Lemma srz_write1_disjoint : forall ms model x8 buf T,
m_halted model = None ->
accesses_outside_lazy [(ms_gpr ms 1, length buf)] (m_vm_lazy model) ->
fd1chan model ->
ms_svc_pending ms = Some x8 ->
bv_unsigned x8 = 64%Z ->
ms_gpr ms 0 = Z_to_bv 64 1 ->
ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
buf_modeled buf ->
(1 <= length buf)%nat ->
(forall n, (1 <= n)%nat -> (n <= length buf)%nat ->
srealizes segs (mkCfg (advance_past_svc
(set_gpr0 ms (len_word (firstn n buf)))) model) T) ->
srealizes segs (mkCfg ms model) (t_write_ch (Z_to_bv 64 1) buf T).
Proof.
intros ms model x8 buf T Hh Hout Hfd Hsvc Hno Hg Hr Hok Hbm Hnb Hc.
unfold t_write_ch.
apply (srz_node segs (mkCfg ms model) (wr_index buf)
(fun i => map (WriteEv (Z_to_bv 64 1)) (firstn (proj1_sig i) buf))
(fun i => mkCfg (advance_past_svc
(set_gpr0 ms (len_word (firstn (proj1_sig i) buf))))
model)
(fun _ => T) (wr_full buf Hnb)).
- apply (node_write1_disjoint ms model x8 buf); assumption.
- intros [n [Hn1 Hn2]]. cbn [proj1_sig]. apply Hc; assumption.
Qed.
Inductive msteps_acc
: machine_state -> machine_state -> list (word * nat) -> Prop :=
| msta_refl : forall ms, msteps_acc ms ms []
| msta_step : forall ms ms1 ms2 ranges accs,
ms_svc_pending ms = None ->
RiscvSemantics.step_accesses segs ms
= MachineOk (@mkAccessReport machine_state ms1 ranges) ->
msteps_acc ms1 ms2 accs ->
msteps_acc ms ms2 (ranges ++ accs).
End f.
End d.
Ltac stepacc_pipeline Hfetch Hecall Hdecode :=
unfold RiscvSemantics.step_accesses;
cbn [ms_pc ms_pc_val mkst];
rewrite Hfetch;
cbv beta iota;
unfold RiscvSemantics.decode_exec_accesses;
rewrite Hecall;
cbv beta iota;
rewrite Hdecode;
cbv beta iota zeta delta
[RiscvSemantics.interp_eff_accesses
RiscvSemantics.width_bytes RiscvSemantics.width_bytesZ
Sem.exec Sem.load_val Sem.store_val
Sem.rget Sem.rset Sem.with_regs Sem.with_pc Sem.with_resv
Sem.inval_resv Sem.w0 Sem.w1
Sem.c_regs Sem.c_fregs Sem.c_pc Sem.c_fcsr Sem.c_resv
ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom mkst];
rewrite ?bv_eqb0_is_x0.
Section g.
Context {fx : FPState}.
Section h.
Variable segs : list Segment.
Variables (ms1 : machine_state) (model : Model) (x8a : word).
Hypothesis Hh : m_halted model = None.
Hypothesis Hfd : fd1chan model.
Hypothesis Hsvc1 : ms_svc_pending ms1 = Some x8a.
Hypothesis Hno1 : bv_unsigned x8a = 222%Z.
Hypothesis Hargs1 : mmap_args_ok_noreserve ms1.
(* Shape and placement taken from the model's own two-mmap section,
727298f3:theories/Common/NoReserve.v:1836-1842 (Hdecl1) and :1874-1879
(Hdecl2): the revision's decline is a fact about each call's HINT, so each
ecall in the chain carries its own, against the model it runs on. *)
Hypothesis Hdecl1 :
place_declined_b (m_kernel model) (m_vmmaps model) (ms_gpr ms1 0)
  (page_round_up_Z (bv_unsigned (ms_gpr ms1 1))) = false.
Let nZ1 : Z := page_round_up_Z (bv_unsigned (ms_gpr ms1 1)).
Let n1 : word := page_round_up (ms_gpr ms1 1).
Let model1 (a1 : word) : Model := mmap_model_noreserve a1 n1 model.
Let post1 (a1 : word) : machine_state :=
advance_past_svc (apply_effect ms1 (mkEffect a1 [] [(a1, n1)])).
Hypothesis Hrefuse1 : forall e, In e mmap_errnos ->
to_spin segs (advance_past_svc (set_gpr0 ms1 (errno_ret e))) model.
Hypothesis Hex1 : exists a, grant_ok_nr (ms_gpr ms1 0) model a nZ1 = true.
Variable ms2 : word -> machine_state.
Variable accs1 : word -> list (word * nat).
Hypothesis Hwalk1 : forall a1, grant_ok_nr (ms_gpr ms1 0) model a1 nZ1 = true ->
msteps_acc segs (post1 a1) (ms2 a1) (accs1 a1).
Hypothesis Hout1 : forall a1, grant_ok_nr (ms_gpr ms1 0) model a1 nZ1 = true ->
accesses_outside_lazy (accs1 a1) (m_vm_lazy (model1 a1)).
Variable x8b : word.
Hypothesis Hno2 : bv_unsigned x8b = 222%Z.
Hypothesis Hsvc2 : forall a1, grant_ok_nr (ms_gpr ms1 0) model a1 nZ1 = true ->
ms_svc_pending (ms2 a1) = Some x8b.
Hypothesis Hargs2 : forall a1, grant_ok_nr (ms_gpr ms1 0) model a1 nZ1 = true ->
mmap_args_ok (ms2 a1).
Hypothesis Hdecl2 : forall a1, grant_ok_nr (ms_gpr ms1 0) model a1 nZ1 = true ->
place_declined_b (m_kernel (model1 a1)) (m_vmmaps (model1 a1))
  (ms_gpr (ms2 a1) 0)
  (page_round_up_Z (bv_unsigned (ms_gpr (ms2 a1) 1))) = false.
Let nZ2 (a1 : word) : Z := page_round_up_Z (bv_unsigned (ms_gpr (ms2 a1) 1)).
Let n2 (a1 : word) : word := page_round_up (ms_gpr (ms2 a1) 1).
Let model2 (a1 a2 : word) : Model := mmap_model a2 (n2 a1) (model1 a1).
Let post2 (a1 a2 : word) : machine_state :=
advance_past_svc (apply_effect (ms2 a1) (mkEffect a2 [] [(a2, n2 a1)])).
Hypothesis Hrefuse2 : forall a1, grant_ok_nr (ms_gpr ms1 0) model a1 nZ1 = true ->
forall e, In e mmap_errnos ->
to_spin segs (advance_past_svc (set_gpr0 (ms2 a1) (errno_ret e))) (model1 a1).
Hypothesis Hex2 : forall a1, grant_ok_nr (ms_gpr ms1 0) model a1 nZ1 = true ->
exists a2, grant_ok (ms_gpr (ms2 a1) 0) (model1 a1) a2 (nZ2 a1) = true.
Variable ms3 : word -> word -> machine_state.
Variable accs2 : word -> word -> list (word * nat).
Hypothesis Hwalk2 : forall a1 a2,
grant_ok_nr (ms_gpr ms1 0) model a1 nZ1 = true ->
grant_ok (ms_gpr (ms2 a1) 0) (model1 a1) a2 (nZ2 a1) = true ->
msteps_acc segs (post2 a1 a2) (ms3 a1 a2) (accs2 a1 a2).
Hypothesis Hout2 : forall a1 a2,
grant_ok_nr (ms_gpr ms1 0) model a1 nZ1 = true ->
grant_ok (ms_gpr (ms2 a1) 0) (model1 a1) a2 (nZ2 a1) = true ->
accesses_outside_lazy (accs2 a1 a2) (m_vm_lazy (model2 a1 a2)).
Variable buf : list byte.
Hypothesis Hbufnb : (1 <= length buf)%nat.
Hypothesis Hbufmod : buf_modeled buf.
Variable x8c : word.
Hypothesis Hno3 : bv_unsigned x8c = 64%Z.
Hypothesis Hw_svc : forall a1 a2,
grant_ok_nr (ms_gpr ms1 0) model a1 nZ1 = true ->
grant_ok (ms_gpr (ms2 a1) 0) (model1 a1) a2 (nZ2 a1) = true ->
ms_svc_pending (ms3 a1 a2) = Some x8c.
Hypothesis Hw_fd1 : forall a1 a2,
grant_ok_nr (ms_gpr ms1 0) model a1 nZ1 = true ->
grant_ok (ms_gpr (ms2 a1) 0) (model1 a1) a2 (nZ2 a1) = true ->
ms_gpr (ms3 a1 a2) 0 = Z_to_bv 64 1.
Hypothesis Hw_read : forall a1 a2,
grant_ok_nr (ms_gpr ms1 0) model a1 nZ1 = true ->
grant_ok (ms_gpr (ms2 a1) 0) (model1 a1) a2 (nZ2 a1) = true ->
ms_read_bytes (ms3 a1 a2) (ms_gpr (ms3 a1 a2) 1) (ms_gpr (ms3 a1 a2) 2) = Some buf.
Hypothesis Hw_acc : forall a1 a2,
grant_ok_nr (ms_gpr ms1 0) model a1 nZ1 = true ->
grant_ok (ms_gpr (ms2 a1) 0) (model1 a1) a2 (nZ2 a1) = true ->
access_okb (ms_gpr (ms3 a1 a2) 1) (bv_unsigned (ms_gpr (ms3 a1 a2) 2)) = true.
Hypothesis Hw_out : forall a1 a2,
grant_ok_nr (ms_gpr ms1 0) model a1 nZ1 = true ->
grant_ok (ms_gpr (ms2 a1) 0) (model1 a1) a2 (nZ2 a1) = true ->
accesses_outside_lazy [(ms_gpr (ms3 a1 a2) 1, length buf)]
(m_vm_lazy (model2 a1 a2)).
Variable msE : word -> word -> nat -> machine_state.
Variable accs3 : word -> word -> nat -> list (word * nat).
Hypothesis Hwalk3 : forall a1 a2 n,
grant_ok_nr (ms_gpr ms1 0) model a1 nZ1 = true ->
grant_ok (ms_gpr (ms2 a1) 0) (model1 a1) a2 (nZ2 a1) = true ->
(1 <= n)%nat -> (n <= length buf)%nat ->
msteps_acc segs
(advance_past_svc (set_gpr0 (ms3 a1 a2) (len_word (firstn n buf))))
(msE a1 a2 n) (accs3 a1 a2 n).
Hypothesis Hout3 : forall a1 a2 n,
grant_ok_nr (ms_gpr ms1 0) model a1 nZ1 = true ->
grant_ok (ms_gpr (ms2 a1) 0) (model1 a1) a2 (nZ2 a1) = true ->
(1 <= n)%nat -> (n <= length buf)%nat ->
accesses_outside_lazy (accs3 a1 a2 n) (m_vm_lazy (model2 a1 a2)).
Variables (x8d : word) (cs : word).
Hypothesis HE_no : is_exit_no x8d.
Hypothesis HE_svc : forall a1 a2 n,
grant_ok_nr (ms_gpr ms1 0) model a1 nZ1 = true ->
grant_ok (ms_gpr (ms2 a1) 0) (model1 a1) a2 (nZ2 a1) = true ->
(1 <= n)%nat -> (n <= length buf)%nat ->
ms_svc_pending (msE a1 a2 n) = Some x8d.
Hypothesis HE_code : forall a1 a2 n,
grant_ok_nr (ms_gpr ms1 0) model a1 nZ1 = true ->
grant_ok (ms_gpr (ms2 a1) 0) (model1 a1) a2 (nZ2 a1) = true ->
(1 <= n)%nat -> (n <= length buf)%nat ->
bv_and (ms_gpr (msE a1 a2 n) 0) (Z_to_bv 64 255) = cs.
End h.
End g.
