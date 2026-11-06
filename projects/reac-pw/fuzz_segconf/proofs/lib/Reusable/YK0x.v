(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YK0x.v, with its module paths changed. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YK16 YK0n YK11 YK0i YK0v YK15 YK0j YK0t YK1g YK18.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable.R Require Import Cfg.
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
Lemma materialize_munmap_eff_nil : forall (m : Model) (ms : machine_state),
materialize_model_accesses m (syscall_effect_accesses (munmap_eff ms))
= Some m.
Proof. intros m ms. exact (materialize_model_accesses_nil m). Qed.
Lemma access_outside_range_mono : forall (a : word) (n n' : nat) (lo sz : word),
(n' <= n)%nat ->
access_outside_range a n lo sz ->
access_outside_range a n' lo sz.
Proof.
intros a n n' lo sz Hle [Hnw Hd].
split; [lia | destruct Hd as [Hd | Hd]; [left; lia | right; exact Hd]].
Qed.
Lemma accesses_outside_lazy_incl :
forall (accs accs' : list (word * nat)) (lazy : list (word * word)),
(forall x, In x accs' -> In x accs) ->
accesses_outside_lazy accs lazy ->
accesses_outside_lazy accs' lazy.
Proof.
intros accs accs' lazy Hincl Hout a n lo sz Hin Hlz.
exact (Hout a n lo sz (Hincl _ Hin) Hlz).
Qed.
Lemma accesses_outside_lazy_app_l :
forall accs1 accs2 lazy,
accesses_outside_lazy (accs1 ++ accs2) lazy ->
accesses_outside_lazy accs1 lazy.
Proof.
intros accs1 accs2 lazy Hout.
apply (accesses_outside_lazy_incl (accs1 ++ accs2)); [| exact Hout].
intros x Hx. apply in_or_app. left. exact Hx.
Qed.
Lemma accesses_outside_lazy_app_r :
forall accs1 accs2 lazy,
accesses_outside_lazy (accs1 ++ accs2) lazy ->
accesses_outside_lazy accs2 lazy.
Proof.
intros accs1 accs2 lazy Hout.
apply (accesses_outside_lazy_incl (accs1 ++ accs2)); [| exact Hout].
intros x Hx. apply in_or_app. right. exact Hx.
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
Lemma mmap_model_noreserve_halted : forall a n m,
m_halted (mmap_model_noreserve a n m) = m_halted m.
Proof. reflexivity. Qed.
Lemma mmap_model_noreserve_fs : forall a n m,
m_fs (mmap_model_noreserve a n m) = m_fs m.
Proof. reflexivity. Qed.
Lemma mmap_model_noreserve_fd1chan : forall a n m,
fd1chan m -> fd1chan (mmap_model_noreserve a n m).
Proof. intros a n m H. exact H. Qed.
Lemma mmap_model_noreserve_lazy : forall a n m,
m_vm_lazy (mmap_model_noreserve a n m) = lazy_interior a n ++ m_vm_lazy m.
Proof. reflexivity. Qed.
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
Lemma mmap_noreserve_b_flags : mmap_noreserve_b (Z_to_bv 64 16418) = true.
Proof. reflexivity. Qed.
Definition grant_ok_nr (hint : word) (m : Model) (a : word) (n : Z) : bool :=
(bv_unsigned a mod page_size =? 0)%Z && (0 <? bv_unsigned a)%Z
&& (bv_unsigned a + n <=? alloc_top (m_vmmaps m))%Z
&& region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 n).
Lemma grant_ok_nr_unpack : forall hint m a n,
grant_ok_nr hint m a n = true ->
(bv_unsigned a mod page_size = 0)%Z /\ (0 < bv_unsigned a)%Z /\
(bv_unsigned a + n <= alloc_top (m_vmmaps m))%Z /\
region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 n) = true.
Proof.
intros hint m a n H. unfold grant_ok_nr in H.
rewrite !andb_true_iff in H.
destruct H as [[[H1 H2] H3] H4].
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
Section f.
Variable segs : list Segment.
Lemma sstep_munmap_inv_lazy : forall ms model x8 evs st,
m_halted model = None ->
ms_svc_pending ms = Some x8 ->
bv_unsigned x8 = 215%Z ->
munmap_args_ok ms model ->
sstep segs (mkCfg ms model) evs st ->
evs = [] /\
st = SNext (mkCfg (advance_past_svc (apply_effect ms (munmap_eff ms)))
(munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)).
Proof.
intros ms model x8 evs st Hh Hsvc Hno Hargs Hss.
inversion Hss; subst; try congruence.
-
match goal with
| H2 : ms_svc_pending ms = Some ?x,
H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0) |- _ =>
assert (Hx : x = x8) by congruence; subst x;
destruct (munmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3) as (Heff & Hm & Hevs);
subst eff model' evs0
end.
match goal with
| Hmat : materialize_model_accesses
(munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) _ = Some _ |- _ =>
rewrite materialize_munmap_eff_nil in Hmat;
inversion Hmat; subst
end.
split; reflexivity.
-
exfalso.
match goal with
| H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
Hmat : materialize_model_accesses ?model' _ = None |- _ =>
assert (Hx : x = x8) by congruence; subst x;
destruct (munmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3)
as (Heff & Hm & Hevs); subst eff model' evs0;
rewrite materialize_munmap_eff_nil in Hmat;
discriminate
end.
-
exfalso.
match goal with
| H2 : ms_svc_pending ms = Some ?x,
H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
H6 : m_halted ?model' = Some ?code |- _ =>
assert (Hx : x = x8) by congruence; subst x;
destruct (munmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3) as (_ & Hm & _);
subst model'; rewrite munmap_model_halted, Hh in H6; discriminate
end.
-
exfalso.
match goal with
| H2 : ms_svc_pending ms = Some ?x,
H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
H6 : m_killed ?model' = Some _ |- _ =>
assert (Hx : x = x8) by congruence; subst x;
destruct (munmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3) as (_ & Hm & _);
subst model'; rewrite m_killed_of_m_halted_none in H6;
[ discriminate | rewrite munmap_model_halted; exact Hh ]
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
node_ok segs (mkCfg ms model) unit (fun _ => [])
(fun _ => mkCfg (advance_past_svc (apply_effect ms (munmap_eff ms)))
(munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1))
model)).
Proof.
intros ms model x8 Hh Hsvc Hno Hargs.
apply node_ok_of_pnode; [eapply transparent_nonalloc_no; [exact Hsvc | exact Hno | reflexivity]|]. split.
- intros []. apply (sstep_syscall segs ms model x8 (munmap_eff ms)
(munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)
(munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) []).
+ exact Hh.
+ exact Hsvc.
+ apply munmap_ok; assumption.
+ rewrite munmap_model_halted; exact Hh.
+ apply materialize_munmap_eff_nil.
- intros e st Hss.
destruct (sstep_munmap_inv_lazy ms model x8 e st Hh Hsvc Hno Hargs Hss)
as [-> ->].
exists tt. split; reflexivity.
Qed.
Lemma srz_munmap_lazy : forall ms model x8 T,
m_halted model = None ->
ms_svc_pending ms = Some x8 ->
bv_unsigned x8 = 215%Z ->
munmap_args_ok ms model ->
srealizes segs (mkCfg (advance_past_svc (apply_effect ms (munmap_eff ms)))
(munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)) T ->
srealizes segs (mkCfg ms model) T.
Proof.
intros ms model x8 T Hh Hsvc Hno Hargs Hc.
eapply srz_silent1; [apply (node_munmap_lazy ms model x8); assumption | exact Hc].
Qed.
Lemma sstep_write_next_inv_disjoint : forall ms model x8 buf evs c',
m_halted model = None ->
accesses_outside_lazy [(ms_gpr ms 1, length buf)] (m_vm_lazy model) ->
fd1chan model ->
ms_svc_pending ms = Some x8 ->
bv_unsigned x8 = 64%Z ->
ms_gpr ms 0 = Z_to_bv 64 1 ->
ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
(1 <= length buf)%nat ->
sstep segs (mkCfg ms model) evs (SNext c') ->
exists n, (1 <= n)%nat /\ (n <= length buf)%nat /\
evs = map (WriteEv (Z_to_bv 64 1)) (firstn n buf) /\
c' = mkCfg (advance_past_svc (set_gpr0 ms (len_word (firstn n buf)))) model.
Proof.
intros ms model x8 buf evs c' Hh Hout Hfd Hsvc Hno Hg Hr Hnb Hss.
inversion Hss; subst; try congruence.
-
match goal with
| H2 : ms_svc_pending ms = Some ?x, H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0) |- _ =>
assert (Hx : x = x8) by congruence; subst x;
destruct (write1_ok_inv segs ms x8 model eff model' evs0 buf Hfd Hno Hg Hr Hnb H3)
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
destruct (write1_ok_inv segs ms x8 model eff model' evs0 buf Hfd Hno Hg Hr Hnb H3)
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
destruct (write1_ok_inv segs ms x8 model eff model' evs0 buf Hfd Hno Hg Hr Hnb H3)
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
buf_modeled buf ->
(1 <= length buf)%nat ->
sstep segs (mkCfg ms model) evs st ->
exists n, (1 <= n)%nat /\ (n <= length buf)%nat /\
evs = map (WriteEv (Z_to_bv 64 1)) (firstn n buf) /\
st = SNext (mkCfg (advance_past_svc (set_gpr0 ms (len_word (firstn n buf)))) model).
Proof.
intros ms model x8 buf evs st Hh Hout Hfd Hsvc Hno Hg Hr Hcnt Hnb Hss.
destruct st as [c'|].
- destruct (sstep_write_next_inv_disjoint ms model x8 buf evs c'
Hh Hout Hfd Hsvc Hno Hg Hr Hnb Hss) as (n & Hn1 & Hn2 & Hevs & Hc').
exists n. repeat split; [exact Hn1 | exact Hn2 | exact Hevs | now rewrite Hc'].
-
exfalso. inversion Hss; subst; try congruence.
+ match goal with
| H2 : ms_svc_pending ms = Some ?x,
H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
Hmat : materialize_model_accesses ?model' _ = None |- _ =>
assert (Hx : x = x8) by congruence; subst x;
destruct (write1_ok_inv segs ms x8 model eff model' evs0 buf
Hfd Hno Hg Hr Hnb H3)
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
buf_modeled buf ->
(1 <= length buf)%nat ->
node_ok segs (mkCfg ms model) (wr_index buf)
(fun i => map (WriteEv (Z_to_bv 64 1)) (firstn (proj1_sig i) buf))
(fun i => mkCfg (advance_past_svc
(set_gpr0 ms (len_word (firstn (proj1_sig i) buf))))
model).
Proof.
intros ms model x8 buf Hh Hout Hfd Hsvc Hno Hg Hr Hbm Hnb.
apply node_ok_of_pnode; [eapply transparent_nonalloc_no; [exact Hsvc | exact Hno | reflexivity]|]. split.
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
Hh Hout Hfd Hsvc Hno Hg Hr Hbm Hnb Hss)
as (n & Hn1 & Hn2 & -> & ->).
exists (exist _ n (conj Hn1 Hn2)). split; reflexivity.
Qed.
Lemma srz_write1_disjoint : forall ms model x8 buf T,
m_halted model = None ->
accesses_outside_lazy [(ms_gpr ms 1, length buf)] (m_vm_lazy model) ->
fd1chan model ->
ms_svc_pending ms = Some x8 ->
bv_unsigned x8 = 64%Z ->
ms_gpr ms 0 = Z_to_bv 64 1 ->
ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
buf_modeled buf ->
(1 <= length buf)%nat ->
(forall n, (1 <= n)%nat -> (n <= length buf)%nat ->
srealizes segs (mkCfg (advance_past_svc
(set_gpr0 ms (len_word (firstn n buf)))) model) T) ->
srealizes segs (mkCfg ms model) (t_write_ch (Z_to_bv 64 1) buf T).
Proof.
intros ms model x8 buf T Hh Hout Hfd Hsvc Hno Hg Hr Hbm Hnb Hc.
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
Lemma msteps_acc_one : forall ms ms' ranges,
ms_svc_pending ms = None ->
RiscvSemantics.step_accesses segs ms
= MachineOk (@mkAccessReport machine_state ms' ranges) ->
msteps_acc ms ms' ranges.
Proof.
intros ms ms' ranges Hsvc Hstep.
rewrite <- (app_nil_r ranges).
eapply msta_step; [exact Hsvc | exact Hstep | apply msta_refl].
Qed.
Lemma msteps_acc_trans : forall ms ms' ms'' accs1 accs2,
msteps_acc ms ms' accs1 -> msteps_acc ms' ms'' accs2 ->
msteps_acc ms ms'' (accs1 ++ accs2).
Proof.
intros ms ms' ms'' accs1 accs2 H; revert accs2 ms''.
induction H as [ms | ms ms1 ms2 ranges accs Hsvc Hstep H IH];
intros accs2 ms'' H2; [exact H2|].
rewrite <- app_assoc. eapply msta_step; eauto.
Qed.
Lemma srz_msteps_disjoint : forall ms ms' model accs T,
m_halted model = None ->
msteps_acc ms ms' accs ->
accesses_outside_lazy accs (m_vm_lazy model) ->
srealizes segs (mkCfg ms' model) T ->
srealizes segs (mkCfg ms model) T.
Proof.
intros ms ms' model accs T Hh Hms; revert T;
induction Hms as [ms | ms ms1 ms2 ranges accs Hsvc Hstep Hms IH];
intros T Hout Hc; [exact Hc|].
eapply srz_step_disjoint;
[ exact Hh | exact Hsvc | exact Hstep
| exact (accesses_outside_lazy_app_l ranges accs _ Hout)
| apply IH; [exact (accesses_outside_lazy_app_r ranges accs _ Hout) | exact Hc] ].
Qed.
Lemma rz_msteps_disjoint : forall ms ms' model accs T,
m_halted model = None ->
msteps_acc ms ms' accs ->
accesses_outside_lazy accs (m_vm_lazy model) ->
realizes segs (mkCfg ms' model) T ->
realizes segs (mkCfg ms model) T.
Proof.
intros ms ms' model accs T Hh Hms; revert T;
induction Hms as [ms | ms ms1 ms2 ranges accs Hsvc Hstep Hms IH];
intros T Hout Hc; [exact Hc|].
eapply rz_step_disjoint;
[ exact Hh | exact Hsvc | exact Hstep
| exact (accesses_outside_lazy_app_l ranges accs _ Hout)
| apply IH; [exact (accesses_outside_lazy_app_r ranges accs _ Hout) | exact Hc] ].
Qed.
Lemma ts_msteps_disjoint : forall ms ms' model accs,
msteps_acc ms ms' accs ->
accesses_outside_lazy accs (m_vm_lazy model) ->
to_spin segs ms' model ->
to_spin segs ms model.
Proof.
intros ms ms' model accs Hms;
induction Hms as [ms | ms ms1 ms2 ranges accs Hsvc Hstep Hms IH];
intros Hout Hspin; [exact Hspin|].
eapply ts_step_disjoint;
[ exact Hsvc | exact Hstep
| exact (accesses_outside_lazy_app_l ranges accs _ Hout)
| apply IH; [exact (accesses_outside_lazy_app_r ranges accs _ Hout) | exact Hspin] ].
Qed.
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
Lemma stepacc_opimm_gen : forall segs regs pc mem rom w op rd rs (imm : bv 12),
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (OpImm op rd rs imm, 4%Z) ->
RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
MachineOk (@mkAccessReport machine_state
(mkst (if bv_eqb rd 0 then regs
else regupd regs rd (alu64 op (getr regs rs) (sext 64 imm)))
(v_addi pc 4) mem rom) []).
Proof.
intros segs regs pc mem rom w op rd rs imm Hfetch Hecall Hdecode.
stepacc_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0.
destruct (is_x0 rs); cbv beta iota;
destruct (is_x0 rd); cbv beta iota;
rewrite ?b_npc4; reflexivity.
Qed.
Lemma stepacc_shiftimm_gen : forall segs regs pc mem rom w op rd rs (sh : bv 6),
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (ShiftImm op rd rs sh, 4%Z) ->
RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
MachineOk (@mkAccessReport machine_state
(mkst (if bv_eqb rd 0 then regs
else regupd regs rd (alu64 op (getr regs rs) (zext 64 sh)))
(v_addi pc 4) mem rom) []).
Proof.
intros segs regs pc mem rom w op rd rs sh Hfetch Hecall Hdecode.
stepacc_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0.
destruct (is_x0 rs); cbv beta iota;
destruct (is_x0 rd); cbv beta iota;
rewrite ?b_npc4; reflexivity.
Qed.
Lemma stepacc_op_gen : forall segs regs pc mem rom w op rd rs1 rs2,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Op op rd rs1 rs2, 4%Z) ->
RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
MachineOk (@mkAccessReport machine_state
(mkst (if bv_eqb rd 0 then regs
else regupd regs rd (alu64 op (getr regs rs1) (getr regs rs2)))
(v_addi pc 4) mem rom) []).
Proof.
intros segs regs pc mem rom w op rd rs1 rs2 Hfetch Hecall Hdecode.
stepacc_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0.
destruct (is_x0 rs1); cbv beta iota;
destruct (is_x0 rs2); cbv beta iota;
destruct (is_x0 rd); cbv beta iota;
rewrite ?b_npc4; reflexivity.
Qed.
Lemma stepacc_opimm32_gen : forall segs regs pc mem rom w rd rs (imm : bv 12),
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (OpImm32 rd rs imm, 4%Z) ->
RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
MachineOk (@mkAccessReport machine_state
(mkst (if bv_eqb rd 0 then regs
else regupd regs rd (sext 64 (alu32 ALU_ADD (low32 (getr regs rs)) (sext 32 imm))))
(v_addi pc 4) mem rom) []).
Proof.
intros segs regs pc mem rom w rd rs imm Hfetch Hecall Hdecode.
stepacc_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0.
destruct (is_x0 rs); cbv beta iota;
destruct (is_x0 rd); cbv beta iota;
rewrite ?b_npc4; reflexivity.
Qed.
Lemma stepacc_shiftimm32_gen : forall segs regs pc mem rom w op rd rs (sh : bv 5),
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (ShiftImm32 op rd rs sh, 4%Z) ->
RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
MachineOk (@mkAccessReport machine_state
(mkst (if bv_eqb rd 0 then regs
else regupd regs rd (sext 64 (alu32 op (low32 (getr regs rs)) (zext 32 sh))))
(v_addi pc 4) mem rom) []).
Proof.
intros segs regs pc mem rom w op rd rs sh Hfetch Hecall Hdecode.
stepacc_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0.
destruct (is_x0 rs); cbv beta iota;
destruct (is_x0 rd); cbv beta iota;
rewrite ?b_npc4; reflexivity.
Qed.
Lemma stepacc_op32_gen : forall segs regs pc mem rom w op rd rs1 rs2,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Op32 op rd rs1 rs2, 4%Z) ->
RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
MachineOk (@mkAccessReport machine_state
(mkst (if bv_eqb rd 0 then regs
else regupd regs rd (sext 64 (alu32 op (low32 (getr regs rs1)) (low32 (getr regs rs2)))))
(v_addi pc 4) mem rom) []).
Proof.
intros segs regs pc mem rom w op rd rs1 rs2 Hfetch Hecall Hdecode.
stepacc_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0.
destruct (is_x0 rs1); cbv beta iota;
destruct (is_x0 rs2); cbv beta iota;
destruct (is_x0 rd); cbv beta iota;
rewrite ?b_npc4; reflexivity.
Qed.
Lemma stepacc_mul_gen : forall segs regs pc mem rom w op rd rs1 rs2,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Mul op rd rs1 rs2, 4%Z) ->
RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
MachineOk (@mkAccessReport machine_state
(mkst (if bv_eqb rd 0 then regs
else regupd regs rd (mul_div op (getr regs rs1) (getr regs rs2)))
(v_addi pc 4) mem rom) []).
Proof.
intros segs regs pc mem rom w op rd rs1 rs2 Hfetch Hecall Hdecode.
stepacc_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0.
destruct (is_x0 rs1); cbv beta iota;
destruct (is_x0 rs2); cbv beta iota;
destruct (is_x0 rd); cbv beta iota;
rewrite ?b_npc4; reflexivity.
Qed.
Lemma stepacc_mul32_gen : forall segs regs pc mem rom w op rd rs1 rs2,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Mul32 op rd rs1 rs2, 4%Z) ->
RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
MachineOk (@mkAccessReport machine_state
(mkst (if bv_eqb rd 0 then regs
else regupd regs rd (sext 64 (mul_div op (low32 (getr regs rs1)) (low32 (getr regs rs2)))))
(v_addi pc 4) mem rom) []).
Proof.
intros segs regs pc mem rom w op rd rs1 rs2 Hfetch Hecall Hdecode.
stepacc_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0.
destruct (is_x0 rs1); cbv beta iota;
destruct (is_x0 rs2); cbv beta iota;
destruct (is_x0 rd); cbv beta iota;
rewrite ?b_npc4; reflexivity.
Qed.
Lemma stepacc_branch_tk_gen : forall segs regs pc mem rom w c rs1 rs2 (imm : bv 13),
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Branch c rs1 rs2 imm, 4%Z) ->
branch_taken c (getr regs rs1) (getr regs rs2) = true ->
RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
MachineOk (@mkAccessReport machine_state
(mkst regs (btgt pc (bv_signed imm)) mem rom) []).
Proof.
intros segs regs pc mem rom w c rs1 rs2 imm Hfetch Hecall Hdecode Hc.
stepacc_pipeline Hfetch Hecall Hdecode.
unfold getr in Hc; rewrite ?bv_eqb0_is_x0 in Hc.
destruct (is_x0 rs1); destruct (is_x0 rs2);
cbv beta iota; rewrite Hc; cbv beta iota;
rewrite b_addsext; reflexivity.
Qed.
Lemma stepacc_branch_ft_gen : forall segs regs pc mem rom w c rs1 rs2 (imm : bv 13),
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Branch c rs1 rs2 imm, 4%Z) ->
branch_taken c (getr regs rs1) (getr regs rs2) = false ->
RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
MachineOk (@mkAccessReport machine_state
(mkst regs (v_addi pc 4) mem rom) []).
Proof.
intros segs regs pc mem rom w c rs1 rs2 imm Hfetch Hecall Hdecode Hc.
stepacc_pipeline Hfetch Hecall Hdecode.
unfold getr in Hc; rewrite ?bv_eqb0_is_x0 in Hc.
destruct (is_x0 rs1); destruct (is_x0 rs2);
cbv beta iota; rewrite Hc; cbv beta iota;
rewrite b_npc4; reflexivity.
Qed.
Lemma stepacc_lui : forall segs regs pc mem rom w rd (imm : bv 20),
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Lui rd imm, 4%Z) ->
RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
MachineOk (@mkAccessReport machine_state
(mkst (if bv_eqb rd 0 then regs
else regupd regs rd (v_lui (Z.shiftl (bv_signed imm) 12)))
(v_addi pc 4) mem rom) []).
Proof.
intros segs regs pc mem rom w rd imm Hfetch Hecall Hdecode.
stepacc_pipeline Hfetch Hecall Hdecode.
destruct (is_x0 rd); cbv beta iota;
rewrite ?b_npc4, ?b_lui; reflexivity.
Qed.
Lemma stepacc_auipc : forall segs regs pc mem rom w rd (imm : bv 20),
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Auipc rd imm, 4%Z) ->
RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
MachineOk (@mkAccessReport machine_state
(mkst (if bv_eqb rd 0 then regs
else regupd regs rd (v_auipc pc (Z.shiftl (bv_signed imm) 12)))
(v_addi pc 4) mem rom) []).
Proof.
intros segs regs pc mem rom w rd imm Hfetch Hecall Hdecode.
stepacc_pipeline Hfetch Hecall Hdecode.
destruct (is_x0 rd); cbv beta iota;
rewrite ?b_npc4, ?b_auipc; reflexivity.
Qed.
Lemma stepacc_jal_x0 : forall segs regs pc mem rom w (imm : bv 21),
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Jal 0 imm, 4%Z) ->
RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
MachineOk (@mkAccessReport machine_state
(mkst regs (btgt pc (bv_signed imm)) mem rom) []).
Proof.
intros segs regs pc mem rom w imm Hfetch Hecall Hdecode.
stepacc_pipeline Hfetch Hecall Hdecode.
rewrite is_x0_0; cbv beta iota.
rewrite b_addsext. reflexivity.
Qed.
Lemma stepacc_jalr_gen : forall segs regs pc mem rom w rd rs1 (imm : bv 12),
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Jalr rd rs1 imm, 4%Z) ->
RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
MachineOk (@mkAccessReport machine_state
(mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_addi pc 4))
(jalr_tgt (getr regs rs1) (bv_signed imm)) mem rom) []).
Proof.
intros segs regs pc mem rom w rd rs1 imm Hfetch Hecall Hdecode.
stepacc_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0.
destruct (is_x0 rs1); cbv beta iota;
destruct (is_x0 rd); cbv beta iota;
rewrite ?b_jalr, ?b_npc4; reflexivity.
Qed.
Lemma stepacc_ecall : forall segs regs pc mem rom w,
fetch_word segs pc = Some w -> is_ecall w = true ->
RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
MachineOk (@mkAccessReport machine_state
{| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
ms_svc_pending := Some (getr regs 17);
ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := rom |}
[]).
Proof.
intros segs regs pc mem rom w Hfetch Hecall.
unfold RiscvSemantics.step_accesses.
cbn [ms_pc ms_pc_val mkst].
rewrite Hfetch. cbv beta iota.
unfold RiscvSemantics.decode_exec_accesses.
rewrite Hecall. cbv beta iota.
reflexivity.
Qed.
Lemma stepacc_lbu : forall segs regs pc mem rom w rd rs (imm : bv 12) b,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Load SZ1 false rd rs imm, 4%Z) ->
rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 1%nat = Some [b] ->
RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
MachineOk (@mkAccessReport machine_state
(mkst (if bv_eqb rd 0 then regs else regupd regs rd (Z_to_bv 64 (bv_unsigned b)))
(v_addi pc 4) mem rom)
[(v_addi (getr regs rs) (bv_signed imm), 1%nat)]).
Proof.
intros segs regs pc mem rom w rd rs imm b Hfetch Hecall Hdecode Hread.
assert (Hz : zext 64 (bv_extract 0 8 (le_bytes_to_word [b])) = Z_to_bv 64 (bv_unsigned b)).
{ rewrite le_word_1, b_extract8_id. apply bv_eq.
unfold zext. rewrite bv_zero_extend_unsigned by lia.
rewrite Z_to_bv_unsigned. symmetry. apply bv_wrap_small.
pose proof (u8_range b). change (bv_modulus 64) with (2^64)%Z. lia. }
stepacc_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0.
unfold getr in Hread; rewrite ?bv_eqb0_is_x0 in Hread.
rewrite ov_rdn, b_addsext, Hread; cbv beta iota.
rewrite Hz, b_npc4.
destruct (is_x0 rd); cbv beta iota;
reflexivity.
Qed.
Lemma stepacc_lb : forall segs regs pc mem rom w rd rs (imm : bv 12) b,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Load SZ1 true rd rs imm, 4%Z) ->
rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 1%nat = Some [b] ->
RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
MachineOk (@mkAccessReport machine_state
(mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_lb b))
(v_addi pc 4) mem rom)
[(v_addi (getr regs rs) (bv_signed imm), 1%nat)]).
Proof.
intros segs regs pc mem rom w rd rs imm b Hfetch Hecall Hdecode Hread.
stepacc_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0.
unfold getr in Hread; rewrite ?bv_eqb0_is_x0 in Hread.
rewrite ov_rdn, b_addsext, Hread; cbv beta iota.
rewrite b_lb_val, b_npc4.
destruct (is_x0 rd); cbv beta iota;
reflexivity.
Qed.
Lemma stepacc_lh : forall segs regs pc mem rom w rd rs (imm : bv 12) bs v,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Load SZ2 true rd rs imm, 4%Z) ->
rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 2%nat = Some bs ->
bytes_le_to_Z bs = bv_unsigned v ->
RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
MachineOk (@mkAccessReport machine_state
(mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_lh v))
(v_addi pc 4) mem rom)
[(v_addi (getr regs rs) (bv_signed imm), 2%nat)]).
Proof.
intros segs regs pc mem rom w rd rs imm bs v Hfetch Hecall Hdecode Hread Hv.
stepacc_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0.
unfold getr in Hread; rewrite ?bv_eqb0_is_x0 in Hread.
rewrite ov_rdn, b_addsext, Hread; cbv beta iota.
rewrite (le_word_v _ _ Hv), b_lh_val, b_npc4.
destruct (is_x0 rd); cbv beta iota;
reflexivity.
Qed.
Lemma stepacc_lhu : forall segs regs pc mem rom w rd rs (imm : bv 12) bs v,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Load SZ2 false rd rs imm, 4%Z) ->
rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 2%nat = Some bs ->
bytes_le_to_Z bs = bv_unsigned v ->
RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
MachineOk (@mkAccessReport machine_state
(mkst (if bv_eqb rd 0 then regs else regupd regs rd v)
(v_addi pc 4) mem rom)
[(v_addi (getr regs rs) (bv_signed imm), 2%nat)]).
Proof.
intros segs regs pc mem rom w rd rs imm bs v Hfetch Hecall Hdecode Hread Hv.
assert (Hz : zext 64 (bv_extract 0 16 v) = v).
{ pose proof (rdn_length _ _ _ _ _ Hread) as Hlen.
pose proof (bytes_le_to_Z_bound bs) as Hb.
pose proof (bytes_le_to_Z_nonneg bs) as Hnn.
rewrite Hlen in Hb. rewrite Hv in Hb, Hnn.
apply bv_eq. unfold zext.
rewrite bv_zero_extend_unsigned by lia.
rewrite bv_extract_unsigned, Z.shiftr_0_r.
apply bv_wrap_small.
change (bv_modulus 16) with 65536%Z.
change (2 ^ (8 * Z.of_nat 2))%Z with 65536%Z in Hb. lia. }
stepacc_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0.
unfold getr in Hread; rewrite ?bv_eqb0_is_x0 in Hread.
rewrite ov_rdn, b_addsext, Hread; cbv beta iota.
rewrite (le_word_v _ _ Hv), Hz, b_npc4.
destruct (is_x0 rd); cbv beta iota;
reflexivity.
Qed.
Lemma stepacc_lw : forall segs regs pc mem rom w rd rs (imm : bv 12) bs v,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Load SZ4 true rd rs imm, 4%Z) ->
rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 4%nat = Some bs ->
bytes_le_to_Z bs = bv_unsigned v ->
RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
MachineOk (@mkAccessReport machine_state
(mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_lw v))
(v_addi pc 4) mem rom)
[(v_addi (getr regs rs) (bv_signed imm), 4%nat)]).
Proof.
intros segs regs pc mem rom w rd rs imm bs v Hfetch Hecall Hdecode Hread Hv.
stepacc_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0.
unfold getr in Hread; rewrite ?bv_eqb0_is_x0 in Hread.
rewrite ov_rdn, b_addsext, Hread; cbv beta iota.
rewrite (le_word_v _ _ Hv), b_lw_val, b_npc4.
destruct (is_x0 rd); cbv beta iota;
reflexivity.
Qed.
Lemma stepacc_lwu : forall segs regs pc mem rom w rd rs (imm : bv 12) bs v,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Load SZ4 false rd rs imm, 4%Z) ->
rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 4%nat = Some bs ->
bytes_le_to_Z bs = bv_unsigned v ->
RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
MachineOk (@mkAccessReport machine_state
(mkst (if bv_eqb rd 0 then regs else regupd regs rd v)
(v_addi pc 4) mem rom)
[(v_addi (getr regs rs) (bv_signed imm), 4%nat)]).
Proof.
intros segs regs pc mem rom w rd rs imm bs v Hfetch Hecall Hdecode Hread Hv.
assert (Hz : zext 64 (bv_extract 0 32 v) = v).
{ pose proof (rdn_length _ _ _ _ _ Hread) as Hlen.
pose proof (bytes_le_to_Z_bound bs) as Hb.
pose proof (bytes_le_to_Z_nonneg bs) as Hnn.
rewrite Hlen in Hb. rewrite Hv in Hb, Hnn.
apply bv_eq. unfold zext.
rewrite bv_zero_extend_unsigned by lia.
rewrite bv_extract_unsigned, Z.shiftr_0_r.
apply bv_wrap_small.
change (bv_modulus 32) with 4294967296%Z.
change (2 ^ (8 * Z.of_nat 4))%Z with 4294967296%Z in Hb. lia. }
stepacc_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0.
unfold getr in Hread; rewrite ?bv_eqb0_is_x0 in Hread.
rewrite ov_rdn, b_addsext, Hread; cbv beta iota.
rewrite (le_word_v _ _ Hv), Hz, b_npc4.
destruct (is_x0 rd); cbv beta iota;
reflexivity.
Qed.
Lemma stepacc_ld : forall segs regs pc mem rom w rd rs (imm : bv 12) bs v,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Load SZ8 true rd rs imm, 4%Z) ->
rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 8%nat = Some bs ->
bytes_le_to_Z bs = bv_unsigned v ->
RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
MachineOk (@mkAccessReport machine_state
(mkst (if bv_eqb rd 0 then regs else regupd regs rd v)
(v_addi pc 4) mem rom)
[(v_addi (getr regs rs) (bv_signed imm), 8%nat)]).
Proof.
intros segs regs pc mem rom w rd rs imm bs v Hfetch Hecall Hdecode Hread Hv.
assert (Hz : bv_extract 0 64 v = v).
{ apply bv_eq.
rewrite bv_extract_unsigned, Z.shiftr_0_r.
apply bv_wrap_bv_unsigned. }
stepacc_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0.
unfold getr in Hread; rewrite ?bv_eqb0_is_x0 in Hread.
rewrite ov_rdn, b_addsext, Hread; cbv beta iota.
rewrite (le_word_v _ _ Hv), Hz, b_npc4.
destruct (is_x0 rd); cbv beta iota;
reflexivity.
Qed.
End g.
