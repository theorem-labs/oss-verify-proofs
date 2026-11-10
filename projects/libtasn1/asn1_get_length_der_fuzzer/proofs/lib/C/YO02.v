(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Trevor Hansen, 2026-11: module names. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import DispatchCompute.
From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.C Require Import
YK11 YK0i YK0j YK14 YK1b YK15 YK0o YK0v YK02 YQ0k YN06 YN02.
From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.C Require Import YP0j YP0g YP0c.
From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.C Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section f.
Variable segs : list Segment.
Lemma knode_fallible : forall c1 q snap (Kont : Z -> config -> Prop) (J : Type) (nx : J -> config) (bit : J -> Z) (j0 : J),
fallible q = true ->
node_ok segs c1 J (fun _ => []) nx ->
(forall j, bit j = 0 \/ bit j = 1) -> bit j0 = 0 ->
(mgrant snap q -> exists j, bit j = 1) ->
(forall j, Kont (bit j) (nx j)) ->
knode segs c1 q snap Kont.
Proof.
intros c1 q snap Kont J nx bit j0 Hf Hn Hbits Hj0 Hg Hk.
destruct q; try discriminate; cbn; exists J, nx, bit, j0; (split; [exact Hn|]); (split; [exact Hk|]); repeat split; eauto.
Qed.
Lemma knode_forced : forall c1 q snap (Kont : Z -> config -> Prop) (J : Type) (nx : J -> config) (j0 : J),
fallible q = false -> (forall p, q <> KJunk p) ->
node_ok segs c1 J (fun _ => []) nx ->
(forall j, Kont 1 (nx j)) ->
knode segs c1 q snap Kont.
Proof.
intros c1 q snap Kont J nx j0 Hf Hnj Hn Hk.
destruct q; try discriminate; try (exfalso; eapply Hnj; reflexivity);
cbn; exists J, nx, (fun _ => 1), j0; (split; [exact Hn|]); split; auto.
Qed.

Lemma mreal_ask {R} : forall c q snap (k : Z -> itree astate R) Q,
SR segs c (fun c1 => knode segs c1 q snap (fun z c2 => mreal segs c2 (k z) Q)) ->
mreal segs c (IAsk q snap k) Q.
Proof. intros. exact H. Qed.
Lemma mreal_leaf {R} : forall c (r : R) Q, SR segs c (Q r) -> mreal segs c (IRet r) Q.
Proof. intros. exact H. Qed.
Definition brk_nx (regs : bvmap 5 word) (pc : word) (mem rom : word -> option byte) (model : Model)
(i : {r : word | brk_resolution_ok model (getr regs 10) r}) : config :=
let r := proj1_sig i in
mkCfg (mkst (regupd regs 10 r) (v_addi pc 4)
(apply_zeros (apply_unmaps mem (brk_unmaps r (vm_brk (m_vmmaps model))))
(brk_zeros (getr regs 10) r (vm_brk (m_vmmaps model)))) rom)
(brk_model (getr regs 10) r model).
Lemma node_brk : forall regs pc mem rom model,
m_halted model = None -> m_vm_lazy model = [] ->
bv_unsigned (getr regs 17) = 214 ->
node_ok segs (mkCfg (pend_at regs pc mem rom) model) {r : word | brk_resolution_ok model (getr regs 10) r}
(fun _ => []) (brk_nx regs pc mem rom model).
Proof.
intros regs pc mem rom model Hh Hlz Hno.
pose (J := {r : word | brk_resolution_ok model (getr regs 10) r}).
pose (ef := fun i : J =>
mkEffectU (proj1_sig i) []
(brk_zeros (getr regs 10) (proj1_sig i) (vm_brk (m_vmmaps model)))
(brk_unmaps (proj1_sig i) (vm_brk (m_vmmaps model))) [] []).
pose (md := fun i : J => brk_model (getr regs 10) (proj1_sig i) model).
pose (i0 := exist (fun r => brk_resolution_ok model (getr regs 10) r)
(vm_brk (m_vmmaps model)) (brk_resolution_ok_keep model (getr regs 10)) : J).
assert (Hn : node_ok segs (mkCfg (pend_at regs pc mem rom) model) J (fun _ => [])
(fun i => mkCfg (advance_past_svc (apply_effect (pend_at regs pc mem rom) (ef i))) (md i))).
{ apply (node_chk segs (pend_at regs pc mem rom) model (getr regs 17) J i0 ef md (fun _ => []) Hh eq_refl).
+ intros [r Hr]. unfold ef, md; cbn [proj1_sig]. apply check_syscall_ok_iff.
rewrite <- (pend_gpr0 regs pc mem rom).
apply (brk_ok_intro segs (pend_at regs pc mem rom) (getr regs 17) model r Hno).
rewrite pend_gpr0. exact Hr.
+ intros [r Hr]. unfold md. rewrite brk_model_halted. exact Hh.
+ intros [r Hr]. unfold md. apply brk_model_lazy. exact Hlz.
+ intros eff m' evs Hk. apply check_syscall_ok_iff in Hk.
apply (brk_ok_iff segs (pend_at regs pc mem rom) (getr regs 17) model eff m' evs Hno) in Hk.
rewrite pend_gpr0 in Hk. destruct Hk as (Heff & -> & Hr & ->).
exists (exist _ (eff_ret eff) Hr). unfold ef, md; cbn [proj1_sig]. rewrite <- Heff. auto. }
destruct Hn as [Hs Hc]. split.
- intros i. specialize (Hs i). unfold ef, md in Hs. rewrite adv_pend in Hs. cbn [eff_ret] in Hs.
unfold effmem in Hs. cbn [eff_unmaps eff_zeros eff_writes eff_copies apply_writes apply_copies] in Hs. exact Hs.
- intros e st Hst. destruct (Hc e st Hst) as (i & -> & ->). exists i. split; [reflexivity|].
unfold ef, md. rewrite adv_pend. cbn [eff_ret]. unfold effmem.
cbn [eff_unmaps eff_zeros eff_writes eff_copies apply_writes apply_copies]. reflexivity.
Qed.
Lemma knode_brk_query : forall regs pc mem rom model snap (Kont : Z -> config -> Prop),
m_halted model = None -> m_vm_lazy model = [] ->
bv_unsigned (getr regs 17) = 214 -> getr regs 10 = Z_to_bv 64 0 ->
Kont 1 (mkCfg (mkst (regupd regs 10 (vm_brk (m_vmmaps model))) (v_addi pc 4) mem rom)
(brk_model (Z_to_bv 64 0) (vm_brk (m_vmmaps model)) model)) ->
knode segs (mkCfg (pend_at regs pc mem rom) model) KBrkQuery snap Kont.
Proof.
intros regs pc mem rom model snap Kont Hh Hlz Hno H0 HK.
eapply (knode_forced _ KBrkQuery snap Kont _ (brk_nx regs pc mem rom model)
(exist _ (vm_brk (m_vmmaps model)) (brk_resolution_ok_keep model (getr regs 10))));
[reflexivity | intros p; discriminate | apply node_brk; assumption |].
intros [r Hr]. unfold brk_nx; cbn [proj1_sig].
pose proof Hr as Hr'. unfold brk_resolution_ok in Hr'. rewrite H0 in Hr'. apply brk_r_ok_query_iff in Hr'. subst r.
rewrite H0, brk_unmaps_keep, brk_zeros_query. cbn [apply_unmaps apply_zeros]. exact HK.
Qed.
Lemma knode_brk_grow : forall regs pc mem rom model snap (npages : Z) (Kont : Z -> config -> Prop),
let b := vm_brk (m_vmmaps model) in
m_halted model = None -> m_vm_lazy model = [] ->
bv_unsigned (getr regs 17) = 214 ->
bv_unsigned (getr regs 10) = bv_unsigned b + PGSZ * npages ->
0 < npages -> 0 < bv_unsigned b -> bv_unsigned b mod page_size = 0 ->
bv_unsigned (vm_start_brk (m_vmmaps model)) <= bv_unsigned b ->
Kont 0 (mkCfg (mkst (regupd regs 10 b) (v_addi pc 4) mem rom) (brk_model (getr regs 10) b model)) ->
(Mmap.brk_grow_ok model (getr regs 10) (getr regs 10) = true ->
Kont 1 (mkCfg (mkst (regupd regs 10 (getr regs 10)) (v_addi pc 4)
(apply_zeros mem [(b, Z_to_bv 64 (PGSZ * npages))]) rom)
(brk_model (getr regs 10) (getr regs 10) model))) ->
(mgrant snap (KBrkGrow npages) -> Mmap.brk_grow_ok model (getr regs 10) (getr regs 10) = true) ->
knode segs (mkCfg (pend_at regs pc mem rom) model) (KBrkGrow npages) snap Kont.
Proof.
intros regs pc mem rom model snap npages Kont b Hh Hlz Hno Hreq Hn Hb0 Hbal Hs HK0 HK1 HG. subst b.
pose proof (u64_range (vm_brk (m_vmmaps model))) as Hbr.
assert (Hlt : bv_unsigned (vm_brk (m_vmmaps model)) < bv_unsigned (getr regs 10)) by (unfold PGSZ in Hreq; lia).
assert (Hreq0 : getr regs 10 <> Z_to_bv 64 0).
{ intro E. rewrite E in Hreq. change (bv_unsigned (Z_to_bv 64 0)) with 0 in Hreq. unfold PGSZ in Hreq. lia. }
assert (Hru : page_round_up_Z (bv_unsigned (getr regs 10)) = bv_unsigned (vm_brk (m_vmmaps model)) + PGSZ * npages).
{ rewrite Hreq. apply page_round_up_Z_aligned; [unfold PGSZ; lia|].
unfold page_size, PGSZ in *. rewrite Z.add_mod, Hbal by lia. rewrite Z.mul_comm, Z_mod_mult. reflexivity. }
pose proof (brk_resolution_ok_grow_iff model (getr regs 10)) as Hiff. cbv zeta in Hiff.
set (bit := fun i : {r : word | brk_resolution_ok model (getr regs 10) r} =>
if bv_eqb (proj1_sig i) (getr regs 10) then 1 else 0).
eapply (knode_fallible _ (KBrkGrow npages) snap Kont _ (brk_nx regs pc mem rom model) bit
(exist _ (vm_brk (m_vmmaps model)) (brk_resolution_ok_keep model (getr regs 10))));
[reflexivity | apply node_brk; assumption | | | |].
- intros j. unfold bit. destruct (bv_eqb _ _); auto.
- unfold bit; cbn [proj1_sig]. rewrite (bv_eqb_neq _ _); [reflexivity|]. intros E. rewrite E in Hlt. lia.
- intros Hm. pose proof (HG Hm) as G.
assert (Hr : brk_resolution_ok model (getr regs 10) (getr regs 10)) by (apply (proj2 (Hiff _ Hs Hlt)); right; auto).
exists (exist _ (getr regs 10) Hr). unfold bit; cbn [proj1_sig]. rewrite bv_eqb_refl. reflexivity.
- intros [r Hr]. unfold bit, brk_nx; cbn [proj1_sig].
destruct (proj1 (Hiff _ Hs Hlt) Hr) as [-> | [-> G]].
+ rewrite (bv_eqb_neq _ _) by (intros E; rewrite E in Hlt; lia).
rewrite brk_zeros_keep, brk_unmaps_keep. cbn [apply_unmaps apply_zeros]. exact HK0.
+ rewrite bv_eqb_refl.
rewrite (brk_unmaps_grow (getr regs 10) (vm_brk (m_vmmaps model))) by lia.
rewrite (brk_zeros_aligned_grow (getr regs 10) (getr regs 10) (vm_brk (m_vmmaps model)) Hreq0 Hb0 Hlt Hbal), Hru.
replace (bv_unsigned (vm_brk (m_vmmaps model)) + PGSZ * npages - bv_unsigned (vm_brk (m_vmmaps model))) with (PGSZ * npages) by lia.
cbn [apply_unmaps]. apply HK1. exact G.
Qed.
Definition mmap_rw_J (hint : word) (model : Model) (nZ : Z) : Type :=
({e : Z | In e mmap_errnos} + {a : word | grant_ok hint model a nZ = true})%type.
Definition mmap_rw_nx (regs : bvmap 5 word) (pc : word) (mem rom : word -> option byte) (model : Model)
(i : mmap_rw_J (getr regs 10) model (page_round_up_Z (bv_unsigned (getr regs 11)))) : config :=
match i with
| inl e => mkCfg (mkst (regupd regs 10 (errno_ret (proj1_sig e))) (v_addi pc 4) mem rom) model
| inr a => mkCfg (mkst (regupd regs 10 (proj1_sig a)) (v_addi pc 4)
(apply_zeros mem [(proj1_sig a, page_round_up (getr regs 11))]) rom)
(mmap_model (proj1_sig a) (page_round_up (getr regs 11)) model)
end.
Lemma node_mmap_rw : forall regs pc mem rom model,
m_halted model = None -> m_vm_lazy model = [] ->
bv_unsigned (getr regs 17) = 222 ->
getr regs 11 <> Z_to_bv 64 0 -> getr regs 12 = Z_to_bv 64 3 ->
getr regs 13 = Z_to_bv 64 34 -> getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
node_ok segs (mkCfg (pend_at regs pc mem rom) model)
(mmap_rw_J (getr regs 10) model (page_round_up_Z (bv_unsigned (getr regs 11))))
(fun _ => []) (mmap_rw_nx regs pc mem rom model).
Proof.
intros regs pc mem rom model Hh Hlz Hno Hlen Hprot Hflags Hfd Hoff.
assert (Hargs : mmap_args_ok (pend_at regs pc mem rom)).
{ unfold mmap_args_ok. rewrite pend_gpr1, pend_gpr2, pend_gpr3, pend_gpr4, pend_gpr5. auto. }
split.
- intros [[e He] | [a Ha]]; unfold mmap_rw_nx; cbn [proj1_sig].
+ rewrite <- adv_pend_set.
rewrite <- (apply_effect_no_write (pend_at regs pc mem rom) (errno_ret e)).
apply (sstep_syscall segs (pend_at regs pc mem rom) model (getr regs 17) (mkEffect (errno_ret e) [] []) model model []).
* exact Hh. * reflexivity.
* apply mmap_fail_ok; assumption.
* exact Hh.
* apply materialize_model_accesses_no_lazy. exact Hlz.
+ rewrite <- (pend_gpr1 regs pc mem rom) in Ha.
replace (mkst (regupd regs 10 a) (v_addi pc 4) (apply_zeros mem [(a, page_round_up (getr regs 11))]) rom)
with (advance_past_svc (apply_effect (pend_at regs pc mem rom) (mkEffect a [] [(a, page_round_up (ms_gpr (pend_at regs pc mem rom) 1))]))).
2:{ rewrite adv_pend. cbn [eff_ret]. rewrite effmem_zeros, pend_gpr1. reflexivity. }
rewrite <- (pend_gpr1 regs pc mem rom).
apply (sstep_syscall segs (pend_at regs pc mem rom) model (getr regs 17) _
(mmap_model a (page_round_up (ms_gpr (pend_at regs pc mem rom) 1)) model)
(mmap_model a (page_round_up (ms_gpr (pend_at regs pc mem rom) 1)) model) []).
* exact Hh. * reflexivity.
* apply mmap_succ_ok; assumption.
* rewrite mmap_model_halted. exact Hh.
* apply materialize_model_accesses_no_lazy. exact (eq_trans (mmap_model_lazy _ _ _) Hlz).
- intros e st Hst.
destruct (sstep_mmap_inv segs (pend_at regs pc mem rom) model (getr regs 17) e st Hh Hlz eq_refl Hno Hargs Hst)
as (-> & [(err & Herr & ->) | (a & Ha & ->)]).
+ exists (inl (exist _ err Herr)). split; [reflexivity|]. unfold mmap_rw_nx; cbn [proj1_sig]. rewrite adv_pend_set. reflexivity.
+ rewrite pend_gpr1 in Ha. exists (inr (exist _ a Ha)). split; [reflexivity|]. unfold mmap_rw_nx; cbn [proj1_sig].
rewrite adv_pend. cbn [eff_ret]. rewrite effmem_zeros, pend_gpr1. reflexivity.
Qed.
Lemma knode_mmap_rw : forall regs pc mem rom model snap (len : Z) (Kont : Z -> config -> Prop),
m_halted model = None -> m_vm_lazy model = [] ->
bv_unsigned (getr regs 17) = 222 ->
getr regs 11 = Z_to_bv 64 len -> 0 < len < 2 ^ 63 -> getr regs 12 = Z_to_bv 64 3 ->
getr regs 13 = Z_to_bv 64 34 -> getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
(forall e, In e mmap_errnos ->
Kont 0 (mkCfg (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4) mem rom) model)) ->
(forall a, grant_ok (getr regs 10) model a (page_round len) = true ->
Kont 1 (mkCfg (mkst (regupd regs 10 a) (v_addi pc 4) (apply_zeros mem [(a, Z_to_bv 64 (page_round len))]) rom)
(mmap_model a (Z_to_bv 64 (page_round len)) model))) ->
(mgrant snap (KMmapRW len) -> exists a, grant_ok (getr regs 10) model a (page_round len) = true) ->
knode segs (mkCfg (pend_at regs pc mem rom) model) (KMmapRW len) snap Kont.
Proof.
intros regs pc mem rom model snap len Kont Hh Hlz Hno Hlen Hrange Hprot Hflags Hfd Hoff HK0 HK1 HG.
assert (Hlen0 : getr regs 11 <> Z_to_bv 64 0).
{ rewrite Hlen. intros E. apply (f_equal bv_unsigned) in E. rewrite !Z_to_bv_unsigned in E.
change (bv_wrap 64 0) with 0 in E. rewrite bv_wrap_small in E; [lia | change (bv_modulus 64) with (2 ^ 64); lia]. }
assert (Hru : page_round_up_Z (bv_unsigned (getr regs 11)) = page_round len).
{ rewrite Hlen, Z_to_bv_unsigned, bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); lia).
unfold page_round_up_Z, page_round, page_size, PGSZ. reflexivity. }
assert (Hpr : page_round_up (getr regs 11) = Z_to_bv 64 (page_round len)).
{ unfold page_round_up. rewrite Hru. reflexivity. }
set (bit := fun i : mmap_rw_J (getr regs 10) model (page_round_up_Z (bv_unsigned (getr regs 11))) =>
match i with inl _ => 0 | inr _ => 1 end).
eapply (knode_fallible _ (KMmapRW len) snap Kont _ (mmap_rw_nx regs pc mem rom model) bit
(inl (exist _ ENOMEM ENOMEM_in_mmap_errnos)));
[reflexivity | apply node_mmap_rw; assumption | | reflexivity | |].
- intros [|]; cbn; auto.
- intros Hm. destruct (HG Hm) as (a & Ha). rewrite <- Hru in Ha. exists (inr (exist _ a Ha)). reflexivity.
- intros [[e He] | [a Ha]]; unfold bit, mmap_rw_nx; cbn [proj1_sig].
+ apply HK0. exact He.
+ rewrite Hpr. apply HK1. rewrite <- Hru. exact Ha.
Qed.
Definition munmap_nx (regs : bvmap 5 word) (pc : word) (mem rom : word -> option byte) (model : Model) (_ : unit) : config :=
mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4)
(apply_unmaps mem [(getr regs 10, page_round_up (getr regs 11))]) rom)
(munmap_model (getr regs 10) (page_round_up (getr regs 11)) model).
Lemma node_munmap : forall regs pc mem rom model,
m_halted model = None -> m_vm_lazy model = [] ->
bv_unsigned (getr regs 17) = 215 ->
bv_unsigned (getr regs 10) mod page_size = 0 -> getr regs 11 <> Z_to_bv 64 0 ->
bv_unsigned (getr regs 10) + page_round_up_Z (bv_unsigned (getr regs 11)) <= TASK_SIZE ->
map_has (vm_maps (m_vmmaps model)) (getr regs 10) (page_round_up (getr regs 11)) = true ->
node_ok segs (mkCfg (pend_at regs pc mem rom) model) unit (fun _ => []) (munmap_nx regs pc mem rom model).
Proof.
intros regs pc mem rom model Hh Hlz Hno Hal Hlen Hnw Hhas.
assert (Hargs : munmap_args_ok (pend_at regs pc mem rom) model).
{ unfold munmap_args_ok. rewrite pend_gpr0, pend_gpr1. auto. }
assert (E : munmap_nx regs pc mem rom model tt =
mkCfg (advance_past_svc (apply_effect (pend_at regs pc mem rom) (munmap_eff (pend_at regs pc mem rom))))
(munmap_model (ms_gpr (pend_at regs pc mem rom) 0) (page_round_up (ms_gpr (pend_at regs pc mem rom) 1)) model)).
{ unfold munmap_nx, munmap_eff. rewrite pend_gpr0, pend_gpr1, adv_pend. cbn [eff_ret]. rewrite effmem_unmaps. reflexivity. }
split.
- intros []. rewrite E.
set (md' := munmap_model (ms_gpr (pend_at regs pc mem rom) 0) (page_round_up (ms_gpr (pend_at regs pc mem rom) 1)) model).
apply (sstep_syscall segs (pend_at regs pc mem rom) model (getr regs 17) _ md' md' [] Hh eq_refl).
+ apply munmap_ok; assumption.
+ unfold md'. rewrite munmap_model_halted. exact Hh.
+ apply materialize_model_accesses_no_lazy. exact (munmap_model_no_lazy _ _ _ Hlz).
- intros e st Hst.
destruct (sstep_munmap_inv segs (pend_at regs pc mem rom) model (getr regs 17) e st Hh Hlz eq_refl Hno Hargs Hst) as [-> ->].
exists tt. split; [reflexivity|]. rewrite E. reflexivity.
Qed.
Lemma knode_munmap : forall regs pc mem rom model snap (r : nat) (len : Z) (Kont : Z -> config -> Prop),
m_halted model = None -> m_vm_lazy model = [] ->
bv_unsigned (getr regs 17) = 215 ->
bv_unsigned (getr regs 10) mod page_size = 0 -> getr regs 11 <> Z_to_bv 64 0 ->
bv_unsigned (getr regs 10) + page_round_up_Z (bv_unsigned (getr regs 11)) <= TASK_SIZE ->
map_has (vm_maps (m_vmmaps model)) (getr regs 10) (page_round_up (getr regs 11)) = true ->
Kont 1 (munmap_nx regs pc mem rom model tt) ->
knode segs (mkCfg (pend_at regs pc mem rom) model) (KMunmap r len) snap Kont.
Proof.
intros regs pc mem rom model snap r len Kont Hh Hlz Hno Hal Hlen Hnw Hhas HK.
eapply (knode_forced _ (KMunmap r len) snap Kont unit (munmap_nx regs pc mem rom model) tt);
[reflexivity | intros p; discriminate | apply node_munmap; assumption | intros []; exact HK].
Qed.
Definition mmap_none_J (hint : word) (model : Model) (nZ : Z) : Type :=
({e : Z | In e mmap_errnos} + {a : word | place_ok hint model a nZ = true})%type.
Definition mmap_none_nx (regs : bvmap 5 word) (pc : word) (mem rom : word -> option byte) (model : Model)
(i : mmap_none_J (getr regs 10) model (page_round_up_Z (bv_unsigned (getr regs 11)))) : config :=
match i with
| inl e => mkCfg (mkst (regupd regs 10 (errno_ret (proj1_sig e))) (v_addi pc 4) mem rom) model
| inr a => mkCfg (mkst (regupd regs 10 (proj1_sig a)) (v_addi pc 4)
(apply_unmaps mem [(proj1_sig a, page_round_up (getr regs 11))]) rom)
(mmap_none_model (proj1_sig a) (page_round_up (getr regs 11)) model)
end.
Lemma node_mmap_none : forall regs pc mem rom model,
m_halted model = None -> m_vm_lazy model = [] ->
bv_unsigned (getr regs 17) = 222 ->
getr regs 11 <> Z_to_bv 64 0 -> getr regs 12 = Z_to_bv 64 0 -> getr regs 13 = Z_to_bv 64 34 ->
getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
node_ok segs (mkCfg (pend_at regs pc mem rom) model)
(mmap_none_J (getr regs 10) model (page_round_up_Z (bv_unsigned (getr regs 11))))
(fun _ => []) (mmap_none_nx regs pc mem rom model).
Proof.
intros regs pc mem rom model Hh Hlz Hno H1 H2 H3 H4 H5.
set (nZ := page_round_up_Z (bv_unsigned (getr regs 11))) in *.
set (n := page_round_up (getr regs 11)) in *.
assert (HnZ : 0 <= nZ).
{ unfold nZ. apply page_round_up_Z_nonneg. pose proof (u64_range (getr regs 11)). lia. }
assert (Hchk : forall eff,
check_syscall (sys_input segs (pend_at regs pc mem rom) (getr regs 17)) eff model
= match eff with
| mkEffectU r [] [] us [] [] =>
if errno_ret_in mmap_errnos r
then match us with [] => CheckOk model [] | _ => CheckReject end
else if place_ok (getr regs 10) model r nZ && listNN_eqb us [(r, n)]
then CheckOk (mmap_none_model r n model) [] else CheckReject
| _ => CheckReject
end).
{
intro eff. rewrite chk222 by exact Hno. unfold check_mmap.
rewrite H2, H3, ?H4, H5.
change (negb (mmap_off_aligned_b (Z_to_bv 64 0))) with false.
change (negb (mmap_anon_b (Z_to_bv 64 34))) with false.
replace (w_is0 (getr regs 11)) with false by (symmetry; unfold w_is0; apply bv_eqb_neq; exact H1).
change (mmap_modeled_b (Z_to_bv 64 0) (Z_to_bv 64 34) (Z_to_bv 64 0)) with false.
change (mmap_noaccess_b (Z_to_bv 64 0) (Z_to_bv 64 34) (Z_to_bv 64 0)) with true.
cbv beta iota. destruct eff as [r ws zs us cs ci].
destruct ws; [|reflexivity]. destruct zs; [|reflexivity].
destruct cs; [|reflexivity]. destruct ci; [|reflexivity]. cbv zeta.
change (with_mmap_backing (Z_to_bv 64 34)) with (fun (_ _ : word) (m : Model) => m). cbv beta.
unfold place_ok, mmap_none_model. fold nZ. unfold n, page_round_up. fold nZ. reflexivity. }
pose (ef := fun i : mmap_none_J (getr regs 10) model nZ =>
match i with
| inl e => mkEffect (errno_ret (proj1_sig e)) [] []
| inr a => mkEffectU (proj1_sig a) [] [] [(proj1_sig a, n)] [] []
end).
pose (md := fun i : mmap_none_J (getr regs 10) model nZ =>
match i with inl _ => model | inr a => mmap_none_model (proj1_sig a) n model end).
assert (Hn : node_ok segs (mkCfg (pend_at regs pc mem rom) model) (mmap_none_J (getr regs 10) model nZ) (fun _ => [])
(fun i => mkCfg (advance_past_svc (apply_effect (pend_at regs pc mem rom) (ef i))) (md i))).
{ apply (node_chk segs (pend_at regs pc mem rom) model (getr regs 17) (mmap_none_J (getr regs 10) model nZ)
(inl (exist _ ENOMEM ENOMEM_in_mmap_errnos)) ef md (fun _ => []) Hh eq_refl).
+ intros [[e He] | [a Ha]]; unfold ef, md; cbn [proj1_sig]; rewrite Hchk.
* rewrite (errno_ret_in_intro _ _ He). reflexivity.
* rewrite (place_not_errno _ model a nZ HnZ Ha), Ha.
rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
+ intros [[e He] | [a Ha]]; unfold md; [exact Hh | rewrite mmap_none_model_halted; exact Hh].
+ intros [[e He] | [a Ha]]; unfold md; [exact Hlz | rewrite mmap_none_model_lazy; exact Hlz].
+ intros [r ws zs us cs ci] m' evs Hk. rewrite Hchk in Hk.
destruct ws; [|discriminate]. destruct zs; [|discriminate].
destruct cs; [|destruct us; discriminate]. destruct ci; [|destruct us; discriminate].
destruct (errno_ret_in mmap_errnos r) eqn:Her.
* destruct us; [|discriminate]. inversion Hk; subst.
apply errno_ret_in_true in Her. destruct Her as (e & He & ->).
exists (inl (exist _ e He)). unfold ef, md; cbn [proj1_sig]. auto.
* destruct (place_ok (getr regs 10) model r nZ) eqn:Hg; [|discriminate].
destruct (listNN_eqb us [(r, n)]) eqn:Hus; [|discriminate].
apply listNN_eqb_eq in Hus. subst us. cbn [andb] in Hk. inversion Hk; subst.
exists (inr (exist _ r Hg)). unfold ef, md; cbn [proj1_sig]. auto. }
destruct Hn as [Hs Hc]. split.
- intros i. specialize (Hs i). destruct i as [[e He]|[a Ha]]; unfold ef, md, mmap_none_nx in *; cbn [proj1_sig] in *;
rewrite adv_pend in Hs; cbn [eff_ret] in Hs; [rewrite effmem_ret_only in Hs | rewrite effmem_unmaps in Hs]; exact Hs.
- intros e st Hst. destruct (Hc e st Hst) as (i & -> & ->). exists i. split; [reflexivity|].
destruct i as [[e He]|[a Ha]]; unfold ef, md, mmap_none_nx; cbn [proj1_sig]; rewrite adv_pend; cbn [eff_ret];
[rewrite effmem_ret_only | rewrite effmem_unmaps]; reflexivity.
Qed.
Lemma knode_mmap_none : forall regs pc mem rom model snap (len : Z) (Kont : Z -> config -> Prop),
m_halted model = None -> m_vm_lazy model = [] ->
bv_unsigned (getr regs 17) = 222 ->
getr regs 11 = Z_to_bv 64 len -> 0 < len < 2 ^ 63 -> getr regs 12 = Z_to_bv 64 0 ->
getr regs 13 = Z_to_bv 64 34 -> getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
(forall e, In e mmap_errnos ->
Kont 0 (mkCfg (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4) mem rom) model)) ->
(forall a, place_ok (getr regs 10) model a (page_round len) = true ->
Kont 1 (mkCfg (mkst (regupd regs 10 a) (v_addi pc 4) (apply_unmaps mem [(a, Z_to_bv 64 (page_round len))]) rom)
(mmap_none_model a (Z_to_bv 64 (page_round len)) model))) ->
(mgrant snap (KMmapNone len) -> exists a, place_ok (getr regs 10) model a (page_round len) = true) ->
knode segs (mkCfg (pend_at regs pc mem rom) model) (KMmapNone len) snap Kont.
Proof.
intros regs pc mem rom model snap len Kont Hh Hlz Hno Hlen Hrange H2 H3 H4 H5 HK0 HK1 HG.
assert (Hlen0 : getr regs 11 <> Z_to_bv 64 0).
{ rewrite Hlen. intros E. apply (f_equal bv_unsigned) in E. rewrite !Z_to_bv_unsigned in E.
change (bv_wrap 64 0) with 0 in E. rewrite bv_wrap_small in E; [lia | change (bv_modulus 64) with (2 ^ 64); lia]. }
assert (Hru : page_round_up_Z (bv_unsigned (getr regs 11)) = page_round len).
{ rewrite Hlen, Z_to_bv_unsigned, bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); lia). reflexivity. }
assert (Hpr : page_round_up (getr regs 11) = Z_to_bv 64 (page_round len)) by (unfold page_round_up; rewrite Hru; reflexivity).
set (bit := fun i : mmap_none_J (getr regs 10) model (page_round_up_Z (bv_unsigned (getr regs 11))) =>
match i with inl _ => 0 | inr _ => 1 end).
eapply (knode_fallible _ (KMmapNone len) snap Kont _ (mmap_none_nx regs pc mem rom model) bit
(inl (exist _ ENOMEM ENOMEM_in_mmap_errnos)));
[reflexivity | apply node_mmap_none; assumption | | reflexivity | |].
- intros [|]; cbn; auto.
- intros Hm. destruct (HG Hm) as (a & Ha). rewrite <- Hru in Ha. exists (inr (exist _ a Ha)). reflexivity.
- intros [[e He] | [a Ha]]; unfold bit, mmap_none_nx; cbn [proj1_sig].
+ apply HK0. exact He.
+ rewrite Hpr. apply HK1. rewrite <- Hru. exact Ha.
Qed.
Definition mprotect_J (model : Model) (addr n : word) : Type :=
({e : Z | In e mprotect_errnos} + {_ : unit | mprotect_budget_ok model addr n = true})%type.
Definition mprotect_nx (regs : bvmap 5 word) (pc : word) (mem rom : word -> option byte) (model : Model)
(i : mprotect_J model (getr regs 10) (page_round_up (getr regs 11))) : config :=
match i with
| inl e => mkCfg (mkst (regupd regs 10 (errno_ret (proj1_sig e))) (v_addi pc 4) mem rom) model
| inr _ => mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4)
(apply_zeros mem [(getr regs 10, page_round_up (getr regs 11))]) rom)
(mprotect_model (getr regs 10) (page_round_up (getr regs 11)) model)
end.
Lemma node_mprotect_rw : forall regs pc mem rom model,
m_halted model = None -> m_vm_lazy model = [] ->
bv_unsigned (getr regs 17) = 226 ->
bv_unsigned (getr regs 10) mod page_size = 0 ->
getr regs 11 <> Z_to_bv 64 0 ->
bv_unsigned (getr regs 10) + page_round_up_Z (bv_unsigned (getr regs 11)) < two_pow_64 ->
getr regs 12 = Z_to_bv 64 3 ->
map_contains (vm_noaccess (m_vmmaps model)) (getr regs 10) (page_round_up (getr regs 11)) = true ->
map_contains (vm_maps (m_vmmaps model)) (getr regs 10) (page_round_up (getr regs 11)) = true ->
node_ok segs (mkCfg (pend_at regs pc mem rom) model)
(mprotect_J model (getr regs 10) (page_round_up (getr regs 11)))
(fun _ => []) (mprotect_nx regs pc mem rom model).
Proof.
intros regs pc mem rom model Hh Hlz Hno Hal Hlen Hnw Hprot Hna Hma.
set (addr := getr regs 10) in *.
set (nZ := page_round_up_Z (bv_unsigned (getr regs 11))) in *.
set (n := page_round_up (getr regs 11)) in *.
assert (Hchk : forall eff,
check_syscall (sys_input segs (pend_at regs pc mem rom) (getr regs 17)) eff model
= match eff with
| mkEffectU r [] zs [] [] [] =>
if errno_ret_in mprotect_errnos r
then match zs with [] => CheckOk model [] | _ => CheckReject end
else if mprotect_budget_ok model addr n && w_is0 r && listNN_eqb zs [(addr, n)]
then CheckOk (mprotect_model addr n model) [] else CheckReject
| _ => CheckReject
end).
{ intro eff. rewrite chk226 by exact Hno. fold addr. rewrite Hprot. unfold check_mprotect.
change (mprotect_grows_conflict_b (Z_to_bv 64 3)) with false.
change (mprotect_modeled_b (Z_to_bv 64 3)) with true.
rewrite (proj2 (Z.eqb_eq _ _) Hal). unfold w_is0 at 1. rewrite (bv_eqb_neq _ _ Hlen).
cbn [negb]. fold nZ. rewrite (proj2 (Z.leb_gt _ _) Hnw). cbv beta iota zeta. fold nZ.
unfold n, page_round_up in Hna, Hma. fold nZ in Hna. fold nZ in Hma.
rewrite Hna, Hma. cbn [andb].
destruct eff as [r ws zs us cs ci]. destruct ws; [|reflexivity].
destruct us; [|reflexivity]. destruct cs; [|reflexivity]. destruct ci; [|reflexivity].
unfold mprotect_model, n, page_round_up. fold nZ. destruct zs; reflexivity. }
pose (ef := fun i : mprotect_J model addr n =>
match i with
| inl e => mkEffect (errno_ret (proj1_sig e)) [] []
| inr _ => mkEffect (Z_to_bv 64 0) [] [(addr, n)]
end).
pose (md := fun i : mprotect_J model addr n =>
match i with inl _ => model | inr _ => mprotect_model addr n model end).
assert (Hn : node_ok segs (mkCfg (pend_at regs pc mem rom) model) (mprotect_J model addr n) (fun _ => [])
(fun i => mkCfg (advance_past_svc (apply_effect (pend_at regs pc mem rom) (ef i))) (md i))).
{ apply (node_chk segs (pend_at regs pc mem rom) model (getr regs 17) (mprotect_J model addr n)
(inl (exist _ ENOMEM ENOMEM_in_mprotect_errnos)) ef md (fun _ => []) Hh eq_refl).
+ intros [[e He] | [[] Hb]]; unfold ef, md; cbn [proj1_sig]; rewrite Hchk.
* rewrite (errno_ret_in_intro _ _ He). reflexivity.
* change (errno_ret_in mprotect_errnos (Z_to_bv 64 0)) with false.
change (w_is0 (Z_to_bv 64 0)) with true.
rewrite (proj2 (listNN_eqb_eq _ _) eq_refl), Hb. reflexivity.
+ intros [[e He] | [[] Hb]]; unfold md; [exact Hh | rewrite mprotect_model_halted; exact Hh].
+ intros [[e He] | [[] Hb]]; unfold md; [exact Hlz | rewrite mprotect_model_lazy; exact Hlz].
+ intros [r ws zs us cs ci] m' evs Hk. rewrite Hchk in Hk.
destruct ws; [|discriminate]. destruct us; [|destruct zs; discriminate].
destruct cs; [|destruct zs; discriminate]. destruct ci; [|destruct zs; discriminate].
destruct (errno_ret_in mprotect_errnos r) eqn:Her.
* destruct zs; [|discriminate]. inversion Hk; subst.
apply errno_ret_in_true in Her. destruct Her as (e & He & ->).
exists (inl (exist _ e He)). unfold ef, md; cbn [proj1_sig]. auto.
* destruct (Bool.bool_dec (mprotect_budget_ok model addr n) true) as [Hb|Hb];
[rewrite Hb in Hk | apply Bool.not_true_is_false in Hb; rewrite Hb in Hk; discriminate].
destruct (w_is0 r) eqn:Hr; [|discriminate].
destruct (listNN_eqb zs [(addr, n)]) eqn:Hzs; [|discriminate].
unfold w_is0 in Hr. apply bv_eqb_eq in Hr. apply listNN_eqb_eq in Hzs. subst.
cbn [andb] in Hk. inversion Hk; subst. exists (inr (exist _ tt Hb)). unfold ef, md. auto. }
destruct Hn as [Hs Hc]. split.
- intros i. specialize (Hs i). destruct i as [[e He]|[[] Hb]]; unfold ef, md, mprotect_nx in *; cbn [proj1_sig] in *;
rewrite adv_pend in Hs; cbn [eff_ret] in Hs; [rewrite effmem_ret_only in Hs | rewrite effmem_zeros in Hs]; exact Hs.
- intros e st Hst. destruct (Hc e st Hst) as (i & -> & ->). exists i. split; [reflexivity|].
destruct i as [[e He]|[[] Hb]]; unfold ef, md, mprotect_nx; cbn [proj1_sig]; rewrite adv_pend; cbn [eff_ret];
[rewrite effmem_ret_only | rewrite effmem_zeros]; reflexivity.
Qed.
Lemma knode_mprotect : forall regs pc mem rom model snap (p : sptr) (Kont : Z -> config -> Prop),
m_halted model = None -> m_vm_lazy model = [] ->
bv_unsigned (getr regs 17) = 226 ->
bv_unsigned (getr regs 10) mod page_size = 0 ->
getr regs 11 = Z_to_bv 64 4096 ->
bv_unsigned (getr regs 10) + 4096 < two_pow_64 ->
getr regs 12 = Z_to_bv 64 3 ->
map_contains (vm_noaccess (m_vmmaps model)) (getr regs 10) (Z_to_bv 64 4096) = true ->
map_contains (vm_maps (m_vmmaps model)) (getr regs 10) (Z_to_bv 64 4096) = true ->
(forall e, In e mprotect_errnos ->
Kont 0 (mkCfg (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4) mem rom) model)) ->
(mprotect_budget_ok model (getr regs 10) (Z_to_bv 64 4096) = true ->
Kont 1 (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) (apply_zeros mem [(getr regs 10, Z_to_bv 64 4096)]) rom)
(mprotect_model (getr regs 10) (Z_to_bv 64 4096) model))) ->
(mgrant snap (KMprotect p) -> mprotect_budget_ok model (getr regs 10) (Z_to_bv 64 4096) = true) ->
knode segs (mkCfg (pend_at regs pc mem rom) model) (KMprotect p) snap Kont.
Proof.
intros regs pc mem rom model snap p Kont Hh Hlz Hno Hal Hlen Hnw Hprot Hna Hma HK0 HK1 HG.
assert (Hpr : page_round_up (getr regs 11) = Z_to_bv 64 4096) by (rewrite Hlen; reflexivity).
assert (HprZ : page_round_up_Z (bv_unsigned (getr regs 11)) = 4096) by (rewrite Hlen; reflexivity).
assert (Hlen0 : getr regs 11 <> Z_to_bv 64 0) by (rewrite Hlen; discriminate).
set (bit := fun i : mprotect_J model (getr regs 10) (page_round_up (getr regs 11)) =>
match i with inl _ => 0 | inr _ => 1 end).
eapply (knode_fallible _ (KMprotect p) snap Kont _ (mprotect_nx regs pc mem rom model) bit
(inl (exist _ ENOMEM ENOMEM_in_mprotect_errnos)));
[reflexivity | apply node_mprotect_rw; try assumption; try (rewrite HprZ; exact Hnw); rewrite Hpr; assumption | | reflexivity | |].
- intros [|]; cbn; auto.
- intros Hm. pose proof (HG Hm) as Hb. rewrite <- Hpr in Hb. exists (inr (exist _ tt Hb)). reflexivity.
- intros [[e He] | [[] Hb]]; unfold bit, mprotect_nx; cbn [proj1_sig].
+ apply HK0. exact He.
+ rewrite Hpr. apply HK1. rewrite <- Hpr. exact Hb.
Qed.
Definition fixed_J : Type := ({e : Z | In e mmap_errnos} + (unit + {e : Z | In e mmap_errnos}))%type.
Definition fixed_nx (regs : bvmap 5 word) (pc : word) (mem rom : word -> option byte) (model : Model) (i : fixed_J) : config :=
match i with
| inl e => mkCfg (mkst (regupd regs 10 (errno_ret (proj1_sig e))) (v_addi pc 4) mem rom) model
| inr (inl _) => mkCfg (mkst (regupd regs 10 (getr regs 10)) (v_addi pc 4)
(apply_unmaps mem [(getr regs 10, page_round_up (getr regs 11))]) rom)
(mmap_fixed_model (getr regs 10) (page_round_up (getr regs 11)) model)
| inr (inr e) => mkCfg (mkst (regupd regs 10 (errno_ret (proj1_sig e))) (v_addi pc 4)
(apply_unmaps mem [(getr regs 10, page_round_up (getr regs 11))]) rom)
(mmap_fixed_destroyed_model (getr regs 10) (page_round_up (getr regs 11)) model)
end.
Lemma node_mmap_fixed_none : forall regs pc mem rom model,
m_halted model = None -> m_vm_lazy model = [] ->
bv_unsigned (getr regs 17) = 222 ->
getr regs 11 <> Z_to_bv 64 0 -> getr regs 12 = Z_to_bv 64 0 -> getr regs 13 = Z_to_bv 64 50 ->
getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
bv_unsigned (getr regs 10) mod page_size = 0 -> 0 < bv_unsigned (getr regs 10) ->
bv_unsigned (getr regs 10) + page_round_up_Z (bv_unsigned (getr regs 11)) <= alloc_top (m_vmmaps model) ->
region_free (vm_reserved (m_vmmaps model)) (getr regs 10) (page_round_up (getr regs 11)) = true ->
map_contains (vm_maps (m_vmmaps model)) (getr regs 10) (page_round_up (getr regs 11)) = true ->
node_ok segs (mkCfg (pend_at regs pc mem rom) model) fixed_J (fun _ => []) (fixed_nx regs pc mem rom model).
Proof.
intros regs pc mem rom model Hh Hlz Hno H1 H2 H3 H4 H5 Hal Hpos Hceil Hfree Hcont.
set (addr := getr regs 10) in *.
set (nZ := page_round_up_Z (bv_unsigned (getr regs 11))) in *.
set (n := page_round_up (getr regs 11)) in *.
pose proof (alloc_top_room (m_vmmaps model)) as Hroom. pose proof stack_max_size_val as Hsms.
assert (HnZ : 0 <= nZ).
{ unfold nZ. apply page_round_up_Z_nonneg. pose proof (u64_range (getr regs 11)). lia. }
assert (Haddr_nerr : errno_ret_in mmap_errnos addr = false).
{ apply errno_ret_in_below; [reflexivity|]. unfold two_pow_64 in *. lia. }
assert (Hchk : forall eff,
check_syscall (sys_input segs (pend_at regs pc mem rom) (getr regs 17)) eff model
= match eff with
| mkEffectU r [] [] us [] [] =>
if errno_ret_in mmap_errnos r
then match us with
| [] => CheckOk model []
| _ => if listNN_eqb us [(addr, n)]
then CheckOk (mmap_fixed_destroyed_model addr n model) []
else CheckReject
end
else if bv_eqb r addr && listNN_eqb us [(addr, n)]
then CheckOk (mmap_fixed_model addr n model) [] else CheckReject
| _ => CheckReject
end).
{ intro eff. rewrite chk222 by exact Hno. fold addr. unfold check_mmap.
rewrite H2, H3, ?H4, H5.
change (negb (mmap_off_aligned_b (Z_to_bv 64 0))) with false.
change (negb (mmap_anon_b (Z_to_bv 64 50))) with false.
replace (w_is0 (getr regs 11)) with false by (symmetry; unfold w_is0; apply bv_eqb_neq; exact H1).
change (mmap_modeled_b (Z_to_bv 64 0) (Z_to_bv 64 50) (Z_to_bv 64 0)) with false.
change (mmap_noaccess_b (Z_to_bv 64 0) (Z_to_bv 64 50) (Z_to_bv 64 0)) with false.
change (mmap_fixed_noaccess_b (Z_to_bv 64 0) (Z_to_bv 64 50) (Z_to_bv 64 0)) with true.
cbv beta iota zeta. fold nZ.
rewrite (proj2 (Z.leb_gt _ _)) by (unfold two_pow_64 in *; lia).
rewrite (proj2 (Z.leb_le _ _) Hceil). cbn [negb].
rewrite (proj2 (Z.eqb_eq _ _) Hal). cbn [negb].
rewrite (proj2 (Z.ltb_lt _ _) Hpos). cbn [negb].
unfold n, page_round_up in Hfree, Hcont. fold nZ in Hfree. fold nZ in Hcont.
rewrite Hfree, Hcont. cbn [andb].
destruct eff as [r ws zs us cs ci].
destruct ws; [|reflexivity]. destruct zs; [|reflexivity].
destruct cs; [|destruct us; reflexivity]. destruct ci; [|destruct us; reflexivity].
unfold mmap_fixed_model, mmap_fixed_destroyed_model, n, page_round_up. fold nZ. reflexivity. }
pose (ef := fun i : fixed_J =>
match i with
| inl e => mkEffect (errno_ret (proj1_sig e)) [] []
| inr (inl _) => mkEffectU addr [] [] [(addr, n)] [] []
| inr (inr e) => mkEffectU (errno_ret (proj1_sig e)) [] [] [(addr, n)] [] []
end).
pose (md := fun i : fixed_J =>
match i with
| inl _ => model
| inr (inl _) => mmap_fixed_model addr n model
| inr (inr _) => mmap_fixed_destroyed_model addr n model
end).
assert (Hn : node_ok segs (mkCfg (pend_at regs pc mem rom) model) fixed_J (fun _ => [])
(fun i => mkCfg (advance_past_svc (apply_effect (pend_at regs pc mem rom) (ef i))) (md i))).
{ apply (node_chk segs (pend_at regs pc mem rom) model (getr regs 17) fixed_J
(inl (exist _ ENOMEM ENOMEM_in_mmap_errnos)) ef md (fun _ => []) Hh eq_refl).
+ intros [[e He] | [[] | [e He]]]; unfold ef, md; cbn [proj1_sig]; rewrite Hchk.
* rewrite (errno_ret_in_intro _ _ He). reflexivity.
* rewrite Haddr_nerr, bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
* rewrite (errno_ret_in_intro _ _ He), (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
+ intros [[e He] | [[] | [e He]]]; unfold md;
[exact Hh | rewrite mmap_fixed_model_halted; exact Hh | rewrite mmap_fixed_destroyed_model_halted; exact Hh].
+ intros [[e He] | [[] | [e He]]]; unfold md;
[exact Hlz | apply mmap_fixed_model_lazy; exact Hlz | apply mmap_fixed_destroyed_model_lazy; exact Hlz].
+ intros [r ws zs us cs ci] m' evs Hk. rewrite Hchk in Hk.
destruct ws; [|discriminate]. destruct zs; [|discriminate].
destruct cs; [|destruct us; discriminate]. destruct ci; [|destruct us; discriminate].
destruct (errno_ret_in mmap_errnos r) eqn:Her.
* apply errno_ret_in_true in Her. destruct Her as (e & He & ->).
destruct us as [|u us].
-- inversion Hk; subst. exists (inl (exist _ e He)). unfold ef, md; cbn [proj1_sig]. auto.
-- destruct (listNN_eqb (u :: us) [(addr, n)]) eqn:Hus; [|discriminate].
apply listNN_eqb_eq in Hus. inversion Hk; subst.
exists (inr (inr (exist _ e He))). unfold ef, md; cbn [proj1_sig]. rewrite Hus. auto.
* destruct (bv_eqb r addr) eqn:Hr; [|discriminate].
destruct (listNN_eqb us [(addr, n)]) eqn:Hus; [|discriminate].
apply bv_eqb_eq in Hr. apply listNN_eqb_eq in Hus. subst. cbn [andb] in Hk.
inversion Hk; subst. exists (inr (inl tt)). unfold ef, md. auto. }
destruct Hn as [Hs Hc]. split.
- intros i. specialize (Hs i). destruct i as [[e He]|[[]|[e He]]]; unfold ef, md, fixed_nx in *; cbn [proj1_sig] in *;
rewrite adv_pend in Hs; cbn [eff_ret] in Hs;
[rewrite effmem_ret_only in Hs | rewrite effmem_unmaps in Hs | rewrite effmem_unmaps in Hs]; exact Hs.
- intros e st Hst. destruct (Hc e st Hst) as (i & -> & ->). exists i. split; [reflexivity|].
destruct i as [[e He]|[[]|[e He]]]; unfold ef, md, fixed_nx; cbn [proj1_sig]; rewrite adv_pend; cbn [eff_ret];
[rewrite effmem_ret_only | rewrite effmem_unmaps | rewrite effmem_unmaps]; reflexivity.
Qed.
Lemma knode_guard : forall regs pc mem rom model snap (Kont : Z -> config -> Prop),
m_halted model = None -> m_vm_lazy model = [] ->
bv_unsigned (getr regs 17) = 222 ->
getr regs 11 = Z_to_bv 64 4096 -> getr regs 12 = Z_to_bv 64 0 -> getr regs 13 = Z_to_bv 64 50 ->
getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
bv_unsigned (getr regs 10) mod page_size = 0 -> 0 < bv_unsigned (getr regs 10) ->
bv_unsigned (getr regs 10) + 4096 <= alloc_top (m_vmmaps model) ->
region_free (vm_reserved (m_vmmaps model)) (getr regs 10) (Z_to_bv 64 4096) = true ->
map_contains (vm_maps (m_vmmaps model)) (getr regs 10) (Z_to_bv 64 4096) = true ->
(forall i : fixed_J, Kont 1 (fixed_nx regs pc mem rom model i)) ->
knode segs (mkCfg (pend_at regs pc mem rom) model) KGuard snap Kont.
Proof.
intros regs pc mem rom model snap Kont Hh Hlz Hno Hlen H2 H3 H4 H5 Hal Hpos Hceil Hfree Hcont HK.
assert (Hpr : page_round_up (getr regs 11) = Z_to_bv 64 4096) by (rewrite Hlen; reflexivity).
assert (HprZ : page_round_up_Z (bv_unsigned (getr regs 11)) = 4096) by (rewrite Hlen; reflexivity).
assert (Hlen0 : getr regs 11 <> Z_to_bv 64 0) by (rewrite Hlen; discriminate).
eapply (knode_forced _ KGuard snap Kont fixed_J (fixed_nx regs pc mem rom model) (inl (exist _ ENOMEM ENOMEM_in_mmap_errnos)));
[reflexivity | intros p; discriminate | | exact HK].
apply node_mmap_fixed_none; try assumption; rewrite ?HprZ, ?Hpr; assumption.
Qed.
End f.
End d.
