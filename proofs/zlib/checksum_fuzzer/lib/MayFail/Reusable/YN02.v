(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YN02.v, with its module paths changed. *)
(* Modified by Rares Buhai, 2026-10: proved fallible brk, mmap and mprotect nodes and all fixed-mapping outcomes; changed module paths to the MayFail runtime. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia Classical_Prop.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import DispatchCompute.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0h.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK14.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK1b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK15.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0n.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK0v.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0n.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YM06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YM02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0f.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable.R Require Import Cfg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section f.
Variable segs : list Segment.
Lemma knode_fallible : forall c1 q snap (Kont : Z -> config -> Prop) (J : Type) (nx : J -> config) (bit : J -> Z) (j0 : J),
fallible q = true -> spurious q = true ->
node_ok segs c1 J (fun _ => []) nx ->
(forall j, bit j = 0 \/ bit j = 1) -> bit j0 = 0 ->
(mgrant snap q -> exists j, bit j = 1) ->
(forall j, Kont (bit j) (nx j)) ->
knode segs c1 q snap Kont.
Proof.
intros c1 q snap Kont J nx bit j0 Hf Hsp Hn Hbits Hj0 Hg Hk.
destruct q; try discriminate; cbn; exists J, nx, bit, j0; (split; [exact Hn|]); (split; [exact Hk|]); repeat split; eauto.
Qed.
Lemma knode_granted04 : forall c1 q snap (Kont : Z -> config -> Prop) (J : Type) (nx : J -> config) (bit : J -> Z) (j0 : J),
fallible q = true -> spurious q = false ->
node_ok segs c1 J (fun _ => []) nx ->
(forall j, bit j = 0 \/ bit j = 1) ->
(mgrant snap q -> forall j, bit j = 1) ->
(forall j, Kont (bit j) (nx j)) ->
knode segs c1 q snap Kont.
Proof.
intros c1 q snap Kont J nx bit j0 Hf Hsp Hn Hbits Hg Hk.
destruct q; try discriminate; cbn; exists J, nx, bit, j0; (split; [exact Hn|]); (split; [exact Hk|]); split; auto.
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
Lemma knode_junk : forall c1 p snap (Kont : Z -> config -> Prop) z,
0 <= z < 256 -> Kont z c1 -> knode segs c1 (KJunk p) snap Kont.
Proof. intros c1 p snap Kont z Hz Hk. cbn. exists z. auto. Qed.
Lemma mreal_ask {R} : forall c q snap (k : Z -> itree astate R) Q,
SR segs c (fun c1 => knode segs c1 q snap (fun z c2 => mreal segs c2 (k z) Q)) ->
mreal segs c (IAsk q snap k) Q.
Proof. intros. exact H. Qed.
Lemma mreal_leaf {R} : forall c (r : R) Q, SR segs c (Q r) -> mreal segs c (IRet r) Q.
Proof. intros. exact H. Qed.
Definition brk_eff (regs : bvmap 5 word) (model : Model) (r : word) : SyscallEffect :=
mkEffectU r [] (brk_zeros (getr regs 10) r (vm_brk (m_vmmaps model)))
(brk_unmaps r (vm_brk (m_vmmaps model))) [] [].
Definition brk_J (regs : bvmap 5 word) (pc : word) (mem rom : word -> option byte) (model : Model) : Type :=
{r : word | brk_resolution_ok model (getr regs 10) r /\
~ spurious_refusal_cfg ACFG (sys_input segs (pend_at regs pc mem rom) (getr regs 17)) model (brk_eff regs model r)}.
Definition brk_nx (regs : bvmap 5 word) (pc : word) (mem rom : word -> option byte) (model : Model)
(i : brk_J regs pc mem rom model) : config :=
let r := proj1_sig i in
mkCfg (mkst (regupd regs 10 r) (v_addi pc 4)
(apply_zeros (apply_unmaps mem (brk_unmaps r (vm_brk (m_vmmaps model))))
(brk_zeros (getr regs 10) r (vm_brk (m_vmmaps model)))) rom)
(brk_model (getr regs 10) r model).
Lemma brk_spec_ok : forall regs pc mem rom model r,
bv_unsigned (getr regs 17) = 214 -> brk_resolution_ok model (getr regs 10) r ->
syscall_spec (sys_input segs (pend_at regs pc mem rom) (getr regs 17)) model
(Ok (brk_eff regs model r) (brk_model (getr regs 10) r model) []).
Proof.
intros regs pc mem rom model r Hno Hr.
pose proof (brk_ok_intro segs (pend_at regs pc mem rom) (getr regs 17) model r Hno) as H.
rewrite pend_gpr0 in H. exact (H Hr).
Qed.
Lemma brk_J_inh : forall regs pc mem rom model,
bv_unsigned (getr regs 17) = 214 -> inhabited (brk_J regs pc mem rom model).
Proof.
intros regs pc mem rom model Hno.
destruct (exists_nonspurious ACFG (sys_input segs (pend_at regs pc mem rom) (getr regs 17)) model _ _ _
(brk_spec_ok regs pc mem rom model _ Hno (brk_resolution_ok_keep model (getr regs 10))))
as (eff & m' & evs & Hs & Hns).
apply (brk_ok_iff segs (pend_at regs pc mem rom) (getr regs 17) model eff m' evs Hno) in Hs.
rewrite pend_gpr0 in Hs. destruct Hs as (Heff & _ & Hr & _).
constructor. exists (eff_ret eff). split; [exact Hr|]. unfold brk_eff. rewrite <- Heff. exact Hns.
Qed.
Lemma node_brk : forall regs pc mem rom model,
m_halted model = None -> m_vm_lazy model = [] ->
bv_unsigned (getr regs 17) = 214 ->
node_ok segs (mkCfg (pend_at regs pc mem rom) model) (brk_J regs pc mem rom model)
(fun _ => []) (brk_nx regs pc mem rom model).
Proof.
intros regs pc mem rom model Hh Hlz Hno.
destruct (brk_J_inh regs pc mem rom model Hno) as [i0].
pose (J := brk_J regs pc mem rom model).
pose (ef := fun i : J => brk_eff regs model (proj1_sig i)).
pose (md := fun i : J => brk_model (getr regs 10) (proj1_sig i) model).
assert (Hn : node_ok segs (mkCfg (pend_at regs pc mem rom) model) J (fun _ => [])
(fun i => mkCfg (advance_past_svc (apply_effect (pend_at regs pc mem rom) (ef i))) (md i))).
{ apply (node_chk_cfg segs (pend_at regs pc mem rom) model (getr regs 17) J i0 ef md (fun _ => []) Hh eq_refl).
+ intros [r [Hr Hns]]. unfold ef, md; cbn [proj1_sig]. apply check_syscall_ok_iff.
apply brk_spec_ok; assumption.
+ intros [r Hr]. unfold md. rewrite brk_model_halted. exact Hh.
+ intros [r Hr]. unfold md. apply brk_model_lazy. exact Hlz.
+ intros eff m' evs Hk. apply check_syscall_ok_iff in Hk.
apply (brk_ok_iff segs (pend_at regs pc mem rom) (getr regs 17) model eff m' evs Hno) in Hk.
rewrite pend_gpr0 in Hk. destruct Hk as (Heff & -> & Hr & ->).
destruct (classic (spurious_refusal_cfg ACFG (sys_input segs (pend_at regs pc mem rom) (getr regs 17)) model eff))
as [Hsp | Hns].
* right. split; [exact Hsp | rewrite brk_model_halted; exact Hh].
* left.
assert (Hns' : ~ spurious_refusal_cfg ACFG (sys_input segs (pend_at regs pc mem rom) (getr regs 17)) model
(brk_eff regs model (eff_ret eff))) by (unfold brk_eff; rewrite <- Heff; exact Hns).
exists (exist _ (eff_ret eff) (conj Hr Hns')). unfold ef, md, brk_eff; cbn [proj1_sig]. rewrite <- Heff. auto.
+ intros [r [Hr Hns]]. exact Hns. }
destruct Hn as [Hs Hc]. split.
- intros i. specialize (Hs i). unfold ef, md, brk_eff in Hs. rewrite adv_pend in Hs. cbn [eff_ret] in Hs.
unfold effmem in Hs. cbn [eff_unmaps eff_zeros eff_writes eff_copies apply_writes apply_copies] in Hs. exact Hs.
- intros e st Hst. destruct (Hc e st Hst) as (i & -> & ->). exists i. split; [reflexivity|].
unfold ef, md, brk_eff. rewrite adv_pend. cbn [eff_ret]. unfold effmem.
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
destruct (brk_J_inh regs pc mem rom model Hno) as [i0].
eapply (knode_forced _ KBrkQuery snap Kont _ (brk_nx regs pc mem rom model) i0);
[reflexivity | intros p; discriminate | apply node_brk; assumption |].
intros [r [Hr Hns]]. unfold brk_nx; cbn [proj1_sig].
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
set (bit := fun i : brk_J regs pc mem rom model =>
if bv_eqb (proj1_sig i) (getr regs 10) then 1 else 0).
assert (Hi : brk_resolution_ok model (getr regs 10) (vm_brk (m_vmmaps model))).
{ apply (proj2 (Hiff _ Hs Hlt)). left. reflexivity. }
assert (Hkeep_nonspurious : ~ spurious_refusal_cfg ACFG
  (sys_input segs (pend_at regs pc mem rom) (getr regs 17)) model
  (brk_eff regs model (vm_brk (m_vmmaps model)))) by apply spurious_refusal_may_fail.
set (i0 := (exist _ (vm_brk (m_vmmaps model)) (conj Hi Hkeep_nonspurious) : brk_J regs pc mem rom model)).
eapply (knode_fallible _ (KBrkGrow npages) snap Kont _ (brk_nx regs pc mem rom model) bit i0);
[reflexivity | reflexivity | apply node_brk; assumption | | | |].
- intros j. unfold bit. destruct (bv_eqb _ _); auto.
- unfold bit, i0; cbn [proj1_sig]. rewrite (bv_eqb_neq _ _) by (intros E; rewrite E in Hlt; lia). reflexivity.
- intros Hm. pose proof (HG Hm) as G.
  assert (Hgr : brk_resolution_ok model (getr regs 10) (getr regs 10)).
  { apply (proj2 (Hiff _ Hs Hlt)). right. auto. }
  assert (Hns1 : ~ spurious_refusal_cfg ACFG
    (sys_input segs (pend_at regs pc mem rom) (getr regs 17)) model
    (brk_eff regs model (getr regs 10))) by apply spurious_refusal_may_fail.
  exists (exist _ (getr regs 10) (conj Hgr Hns1)). unfold bit; cbn [proj1_sig]. rewrite bv_eqb_refl. reflexivity.
- intros [r [Hr Hns]]. unfold bit, brk_nx; cbn [proj1_sig].
destruct (proj1 (Hiff _ Hs Hlt) Hr) as [-> | [-> G]].
+ rewrite (bv_eqb_neq _ _) by (intros E; rewrite E in Hlt; lia).
rewrite brk_zeros_keep, brk_unmaps_keep. cbn [apply_unmaps apply_zeros]. exact HK0.
+ rewrite bv_eqb_refl.
rewrite (brk_unmaps_grow (getr regs 10) (vm_brk (m_vmmaps model))) by lia.
rewrite (brk_zeros_aligned_grow (getr regs 10) (getr regs 10) (vm_brk (m_vmmaps model)) Hreq0 Hb0 Hlt Hbal), Hru.
replace (bv_unsigned (vm_brk (m_vmmaps model)) + PGSZ * npages - bv_unsigned (vm_brk (m_vmmaps model))) with (PGSZ * npages) by lia.
cbn [apply_unmaps]. apply HK1. exact G.
Qed.
Definition mmap_rw_J (hint : word) (model : Model) (nZ : Z) : Type := mmap_rw_J04 hint model nZ.
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
destruct (node_mmap_rw04 segs regs pc mem rom model Hh Hlz Hno Hlen Hprot Hflags Hfd Hoff) as [Hs Hc]. split.
- intros i. specialize (Hs i). destruct i as [[e He]|[a Ha]]; unfold mmap_rw_ef04, mmap_rw_md04, mmap_rw_nx in *; cbn [proj1_sig] in *;
rewrite adv_pend in Hs; cbn [eff_ret] in Hs; [rewrite effmem_ret_only in Hs | rewrite effmem_zeros in Hs]; exact Hs.
- intros e st Hst. destruct (Hc e st Hst) as (i & -> & ->). exists i. split; [reflexivity|].
destruct i as [[e He]|[a Ha]]; unfold mmap_rw_ef04, mmap_rw_md04, mmap_rw_nx; cbn [proj1_sig]; rewrite adv_pend; cbn [eff_ret];
[rewrite effmem_ret_only | rewrite effmem_zeros]; reflexivity.
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
[reflexivity | reflexivity | apply node_mmap_rw; assumption | | | |].
- intros [|]; cbn; auto.
- unfold bit. reflexivity.
- intros Hm. destruct (HG Hm) as (a & Ha). rewrite <- Hru in Ha.
  exists (inr (exist _ a Ha)). reflexivity.
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
apply node_ok_of_pnode; [eapply transparent_nonalloc_no; [reflexivity | exact Hno | reflexivity]|]. split.
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
Definition mmap_none_J (hint : word) (model : Model) (nZ : Z) : Type := mmap_none_J04 hint model nZ.
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
destruct (node_mmap_none04 segs regs pc mem rom model Hh Hlz Hno H1 H2 H3 H4 H5) as [Hs Hc]. split.
- intros i. specialize (Hs i). destruct i as [[e He]|[a Ha]]; unfold mmap_none_ef04, mmap_none_md04, mmap_none_nx in *; cbn [proj1_sig] in *;
rewrite adv_pend in Hs; cbn [eff_ret] in Hs; [rewrite effmem_ret_only in Hs | rewrite effmem_unmaps in Hs]; exact Hs.
- intros e st Hst. destruct (Hc e st Hst) as (i & -> & ->). exists i. split; [reflexivity|].
destruct i as [[e He]|[a Ha]]; unfold mmap_none_ef04, mmap_none_md04, mmap_none_nx; cbn [proj1_sig]; rewrite adv_pend; cbn [eff_ret];
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
[reflexivity | reflexivity | apply node_mmap_none; assumption | | | |].
- intros [|]; cbn; auto.
- unfold bit. reflexivity.
- intros Hm. destruct (HG Hm) as (a & Ha). rewrite <- Hru in Ha.
  exists (inr (exist _ a Ha)). reflexivity.
- intros [[e He] | [a Ha]]; unfold bit, mmap_none_nx; cbn [proj1_sig].
+ apply HK0. exact He.
+ rewrite Hpr. apply HK1. rewrite <- Hru. exact Ha.
Qed.
Definition mprotect_J (model : Model) (addr n : word) : Type := mprotect_J04 model addr n.
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
destruct (node_mprotect_rw04 segs regs pc mem rom model Hh Hlz Hno Hal Hlen Hnw Hprot Hna Hma) as [Hs Hc]. split.
- intros i. specialize (Hs i). destruct i as [[e He]|[[] Hb]]; unfold mprotect_ef04, mprotect_md04, mprotect_nx in *; cbn [proj1_sig] in *;
rewrite adv_pend in Hs; cbn [eff_ret] in Hs; [rewrite effmem_ret_only in Hs | rewrite effmem_zeros in Hs]; exact Hs.
- intros e st Hst. destruct (Hc e st Hst) as (i & -> & ->). exists i. split; [reflexivity|].
destruct i as [[e He]|[[] Hb]]; unfold mprotect_ef04, mprotect_md04, mprotect_nx; cbn [proj1_sig]; rewrite adv_pend; cbn [eff_ret];
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
[reflexivity | reflexivity | apply node_mprotect_rw; try assumption; try (rewrite HprZ; exact Hnw); rewrite Hpr; assumption | | | |].
- intros [|]; cbn; auto.
- unfold bit. reflexivity.
- intros Hm. pose proof (HG Hm) as Hb. rewrite <- Hpr in Hb.
  exists (inr (exist _ tt Hb)). reflexivity.
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
node_ok segs (mkCfg (pend_at regs pc mem rom) model) fixed_J (fun _ => [])
(fixed_nx regs pc mem rom model).
Proof.
intros regs pc mem rom model Hh Hlz Hno H1 H2 H3 H4 H5 Hal Hpos Hceil Hfree Hcont.
destruct (node_mmap_fixed_none04 segs regs pc mem rom model Hh Hlz Hno H1 H2 H3 H4 H5 Hal Hpos Hceil Hfree Hcont) as [Hs Hc]. split.
- intros i. specialize (Hs i). destruct i as [[e He] | [[] | [e He]]];
  unfold fixed_nx, mmap_fixed_ef04, mmap_fixed_md04 in *; cbn [proj1_sig] in *;
  rewrite adv_pend in Hs; cbn [eff_ret] in Hs;
  [rewrite effmem_ret_only in Hs | rewrite effmem_unmaps in Hs | rewrite effmem_unmaps in Hs]; exact Hs.
- intros e st Hst. destruct (Hc e st Hst) as (i & -> & ->). exists i. split; [reflexivity|].
  destruct i as [[e He] | [[] | [e He]]];
  unfold fixed_nx, mmap_fixed_ef04, mmap_fixed_md04; cbn [proj1_sig];
  rewrite adv_pend; cbn [eff_ret];
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
eapply (knode_forced _ KGuard snap Kont fixed_J (fixed_nx regs pc mem rom model) (inr (inl tt)));
[reflexivity | intros p; discriminate | | intros i; apply HK].
apply node_mmap_fixed_none; try assumption; rewrite ?HprZ, ?Hpr; assumption.
Qed.
End f.
End d.
