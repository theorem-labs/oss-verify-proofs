(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Classical_Prop.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import DispatchCompute.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YK16 YK0n YK11 YK0i YK0h YK14 YK0v YK02 YK15 YP0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable.R Require Import Cfg.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Local Open Scope Z_scope.
Section b. Context {fx : YK11.FPState}.
Lemma ENOMEM_in_mremap_errnos : In ENOMEM mremap_errnos.
Proof. left. reflexivity. Qed.
Lemma MREMAP_MAYMOVE_val : MREMAP_MAYMOVE = 1.
Proof. reflexivity. Qed.
Lemma page_align_is0_b_false : forall (w : word),
0 < bv_unsigned w -> bv_unsigned w mod page_size = 0 ->
page_align_is0_b w = false /\ page_round_up_Z (bv_unsigned w) = bv_unsigned w.
Proof.
intros w Hpos Hmod.
pose proof (u64_range w) as Hw.
assert (Hr : page_round_up_Z (bv_unsigned w) = bv_unsigned w).
{ apply YK02.page_round_up_Z_aligned; [lia | exact Hmod]. }
split; [|exact Hr].
unfold page_align_is0_b. rewrite Hr.
unfold w_is0. rewrite (bv_eqb_neq w (Z_to_bv 64 0)).
2:{ intros E. rewrite E in Hpos. change (bv_unsigned (Z_to_bv 64 0)) with 0 in Hpos. lia. }
cbn [orb]. apply Z.leb_gt. unfold two_pow_64. lia.
Qed.
Section c.
Variable segs : list Segment.
Lemma chk216 : forall regs pc mem rom model eff,
bv_unsigned (getr regs 17) = 216 ->
check_syscall (sys_input segs (pend_at regs pc mem rom) (getr regs 17)) eff model
= check_mremap (getr regs 10) (getr regs 11) (getr regs 12) (getr regs 13) eff model.
Proof.
intros regs pc mem rom model eff Hno.
rewrite (DispatchCompute.check_syscall_mremap _ eff model) by (rewrite si_sysno; exact Hno).
rewrite ?si_arg0, ?si_arg1, ?si_arg2, ?si_arg3. reflexivity.
Qed.
Record mremap_args (regs : bvmap 5 word) (model : Model) : Prop := mkMremapArgs {
ma_sysno : bv_unsigned (getr regs 17) = 216;
ma_flags : getr regs 13 = Z_to_bv 64 1;
ma_old_al : bv_unsigned (getr regs 10) mod page_size = 0;
ma_oldn_pos : 0 < bv_unsigned (getr regs 11);
ma_oldn_al : bv_unsigned (getr regs 11) mod page_size = 0;
ma_newn_pos : 0 < bv_unsigned (getr regs 12);
ma_newn_al : bv_unsigned (getr regs 12) mod page_size = 0;
ma_newn_lt : bv_unsigned (getr regs 12) < 2 ^ 63;
ma_neq : bv_unsigned (getr regs 11) <> bv_unsigned (getr regs 12);
ma_ceiling : bv_unsigned (getr regs 10) + bv_unsigned (getr regs 11) <= alloc_top (m_vmmaps model);
ma_reserved : region_free (vm_reserved (m_vmmaps model)) (getr regs 10) (getr regs 11) = true;
ma_has : map_has (vm_maps (m_vmmaps model)) (getr regs 10) (getr regs 11) = true;
ma_noaccess : region_free (vm_noaccess (m_vmmaps model)) (getr regs 10) (getr regs 11) = true;
ma_lazy : m_vm_lazy model = []
}.
Definition mremap_chk_body (old old_n new_n : word) (model : Model) (eff : SyscallEffect) : check_result :=
let old_nZ := bv_unsigned old_n in
let new_nZ := bv_unsigned new_n in
match eff with
| mkEffectU r [] zs us cs [] =>
if errno_ret_in mremap_errnos r then
match zs, us, cs with
| [], [], [] => CheckOk model []
| _, _, _ => CheckReject
end
else if bv_eqb r old then
if (new_nZ <? old_nZ) then
if listNN_eqb zs []
&& listNN_eqb us [(bv_add old new_n, Z_to_bv 64 (old_nZ - new_nZ))]
&& listCopy_eqb cs []
then CheckOk (mremap_model_next model old old_n old new_n) []
else CheckReject
else if mremap_inplace_grow_b model old old_n new_n old_nZ new_nZ
then if listNN_eqb zs (mremap_tail old old_n old_nZ new_nZ)
&& listNN_eqb us [] && listCopy_eqb cs []
then CheckOk (mremap_model_next model old old_n old new_n) []
else CheckReject
else CheckReject
else if (old_nZ <? new_nZ)
&& mremap_fresh_b model old_nZ new_nZ old old_n r new_n
&& listNN_eqb zs (mremap_tail r old_n old_nZ new_nZ)
&& listNN_eqb us [(old, old_n)]
&& listCopy_eqb cs [mkCopy old r old_n]
then CheckOk (mremap_model_next model old old_n r new_n) []
else CheckReject
| _ => CheckReject
end.
Lemma mremap_chk : forall regs pc mem rom model eff,
mremap_args regs model ->
check_syscall (sys_input segs (pend_at regs pc mem rom) (getr regs 17)) eff model
= mremap_chk_body (getr regs 10) (getr regs 11) (getr regs 12) model eff.
Proof.
intros regs pc mem rom model eff HA. destruct HA.
rewrite chk216 by assumption. unfold check_mremap.
rewrite ma_flags0. change (bv_unsigned (Z_to_bv 64 1)) with 1. rewrite MREMAP_MAYMOVE_val.
cbn [Z.eqb Pos.eqb negb].
rewrite (proj2 (Z.eqb_eq _ _) ma_old_al0). cbn [negb].
destruct (page_align_is0_b_false (getr regs 12) ma_newn_pos0 ma_newn_al0) as [-> Hr2].
destruct (page_align_is0_b_false (getr regs 11) ma_oldn_pos0 ma_oldn_al0) as [-> Hr1].
cbv zeta. rewrite Hr1, Hr2, !Z_to_bv_bv_unsigned.
unfold mremap_backing_uniform_b. rewrite ma_lazy0. cbn [map_contains region_free existsb orb].
unfold mremap_source_b. rewrite (proj2 (Z.leb_le _ _) ma_ceiling0), ma_reserved0, ma_has0, ma_noaccess0.
cbn [andb negb].
rewrite (proj2 (Z.eqb_neq _ _) ma_neq0).
unfold mremap_chk_body. reflexivity.
Qed.
Definition mremap_J (regs : bvmap 5 word) (pc : word) (mem rom : word -> option byte) (model : Model) : Type :=
{ em : SyscallEffect * Model
| mremap_chk_body (getr regs 10) (getr regs 11) (getr regs 12) model (fst em) = CheckOk (snd em) [] /\
~ spurious_refusal_cfg ACFG (sys_input segs (pend_at regs pc mem rom) (getr regs 17)) model (fst em) }.
Definition mremap_nx (regs : bvmap 5 word) (pc : word) (mem rom : word -> option byte) (model : Model)
(i : mremap_J regs pc mem rom model) : config :=
mkCfg (mkst (regupd regs 10 (eff_ret (fst (proj1_sig i)))) (v_addi pc 4)
(effmem mem (fst (proj1_sig i))) rom)
(snd (proj1_sig i)).
Definition mremap_bit (regs : bvmap 5 word) (pc : word) (mem rom : word -> option byte) (model : Model)
(i : mremap_J regs pc mem rom model) : Z :=
if errno_ret_in mremap_errnos (eff_ret (fst (proj1_sig i))) then 0 else 1.
Lemma mremap_refusal_ok : forall regs model,
mremap_chk_body (getr regs 10) (getr regs 11) (getr regs 12) model
(mkEffectU (errno_ret ENOMEM) [] [] [] [] []) = CheckOk model [].
Proof.
intros regs model. unfold mremap_chk_body.
rewrite (errno_ret_in_intro _ _ ENOMEM_in_mremap_errnos). reflexivity.
Qed.
Lemma mremap_bit_01 : forall regs pc mem rom model i,
mremap_bit regs pc mem rom model i = 0 \/ mremap_bit regs pc mem rom model i = 1.
Proof. intros. unfold mremap_bit. destruct (errno_ret_in _ _); auto. Qed.
Lemma mremap_next_halted : forall m old old_n dst new_n,
m_halted (mremap_model_next m old old_n dst new_n) = m_halted m.
Proof. reflexivity. Qed.



Lemma with_vm_backing_lazy : forall lz mt m, m_vm_lazy (with_vm_backing lz mt m) = lz.
Proof. reflexivity. Qed.

Lemma with_vmmaps_materialized : forall h m, m_vm_materialized (with_vmmaps h m) = m_vm_materialized m.
Proof. reflexivity. Qed.
Lemma mremap_next_lazy : forall m old old_n dst new_n,
m_vm_lazy m = [] -> m_vm_lazy (mremap_model_next m old old_n dst new_n) = [].
Proof.
intros m old old_n dst new_n H. unfold mremap_model_next, mremap_source_lazy_b, vm_resize_backing.
rewrite with_vm_backing_lazy, with_vmmaps_lazy, H. reflexivity.
Qed.

Lemma mremap_next_with_vmmaps : forall m old old_n dst new_n,
m_vm_lazy m = [] -> m_vm_materialized m = [] ->
mremap_model_next m old old_n dst new_n = with_vmmaps (mremap_maps_next (m_vmmaps m) old dst new_n) m.
Proof.
intros m old old_n dst new_n H H'. unfold mremap_model_next, mremap_source_lazy_b, vm_resize_backing.
rewrite with_vmmaps_lazy, with_vmmaps_materialized, H, H'. cbn [map_contains existsb maps_subtract filter app].
destruct m as [fd [vm lz mt] io fs pr li ti]. cbn in H, H'. subst. reflexivity.
Qed.
Lemma mremap_ok_cases : forall (old old_n new_n : word) model eff m',
bv_unsigned old_n <> bv_unsigned new_n ->
mremap_chk_body old old_n new_n model eff = CheckOk m' [] ->
(exists e, In e mremap_errnos /\ eff = mkEffectU (errno_ret e) [] [] [] [] [] /\ m' = model)
\/ (errno_ret_in mremap_errnos (eff_ret eff) = false /\
(
(bv_unsigned new_n < bv_unsigned old_n /\
eff = mkEffectU old [] [] [(bv_add old new_n, Z_to_bv 64 (bv_unsigned old_n - bv_unsigned new_n))] [] [] /\
m' = mremap_model_next model old old_n old new_n)
\/
(bv_unsigned old_n < bv_unsigned new_n /\
mremap_inplace_grow_b model old old_n new_n (bv_unsigned old_n) (bv_unsigned new_n) = true /\
eff = mkEffectU old [] [(bv_add old old_n, Z_to_bv 64 (bv_unsigned new_n - bv_unsigned old_n))] [] [] [] /\
m' = mremap_model_next model old old_n old new_n)
\/
(exists dst, bv_unsigned old_n < bv_unsigned new_n /\ dst <> old /\
mremap_fresh_b model (bv_unsigned old_n) (bv_unsigned new_n) old old_n dst new_n = true /\
eff = mkEffectU dst [] [(bv_add dst old_n, Z_to_bv 64 (bv_unsigned new_n - bv_unsigned old_n))] [(old, old_n)]
[mkCopy old dst old_n] [] /\
m' = mremap_model_next model old old_n dst new_n))).
Proof.
intros old old_n new_n model [r ws zs us cs ci] m' Hne Hk. unfold mremap_chk_body in Hk. cbv zeta in Hk.
destruct ws; [|discriminate]. destruct ci; [|discriminate].
destruct (errno_ret_in mremap_errnos r) eqn:Her.
- destruct zs; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate].
injection Hk as <-. left. apply errno_ret_in_true in Her. destruct Her as (e & He & ->).
exists e. auto.
- right. cbn [eff_ret]. split; [exact Her|].
destruct (bv_eqb r old) eqn:Hro.
+ apply bv_eqb_eq in Hro. subst r.
destruct (bv_unsigned new_n <? bv_unsigned old_n) eqn:Hlt.
* apply Z.ltb_lt in Hlt.
destruct (listNN_eqb zs []) eqn:Hzs; [|discriminate].
destruct (listNN_eqb us [(bv_add old new_n, Z_to_bv 64 (bv_unsigned old_n - bv_unsigned new_n))]) eqn:Hus;
[|discriminate].
destruct (listCopy_eqb cs []) eqn:Hcs; [|discriminate].
apply listNN_eqb_eq in Hzs. apply listNN_eqb_eq in Hus. apply listCopy_eqb_eq in Hcs. subst.
cbn [andb] in Hk. injection Hk as <-. left. auto.
* apply Z.ltb_ge in Hlt.
destruct (mremap_inplace_grow_b model old old_n new_n (bv_unsigned old_n) (bv_unsigned new_n)) eqn:Hg;
[|discriminate].
destruct (listNN_eqb zs (mremap_tail old old_n (bv_unsigned old_n) (bv_unsigned new_n))) eqn:Hzs; [|discriminate].
destruct (listNN_eqb us []) eqn:Hus; [|discriminate].
destruct (listCopy_eqb cs []) eqn:Hcs; [|discriminate].
apply listNN_eqb_eq in Hzs. apply listNN_eqb_eq in Hus. apply listCopy_eqb_eq in Hcs. subst.
cbn [andb] in Hk. injection Hk as <-. right. left.
unfold mremap_tail. rewrite (proj2 (Z.ltb_lt _ _)) by lia. repeat split; try reflexivity. lia.
+ destruct (bv_unsigned old_n <? bv_unsigned new_n) eqn:Hlt; [|discriminate]. apply Z.ltb_lt in Hlt.
destruct (mremap_fresh_b model (bv_unsigned old_n) (bv_unsigned new_n) old old_n r new_n) eqn:Hf; [|discriminate].
destruct (listNN_eqb zs (mremap_tail r old_n (bv_unsigned old_n) (bv_unsigned new_n))) eqn:Hzs; [|discriminate].
destruct (listNN_eqb us [(old, old_n)]) eqn:Hus; [|discriminate].
destruct (listCopy_eqb cs [mkCopy old r old_n]) eqn:Hcs; [|discriminate].
apply listNN_eqb_eq in Hzs. apply listNN_eqb_eq in Hus. apply listCopy_eqb_eq in Hcs. subst.
cbn [andb] in Hk. injection Hk as <-. right. right. exists r.
unfold mremap_tail. rewrite (proj2 (Z.ltb_lt _ _)) by lia.
split; [lia|]. split; [intros ->; rewrite bv_eqb_refl in Hro; discriminate|]. auto.
Qed.
Lemma mremap_ok_model : forall (old old_n new_n : word) model eff m',
bv_unsigned old_n <> bv_unsigned new_n ->
mremap_chk_body old old_n new_n model eff = CheckOk m' [] ->
m_halted m' = m_halted model /\ (m_vm_lazy model = [] -> m_vm_lazy m' = []).
Proof.
intros old old_n new_n model eff m' Hne Hk.
destruct (mremap_ok_cases old old_n new_n model eff m' Hne Hk)
as [(e & _ & _ & ->) | (_ & [(_ & _ & ->) | [(_ & _ & _ & ->) | (dst & _ & _ & _ & _ & ->)]])].
- auto.
- split; [apply mremap_next_halted | apply mremap_next_lazy].
- split; [apply mremap_next_halted | apply mremap_next_lazy].
- split; [apply mremap_next_halted | apply mremap_next_lazy].
Qed.
Lemma mremap_chk_events : forall (old old_n new_n : word) model eff m' evs,
mremap_chk_body old old_n new_n model eff = CheckOk m' evs -> evs = [].
Proof.
intros old old_n new_n model [r ws zs us cs ci] m' evs Hk. unfold mremap_chk_body in Hk. cbv zeta in Hk.
destruct ws; [|discriminate]. destruct ci; [|discriminate].
destruct (errno_ret_in mremap_errnos r).
- destruct zs; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate]. congruence.
- destruct (bv_eqb r old).
+ destruct (bv_unsigned new_n <? bv_unsigned old_n).
* destruct (_ && _ && _); congruence.
* destruct (mremap_inplace_grow_b _ _ _ _ _ _); [|discriminate]. destruct (_ && _ && _); congruence.
+ destruct (_ && _ && _ && _ && _); congruence.
Qed.
Lemma mremap_J_inh : forall regs pc mem rom model,
mremap_args regs model -> inhabited (mremap_J regs pc mem rom model).
Proof.
intros regs pc mem rom model HA.
assert (Hs0 : syscall_spec (sys_input segs (pend_at regs pc mem rom) (getr regs 17)) model
(Ok (mkEffectU (errno_ret ENOMEM) [] [] [] [] []) model [])).
{ apply check_syscall_ok_iff. rewrite (mremap_chk regs pc mem rom model _ HA). apply mremap_refusal_ok. }
destruct (exists_nonspurious ACFG _ _ _ _ _ Hs0) as (eff & m' & evs & Hs & Hns).
apply check_syscall_ok_iff in Hs. rewrite (mremap_chk regs pc mem rom model eff HA) in Hs.
pose proof (mremap_chk_events _ _ _ _ _ _ _ Hs) as ->.
constructor. exists (eff, m'). split; [exact Hs | exact Hns].
Qed.
Lemma node_mremap : forall regs pc mem rom model,
m_halted model = None ->
mremap_args regs model ->
node_ok segs (mkCfg (pend_at regs pc mem rom) model)
(mremap_J regs pc mem rom model) (fun _ => []) (mremap_nx regs pc mem rom model).
Proof.
intros regs pc mem rom model Hh HA.
pose proof (ma_neq _ _ HA) as Hne. pose proof (ma_lazy _ _ HA) as Hlz.
destruct (mremap_J_inh regs pc mem rom model HA) as [i0].
apply (node_chk_cfg segs (pend_at regs pc mem rom) model (getr regs 17) (mremap_J regs pc mem rom model) i0
(fun i => fst (proj1_sig i)) (fun i => snd (proj1_sig i)) (fun _ => []) Hh eq_refl).
- intros [[eff m'] [Hk Hns0]]. cbn [proj1_sig fst snd]. rewrite (mremap_chk regs pc mem rom model eff HA). exact Hk.
- intros [[eff m'] [Hk Hns0]]. cbn [proj1_sig fst snd] in *.
rewrite (proj1 (mremap_ok_model _ _ _ _ _ _ Hne Hk)). exact Hh.
- intros [[eff m'] [Hk Hns0]]. cbn [proj1_sig fst snd] in *.
exact (proj2 (mremap_ok_model _ _ _ _ _ _ Hne Hk) Hlz).
- intros eff m' evs Hk. rewrite (mremap_chk regs pc mem rom model eff HA) in Hk.
pose proof (mremap_chk_events _ _ _ _ _ _ _ Hk) as ->.
destruct (classic (spurious_refusal_cfg ACFG (sys_input segs (pend_at regs pc mem rom) (getr regs 17)) model eff))
as [Hsp | Hns].
+ right. split; [exact Hsp|]. rewrite (proj1 (mremap_ok_model _ _ _ _ _ _ Hne Hk)). exact Hh.
+ left. exists (exist _ (eff, m') (conj Hk Hns)). cbn [proj1_sig fst snd]. auto.
- intros [[eff m'] [Hk0 Hns]]. exact Hns.
Qed.
Definition mremap_post_mem (mem mem' : word -> option byte) (o on r nn : Z) : Prop :=
(forall i, 0 <= i < Z.min on nn -> mem' (Z_to_bv 64 (r + i)) = mem (Z_to_bv 64 (o + i))) /\
(forall i, on <= i < nn -> mem' (Z_to_bv 64 (r + i)) = Some (Z_to_bv 8 0)) /\
(forall a, o <= a < o + on -> ~ (r <= a < r + nn) -> mem' (Z_to_bv 64 a) = None) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (o <= a < o + on) -> ~ (r <= a < r + nn) -> mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
Lemma lit64_u : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia. Qed.
Lemma alloc_top_lt63 : forall h, alloc_top h < 2 ^ 64 - stack_max_size.
Proof. intros h. pose proof (alloc_top_room h). unfold two_pow_64 in *. lia. Qed.
Lemma mremap_mem_shrink : forall (h : VmMaps) mem (old old_n new_n : word),
bv_unsigned new_n < bv_unsigned old_n ->
bv_unsigned old + bv_unsigned old_n <= alloc_top h ->
mremap_post_mem mem
(effmem mem (mkEffectU old [] [] [(bv_add old new_n, Z_to_bv 64 (bv_unsigned old_n - bv_unsigned new_n))] [] []))
(bv_unsigned old) (bv_unsigned old_n) (bv_unsigned old) (bv_unsigned new_n).
Proof.
intros h mem old old_n new_n Hlt Hce.
pose proof (alloc_top_lt63 h) as HC. pose proof stack_max_size_val as HS.
pose proof (u64_range old). pose proof (u64_range new_n). pose proof (u64_range old_n).
assert (Hadd : bv_unsigned (bv_add old new_n) = bv_unsigned old + bv_unsigned new_n).
{ rewrite bv_add_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia. }
assert (Hd : bv_unsigned (Z_to_bv 64 (bv_unsigned old_n - bv_unsigned new_n)) = bv_unsigned old_n - bv_unsigned new_n).
{ apply lit64_u. lia. }
rewrite effmem_unmaps.
split; [|split; [|split]].
- intros i Hi. rewrite apply_unmaps1_out; [reflexivity|]. rewrite Hadd, lit64_u by lia. left. lia.
- intros i Hi. exfalso. lia.
- intros a Ha Hn. apply apply_unmaps1_in. rewrite Hadd, Hd, lit64_u by lia. lia.
- intros a Ha Hn1 Hn2. apply apply_unmaps1_out. rewrite Hadd, Hd, lit64_u by lia. lia.
Qed.
Lemma mremap_mem_grow : forall (h : VmMaps) mem (old old_n new_n : word),
bv_unsigned old_n < bv_unsigned new_n ->
bv_unsigned old + bv_unsigned new_n <= alloc_top h ->
mremap_post_mem mem
(effmem mem (mkEffectU old [] [(bv_add old old_n, Z_to_bv 64 (bv_unsigned new_n - bv_unsigned old_n))] [] [] []))
(bv_unsigned old) (bv_unsigned old_n) (bv_unsigned old) (bv_unsigned new_n).
Proof.
intros h mem old old_n new_n Hlt Hce.
pose proof (alloc_top_lt63 h) as HC. pose proof stack_max_size_val as HS.
pose proof (u64_range old). pose proof (u64_range new_n). pose proof (u64_range old_n).
assert (Hadd : bv_unsigned (bv_add old old_n) = bv_unsigned old + bv_unsigned old_n).
{ rewrite bv_add_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia. }
assert (Hd : bv_unsigned (Z_to_bv 64 (bv_unsigned new_n - bv_unsigned old_n)) = bv_unsigned new_n - bv_unsigned old_n).
{ apply lit64_u. lia. }
rewrite effmem_zeros.
split; [|split; [|split]].
- intros i Hi. rewrite apply_zeros1_out; [reflexivity|]. rewrite Hadd, lit64_u by lia. left. lia.
- intros i Hi. apply apply_zeros1_in. rewrite Hadd, Hd, lit64_u by lia. lia.
- intros a Ha Hn. exfalso. lia.
- intros a Ha Hn1 Hn2. apply apply_zeros1_out. rewrite Hadd, Hd, lit64_u by lia. lia.
Qed.
Lemma mremap_mem_move : forall (h : VmMaps) mem (old old_n dst new_n : word),
bv_unsigned old_n < bv_unsigned new_n ->
bv_unsigned old + bv_unsigned old_n <= alloc_top h ->
bv_unsigned dst + bv_unsigned new_n <= alloc_top h ->
(bv_unsigned dst + bv_unsigned new_n <= bv_unsigned old \/ bv_unsigned old + bv_unsigned old_n <= bv_unsigned dst) ->
mremap_post_mem mem
(effmem mem (mkEffectU dst [] [(bv_add dst old_n, Z_to_bv 64 (bv_unsigned new_n - bv_unsigned old_n))] [(old, old_n)]
[mkCopy old dst old_n] []))
(bv_unsigned old) (bv_unsigned old_n) (bv_unsigned dst) (bv_unsigned new_n).
Proof.
intros h mem old old_n dst new_n Hlt Hce Hcd Hdisj.
pose proof (alloc_top_lt63 h) as HC. pose proof stack_max_size_val as HS.
pose proof (u64_range old). pose proof (u64_range new_n).
pose proof (u64_range old_n). pose proof (u64_range dst).
assert (Hadd : bv_unsigned (bv_add dst old_n) = bv_unsigned dst + bv_unsigned old_n).
{ rewrite bv_add_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia. }
assert (Hd : bv_unsigned (Z_to_bv 64 (bv_unsigned new_n - bv_unsigned old_n)) = bv_unsigned new_n - bv_unsigned old_n).
{ apply lit64_u. lia. }
unfold effmem. cbn [eff_unmaps eff_zeros eff_writes eff_copies apply_writes apply_copies].
unfold apply_copy. cbn [copy_dst copy_src copy_len].
split; [|split; [|split]].
- intros i Hi. rewrite lit64_u by lia.
rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. cbn [andb].
f_equal. apply bv_eq. rewrite !lit64_u by lia. lia.
- intros i Hi. rewrite lit64_u by lia.
rewrite (proj2 (Z.ltb_ge _ _)) by lia. rewrite andb_false_r.
apply apply_zeros1_in. rewrite Hadd, Hd, lit64_u by lia. lia.
- intros a Ha Hn. rewrite lit64_u by lia.
assert (Hc : (bv_unsigned dst <=? a) && (a <? bv_unsigned dst + bv_unsigned old_n) = false).
{ destruct (Z.leb_spec (bv_unsigned dst) a); [|reflexivity]. cbn [andb]. apply Z.ltb_ge. lia. }
rewrite Hc. rewrite apply_zeros1_out by (rewrite Hadd, Hd, lit64_u by lia; lia).
apply apply_unmaps1_in. rewrite lit64_u by lia. lia.
- intros a Ha Hn1 Hn2. rewrite lit64_u by lia.
assert (Hc : (bv_unsigned dst <=? a) && (a <? bv_unsigned dst + bv_unsigned old_n) = false).
{ destruct (Z.leb_spec (bv_unsigned dst) a); [|reflexivity]. cbn [andb]. apply Z.ltb_ge. lia. }
rewrite Hc. rewrite apply_zeros1_out by (rewrite Hadd, Hd, lit64_u by lia; lia).
apply apply_unmaps1_out. rewrite lit64_u by lia. lia.
Qed.
Lemma mremap_inplace_grow_facts : forall model (old old_n new_n : word),
mremap_inplace_grow_b model old old_n new_n (bv_unsigned old_n) (bv_unsigned new_n) = true ->
bv_unsigned old + bv_unsigned new_n <= alloc_top (m_vmmaps model) /\
region_free (vm_reserved (m_vmmaps model) ++ map_remove (vm_maps (m_vmmaps model)) old) old new_n = true /\
mremap_final_budget_b model old old_n old new_n = true.
Proof.
intros model old old_n new_n H. unfold mremap_inplace_grow_b in H. cbv zeta in H.
apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. auto.
Qed.
Lemma mremap_fresh_facts : forall model (old old_n dst new_n : word),
mremap_fresh_b model (bv_unsigned old_n) (bv_unsigned new_n) old old_n dst new_n = true ->
dst <> old /\ bv_unsigned dst mod page_size = 0 /\ 0 < bv_unsigned dst /\
bv_unsigned dst + bv_unsigned new_n <= alloc_top (m_vmmaps model) /\
region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) dst new_n = true /\
mremap_final_budget_b model old old_n dst new_n = true.
Proof.
intros model old old_n dst new_n H. unfold mremap_fresh_b in H. cbv zeta in H.
apply andb_prop in H as [H H6]. apply andb_prop in H as [H H5].
apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
apply Z.leb_le in H4. apply Z.ltb_lt in H3. apply Z.eqb_eq in H2.
split; [|repeat split; auto].
intros ->. rewrite bv_eqb_refl in H1. discriminate.
Qed.
Lemma mremap_fresh_disjoint : forall model (old old_n dst new_n : word),
map_has (vm_maps (m_vmmaps model)) old old_n = true ->
0 < bv_unsigned old_n -> 0 < bv_unsigned new_n ->
mremap_fresh_b model (bv_unsigned old_n) (bv_unsigned new_n) old old_n dst new_n = true ->
bv_unsigned dst + bv_unsigned new_n <= bv_unsigned old \/ bv_unsigned old + bv_unsigned old_n <= bv_unsigned dst.
Proof.
intros model old old_n dst new_n Hhas Hon Hnn Hf.
destruct (mremap_fresh_facts _ _ _ _ _ Hf) as (_ & _ & _ & _ & Hrf & _).
assert (Hin : In (old, old_n) (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model))).
{ apply in_or_app. right. unfold map_has in Hhas. apply existsb_exists in Hhas.
destruct Hhas as ([a s] & Hin & Hp). apply andb_prop in Hp as [Ha Hs].
apply bv_eqb_eq in Ha. apply bv_eqb_eq in Hs. subst. exact Hin. }
pose proof (region_free_In _ _ _ _ _ Hrf Hin) as Hov.
unfold iv_overlap in Hov. apply andb_false_iff in Hov as [Hc|Hc]; apply Z.ltb_ge in Hc; lia.
Qed.
End c.
End b.
