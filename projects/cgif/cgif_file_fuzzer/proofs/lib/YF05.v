(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK16 YK0n YK11 YK0h YK0i YK14 YK1c YK0v YK02 YK0p YK15 YK18 YK0y YK1b YK00 YK01 YK13 YP0n YK04 YK05 YA0i YA0n YA05 YA09 YK0g YA08 YG0b.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0f YG0n.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section K.
Variable segs : list Segment.
Lemma remap_ok_model : forall flags addr n md, mmap_noreserve_b flags = true ->
fixedin_ok_model 3 flags addr n md =
vm_add_lazy addr n (vm_forget_range (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n) (with_vmmaps (mmap_fixed_rw_next (m_vmmaps md) addr n) md)).
Proof.
intros flags addr n md Hnr. unfold fixedin_ok_model, fixedin_ok_vmmaps, with_mmap_replacement, with_mmap_backing. rewrite Hnr. cbn [Z.eqb]. reflexivity.
Qed.
Theorem remap_AI : forall (Hh : word -> bool) A md (flags addr : word) (len : Z),
AI segs Hh A md -> MWF md -> mmap_noreserve_b flags = true ->
bv_unsigned addr mod page_size = 0 -> 0 < len -> bv_unsigned addr + page_round_up_Z len <= alloc_ceiling ->
let n := Z_to_bv 64 (page_round_up_Z len) in
(forall w : word, bv_unsigned addr <= bv_unsigned w < bv_unsigned addr + page_round_up_Z len -> Hh w = false -> page_allowedb A (page_base w) = true) ->
(AI segs Hh A (grant_md false flags addr n md) /\ MWF (grant_md false flags addr n md)) /\
mmap_fixed_rw_budget_ok flags md addr n = true.
Proof.
intros Hh A md flags addr len HAI HW Hnr Hal Hlen Hce n HAL.
pose proof alloc_ceiling_val as Hcv. pose proof (u64_range addr) as Ra.
pose proof (page_round_up_Z_bounds len ltac:(lia)) as PR. pose proof (page_round_up_Z_mod len) as PM. unfold page_size in PR, PM.
assert (Un : bv_unsigned n = page_round_up_Z len) by (unfold n; apply u64_lit; lia).
pose proof HW as [(Wm & Wn & Wl & Wsp) Ws].     pose proof HAI as (HH1 & HH2 & HH3 & HH4 & HH5).
set (lo := bv_unsigned addr) in *. set (hi := lo + bv_unsigned n).
assert (Hlh : 0 <= lo <= hi) by (subst hi; rewrite Un; lia). assert (Hhi : hi < 2 ^ 64) by (subst hi; rewrite Un; lia).
assert (Hhm : hi mod 4096 = 0).
{ subst hi. rewrite Un. unfold page_size in Hal. apply Z.mod_divide in Hal as [q Hq]; [|lia]. apply Z.mod_divide in PM as [r Hr]; [|lia].
rewrite Hq, Hr. apply Z.mod_divide; [lia|]. exists (q + r). lia. }
assert (LI : lazy_interior addr n = [(addr, n)]).
{ apply lazy_interior_aligned; unfold page_size; [exact Hal | rewrite Un; exact PM | rewrite Un; lia | fold lo; lia]. }
pose proof (eager_used_sem md (conj Wm (conj Wn (conj Wl Wsp)))) as EQ0.
set (mdF := vm_forget_range lo hi (with_vmmaps (mmap_fixed_rw_next (m_vmmaps md) addr n) md)).
set (mdOK := vm_add_lazy addr n mdF).
assert (EOK : grant_md false flags addr n md = mdOK) by (unfold grant_md, mdOK, mdF; rewrite (remap_ok_model flags addr n md Hnr); reflexivity).
assert (OKv : m_vmmaps mdOK = mmap_fixed_rw_next (m_vmmaps md) addr n) by (unfold mdOK, mdF; model_proj; reflexivity).
assert (OKl : m_vm_lazy mdOK = (addr, n) :: maps_subtract (m_vm_lazy md) lo hi) by (unfold mdOK, mdF; model_proj; rewrite LI; reflexivity).
assert (OKm : m_vm_materialized mdOK = List.filter (page_outside_range lo hi) (m_vm_materialized md)) by (unfold mdOK, mdF; model_proj; reflexivity).
assert (OKh : m_halted mdOK = None) by (unfold mdOK, mdF; rewrite vm_add_lazy_halted; unfold vm_forget_range; rewrite with_vm_backing_halted, with_vmmaps_halted; exact HH5).
assert (WOK : model_ivs_wf mdOK).
{ unfold model_ivs_wf. rewrite OKv, OKl. unfold mmap_fixed_rw_next. cbn [vm_maps vm_noaccess vm_init_sp]. split; [exact Wm|]. split; [apply maps_subtract_wf; [exact Wn | lia]|].
split; [| exact Wsp].
apply ivs_wf_cons; [| apply maps_subtract_wf; [exact Wl | lia]]. unfold iv_wf, B, YK0g.S. cbn [fst snd]. fold lo. fold hi. lia. }
destruct (maps_subtract_sem (vm_noaccess (m_vmmaps md)) lo hi Wn ltac:(lia)) as (_ & _ & Cn).
destruct (maps_subtract_sem (m_vm_lazy md) lo hi Wl ltac:(lia)) as (_ & _ & Cl).
assert (EOKle : eager_used mdOK <= eager_used md).
{ rewrite (eager_used_sem _ WOK), EQ0. rewrite OKv, OKl. unfold mmap_fixed_rw_next. cbn [vm_maps vm_noaccess].
apply sum_count_mono. intros x Hx. rewrite !covered_app in Hx |- *. change ((addr, n) :: maps_subtract (m_vm_lazy md) lo hi) with ([(addr, n)] ++ maps_subtract (m_vm_lazy md) lo hi) in Hx.
rewrite covered_app, Cn, Cl in Hx. cbn [covered existsb] in Hx. unfold in_iv, B, YK0g.S in Hx. cbn [fst snd] in Hx. fold lo in Hx. fold hi in Hx.
destruct (covered (vm_noaccess (m_vmmaps md)) x), (covered (m_vm_lazy md) x), (in_rng lo hi x); cbn in Hx |- *; congruence. }
pose proof (mat_le_A segs Hh A md HAI) as MA. unfold page_size in MA.
assert (MLle : Z.of_nat (length (m_vm_materialized mdOK)) <= Z.of_nat (length (m_vm_materialized md))).
{ rewrite OKm. pose proof (filter_length_le (page_outside_range lo hi) (m_vm_materialized md)). lia. }
split.
-   rewrite EOK. split.
+ split; [exact HH1|]. split; [exact HH2|]. split.
*
intros w Hl Hw. rewrite OKl in Hl. rewrite page_in_ranges_cons in Hl. cbn [fst snd] in Hl. apply orb_true_iff in Hl as [Hl|Hl].
-- apply andb_true_iff in Hl as [L1 L2]. apply Z.leb_le in L1. apply Z.leb_le in L2. fold lo in L1, L2. fold hi in L2.
pose proof (page_base_facts w) as PB. unfold page_size in *. apply (HAL w); [| exact Hw]. rewrite <- Un. fold hi. lia.
-- apply (HH3 w); [| exact Hw]. exact (page_in_subtract_back _ lo hi _ ltac:(lia) Hhi Wl Hl).
* split; [| exact OKh]. destruct HH4 as [N1 N2 N3 N4 N5]. constructor; rewrite ?OKm, ?OKl, ?OKv.
-- apply NoDup_filter. exact N1.
-- intros p Hp. apply filter_In in Hp as [Hp _]. exact (N2 p Hp).
-- intros p Hp. apply filter_In in Hp as [Hp _]. exact (N3 p Hp).
-- intros p Hp. apply filter_In in Hp as [Hp Ho]. rewrite page_in_ranges_cons. cbn [fst snd]. apply orb_true_iff. right.
pose proof (N2 p Hp) as Hpal. pose proof (N4 p Hp) as Hpl.
apply page_in_subtract_keep; [lia | exact Hhi | lia | exact Wl | | exact Hpl].
unfold page_outside_range in Ho. apply negb_true_iff in Ho. apply andb_false_iff in Ho. unfold page_size in *.
pose proof (u64_range p) as Rp. pose proof Hal as Hal'.
apply Z.mod_divide in Hpal as [q Hq]; [|lia]. apply Z.mod_divide in Hal' as [ql Hql]; [|lia].
destruct Ho as [Ho | Ho]; [apply Z.leb_gt in Ho; left | apply Z.ltb_ge in Ho; right; exact Ho]. fold lo in Hql. rewrite Hq, Hql in *. nia.
-- unfold mmap_fixed_rw_next. cbn [vm_limit]. lia.
+ split; [exact WOK|]. rewrite OKv. unfold mmap_fixed_rw_next. cbn [vm_maps]. exact Ws.
-
unfold mmap_fixed_rw_budget_ok, vm_backing_within_limit. apply Z.leb_le.
assert (Em : with_mmap_replacement flags addr n (with_vmmaps (mmap_fixed_rw_next (m_vmmaps md) addr n) md) = mdOK).
{ unfold with_mmap_replacement, with_mmap_backing, mdOK, mdF. rewrite Hnr. reflexivity. }
rewrite Em, vm_backing_used_split, OKv. destruct HH4 as [N1 N2 N3 N4 N5].
assert (vm_limit (mmap_fixed_rw_next (m_vmmaps md) addr n) = vm_limit (m_vmmaps md)) as -> by reflexivity.
unfold page_size. nia.
Qed.
Theorem remap_shape : forall md (flags addr : word) (len : Z),
MWF md -> mmap_noreserve_b flags = true ->
bv_unsigned addr mod page_size = 0 -> 0 < len -> bv_unsigned addr + page_round_up_Z len <= alloc_ceiling ->
let n := Z_to_bv 64 (page_round_up_Z len) in
let md' := grant_md false flags addr n md in
vm_maps (m_vmmaps md') = vm_maps (m_vmmaps md) /\ vm_reserved (m_vmmaps md') = vm_reserved (m_vmmaps md) /\
vm_limit (m_vmmaps md') = vm_limit (m_vmmaps md) /\ vm_mmap_base (m_vmmaps md') = vm_mmap_base (m_vmmaps md) /\
m_vm_lazy md' = (addr, n) :: maps_subtract (m_vm_lazy md) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n) /\
eager_used md' <= eager_used md.
Proof.
intros md flags addr len HW Hnr Hal Hlen Hce n md'.
pose proof alloc_ceiling_val as Hcv. pose proof (u64_range addr) as Ra.
pose proof (page_round_up_Z_bounds len ltac:(lia)) as PR. pose proof (page_round_up_Z_mod len) as PM. unfold page_size in PR, PM.
assert (Un : bv_unsigned n = page_round_up_Z len) by (unfold n; apply u64_lit; lia).
pose proof HW as [(Wm & Wn & Wl & Wsp) Ws].
set (lo := bv_unsigned addr) in *. set (hi := lo + bv_unsigned n).
assert (Hlh : 0 <= lo <= hi) by (subst hi; rewrite Un; lia). assert (Hhi : hi < 2 ^ 64) by (subst hi; rewrite Un; lia).
assert (LI : lazy_interior addr n = [(addr, n)]).
{ apply lazy_interior_aligned; unfold page_size; [exact Hal | rewrite Un; exact PM | rewrite Un; lia | fold lo; lia]. }
pose proof (eager_used_sem md (conj Wm (conj Wn (conj Wl Wsp)))) as EQ0.
set (mdF := vm_forget_range lo hi (with_vmmaps (mmap_fixed_rw_next (m_vmmaps md) addr n) md)).
set (mdOK := vm_add_lazy addr n mdF).
assert (EOK : md' = mdOK) by (unfold md', grant_md, mdOK, mdF; rewrite (remap_ok_model flags addr n md Hnr); reflexivity).
assert (OKv : m_vmmaps mdOK = mmap_fixed_rw_next (m_vmmaps md) addr n) by (unfold mdOK, mdF; model_proj; reflexivity).
assert (OKl : m_vm_lazy mdOK = (addr, n) :: maps_subtract (m_vm_lazy md) lo hi) by (unfold mdOK, mdF; model_proj; rewrite LI; reflexivity).
assert (WOK : model_ivs_wf mdOK).
{ unfold model_ivs_wf. rewrite OKv, OKl. unfold mmap_fixed_rw_next. cbn [vm_maps vm_noaccess vm_init_sp]. split; [exact Wm|]. split; [apply maps_subtract_wf; [exact Wn | lia]|].
split; [| exact Wsp].
apply ivs_wf_cons; [| apply maps_subtract_wf; [exact Wl | lia]]. unfold iv_wf, B, YK0g.S. cbn [fst snd]. fold lo. fold hi. lia. }
destruct (maps_subtract_sem (vm_noaccess (m_vmmaps md)) lo hi Wn ltac:(lia)) as (_ & _ & Cn).
destruct (maps_subtract_sem (m_vm_lazy md) lo hi Wl ltac:(lia)) as (_ & _ & Cl).
rewrite EOK. rewrite OKv, OKl. unfold mmap_fixed_rw_next. cbn [vm_maps vm_reserved vm_limit vm_mmap_base vm_noaccess].
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
rewrite (eager_used_sem _ WOK), EQ0. rewrite OKv, OKl. unfold mmap_fixed_rw_next. cbn [vm_maps vm_noaccess].
apply sum_count_mono. intros x Hx. rewrite !covered_app in Hx |- *. change ((addr, n) :: maps_subtract (m_vm_lazy md) lo hi) with ([(addr, n)] ++ maps_subtract (m_vm_lazy md) lo hi) in Hx.
rewrite covered_app, Cn, Cl in Hx. cbn [covered existsb] in Hx. unfold in_iv, B, YK0g.S in Hx. cbn [fst snd] in Hx. fold lo in Hx. fold hi in Hx.
destruct (covered (vm_noaccess (m_vmmaps md)) x), (covered (m_vm_lazy md) x), (in_rng lo hi x); cbn in Hx |- *; congruence.
Qed.
Lemma remap_allowed_of_lazy : forall (Hh : word -> bool) A md (lo hi : Z),
AI segs Hh A md ->
(forall p : word, lo <= bv_unsigned p -> bv_unsigned p + page_size <= hi -> page_in_ranges p (m_vm_lazy md) = true) ->
lo mod page_size = 0 -> hi mod page_size = 0 ->
forall w : word, lo <= bv_unsigned w < hi -> Hh w = false -> page_allowedb A (page_base w) = true.
Proof.
intros Hh A md lo hi (_ & _ & LC & _) HL Hlo Hhi w Hw Hx. apply (LC w); [| exact Hx].
pose proof (page_base_facts w) as (P1 & P2 & P3). pose proof (u64_range w) as Rw. unfold page_size in *.
apply Z.mod_divide in P3 as [m Hm]; [|lia]. apply Z.mod_divide in Hlo as [q Hq]; [|lia]. apply Z.mod_divide in Hhi as [r Hr]; [|lia].
apply HL; rewrite Hm; [rewrite Hq | rewrite Hr]; nia.
Qed.
Theorem anon_node : forall regs (pc : word) mem rom md (flags : word) (len : Z),
m_halted md = None ->
getr regs 17 = Z_to_bv 64 222 ->
getr regs 10 = Z_to_bv 64 0 ->
getr regs 11 = Z_to_bv 64 len -> 0 < len < 2 ^ 64 ->
getr regs 12 = Z_to_bv 64 3 -> getr regs 13 = flags -> mmap_flags_core flags = 34 ->
getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
let nZ := page_round_up_Z len in let n := Z_to_bv 64 nZ in
(exists a, grant_ok_na_pin md a nZ = true) -> mmap_noreserve_backed_ok flags md nZ = true ->
exists (I : Type) (nx : I -> config) (bit : I -> Z) (ga : I -> word) (i0 : I),
node_ok segs (mkCfg (pend_at regs pc mem rom) md) I (fun _ => []) nx /\
bit i0 = 1 /\
forall i, exists md_i,
m_halted md_i = None /\ same_io md md_i /\
bit i = 1 /\ grant_ok_na_pin md (ga i) nZ = true /\
nx i = mkCfg (mkst (regupd regs 10 (ga i)) (v_addi pc 4) (zfill (ga i) n mem) rom) md_i /\
md_i = with_mmap_backing flags (ga i) n (mmap_model (ga i) n md).
Proof.
intros regs pc mem rom md flags len Hh H17 H10 H11 Hlen H12 H13 Hcore H14 H15 nZ n (a0 & Ha0) Hb0.
assert (Hno : bv_unsigned (getr regs 17) = 222) by (rewrite H17; apply u64_lit; lia).
assert (RT : forall r, advance_past_svc (apply_effect (pend_at regs pc mem rom) (mkEffectU r [] [] [] [] [])) = mkst (regupd regs 10 r) (v_addi pc 4) mem rom).
{ intros r. rewrite adv_pend. cbn [eff_ret]. rewrite effmem_ret_only. reflexivity. }
assert (ZF : forall r a k, advance_past_svc (apply_effect (pend_at regs pc mem rom) (mkEffectU r [] [(a, k)] [] [] [])) = mkst (regupd regs 10 r) (v_addi pc 4) (zfill a k mem) rom).
{ intros r a k. rewrite adv_pend. cbn [eff_ret]. rewrite effmem_zeros. unfold zfill. rewrite (apply_zeros_one mem a k). reflexivity. }
pose proof (pend_gpr1 regs pc mem rom) as G1. pose proof (pend_gpr2 regs pc mem rom) as G2.
pose proof (pend_gpr3 regs pc mem rom) as G3. pose proof (pend_gpr4 regs pc mem rom) as G4. pose proof (pend_gpr5 regs pc mem rom) as G5.
rewrite H11 in G1. rewrite H12 in G2. rewrite H13 in G3. rewrite H14 in G4. rewrite H15 in G5.
set (ms := pend_at regs pc mem rom) in *.
assert (Hl1 : bv_unsigned (ms_gpr ms 1) = len) by (rewrite G1; apply u64_lit; lia).
assert (Hne1 : ms_gpr ms 1 <> Z_to_bv 64 0).
{ rewrite G1. intros E. apply (f_equal bv_unsigned) in E. rewrite !u64_lit in E by lia. lia. }
pose proof (fun eff => mmap_rw_check segs ms (getr regs 17) md eff flags Hno Hne1 G2 G3 Hcore G4 G5) as Hchk.
cbv zeta in Hchk. rewrite Hl1 in Hchk. fold nZ n in Hchk. rewrite Hb0 in Hchk.
assert (Hn0 : 0 <= nZ) by (unfold nZ; apply page_round_up_Z_nonneg; lia).
pose (IB := {a : word | grant_ok_na_pin md a nZ = true}).
pose (effs := fun i : IB => match i with exist _ a _ => mkEffectU a [] [(a, n)] [] [] [] end).
pose (ms' := fun i : IB => match i with exist _ a _ => with_mmap_backing flags a n (mmap_model a n md) end).
exists IB, (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)),
(fun _ => 1), (fun i => match i with exist _ a _ => a end), (exist _ a0 Ha0).
split; [| split; [reflexivity |]].
- apply (YA09.node_chk_grant_mat segs ms md (getr regs 17) IB (exist _ a0 Ha0) effs ms' _ Hh eq_refl
(YA09.off222 segs ms _ Hno) (YA09.rb222 segs ms _ md Hno)).
+ intros [a Ha]; cbn [effs ms']; rewrite Hchk.
rewrite (YA09.grant_na_pin_not_errno md a nZ Ha Hn0), Ha. cbn [andb]. rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
+ intros [a Ha]. cbn [effs eff_ret]. exact (YA09.grant_na_pin_not_errno md a nZ Ha Hn0).
+ intros [r ws zs us cs ci] m' evs Hc Her. cbn [eff_ret] in Her. rewrite Hchk in Hc.
destruct ws; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
rewrite Her in Hc.
destruct (grant_ok_na_pin md r nZ) eqn:Hg; [|discriminate]. cbn [andb] in Hc.
destruct (listNN_eqb zs [(r, n)]) eqn:Hl; [|discriminate].
apply listNN_eqb_eq in Hl. subst zs. injection Hc as <- <-.
exists (exist _ r Hg). repeat split; reflexivity.
+ intros [r ws zs us cs ci] m' evs Hc Her. cbn [eff_ret] in Her. rewrite Hchk in Hc.
destruct ws; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
rewrite Her in Hc. destruct zs; [|discriminate]. injection Hc as <- <-. exact Hh.
+ intros [a Ha]; cbn [ms']; rewrite with_mmap_backing_halted; unfold mmap_model; rewrite with_vmmaps_halted; exact Hh.
+ intros [a Ha]; reflexivity.
- intros [a Ha]; cbn [effs ms'].
exists (with_mmap_backing flags a n (mmap_model a n md)).
split; [rewrite with_mmap_backing_halted; unfold mmap_model; rewrite with_vmmaps_halted; exact Hh|].
split; [eapply same_io_trans; [apply same_io_with_vmmaps | apply same_io_with_mmap_backing]|].
split; [reflexivity|]. split; [exact Ha|]. split; [| reflexivity].
subst ms. rewrite ZF. reflexivity.
Qed.
End K.
End b.
