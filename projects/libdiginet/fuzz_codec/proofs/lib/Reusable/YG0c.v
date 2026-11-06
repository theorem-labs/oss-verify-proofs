(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from projects/cgif/cgif_file_fuzzer/proofs/lib/YG0c.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_knock/lib/Reusable/YG0c.v at origin/ossv/recipes 4b6f0df50aa7 (fuzz_knock's released ASan tree); module paths changed to libdiginet/fuzz_codec. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import
YK16 YK0n YK11 YK0h YK0i YK14 YK1c YK0v YK02 YK0p
YK15 YK18 YK0y YK1b YK00 YK01 YK13 YP0n
YK04 YK05 YA0i YA0n YA05 YA09 YK0g YA08.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK0c YK0e YK0f YK09 YA0c YA0e.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0f YG0n.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YM05 YK06.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0b.
Import ListNotations.
Import AX2. Import AX2S. Import APG. Import APSG.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section K.
Variable segs : list Segment.
Definition restore_md (flags addr n : word) (md : Model) : Model :=
with_mmap_backing flags addr n (noaccess_model addr n md).
Lemma same_io_destroyed : forall addr n md, same_io md (fixedin_destroyed_model addr n md).
Proof.
intros. unfold fixedin_destroyed_model, with_mmap_destroyed. eapply same_io_trans; [apply same_io_with_vmmaps | apply same_io_vm_forget_range].
Qed.
Lemma same_io_restore : forall flags addr n md, same_io md (restore_md flags addr n md).
Proof.
intros. unfold restore_md, noaccess_model. eapply same_io_trans; [apply same_io_with_vmmaps | apply same_io_with_mmap_backing].
Qed.
Lemma destroyed_halted : forall addr n md, m_halted (fixedin_destroyed_model addr n md) = m_halted md.
Proof. intros. unfold fixedin_destroyed_model. rewrite with_mmap_destroyed_halted'. reflexivity. Qed.
Lemma restore_halted : forall flags addr n md, m_halted (restore_md flags addr n md) = m_halted md.
Proof. intros. unfold restore_md, noaccess_model. rewrite with_mmap_backing_halted. apply with_vmmaps_halted. Qed.
Lemma destroyed_shape : forall (a n : word) md,
vm_maps (m_vmmaps (fixedin_destroyed_model a n md)) = maps_subtract (vm_maps (m_vmmaps md)) (bv_unsigned a) (bv_unsigned a + bv_unsigned n) /\
vm_noaccess (m_vmmaps (fixedin_destroyed_model a n md)) = maps_subtract (vm_noaccess (m_vmmaps md)) (bv_unsigned a) (bv_unsigned a + bv_unsigned n) /\
vm_reserved (m_vmmaps (fixedin_destroyed_model a n md)) = vm_reserved (m_vmmaps md) /\
vm_limit (m_vmmaps (fixedin_destroyed_model a n md)) = vm_limit (m_vmmaps md) /\
vm_mmap_base (m_vmmaps (fixedin_destroyed_model a n md)) = vm_mmap_base (m_vmmaps md) /\
vm_init_sp (m_vmmaps (fixedin_destroyed_model a n md)) = vm_init_sp (m_vmmaps md) /\
m_vm_lazy (fixedin_destroyed_model a n md) = maps_subtract (m_vm_lazy md) (bv_unsigned a) (bv_unsigned a + bv_unsigned n) /\
m_vm_materialized (fixedin_destroyed_model a n md) = List.filter (page_outside_range (bv_unsigned a) (bv_unsigned a + bv_unsigned n)) (m_vm_materialized md).
Proof.
intros a n md. unfold fixedin_destroyed_model, fixedin_destroyed_vmmaps, with_mmap_destroyed, vm_forget_range. model_proj. cbn [vm_maps vm_noaccess vm_reserved vm_limit vm_mmap_base vm_init_sp].
repeat split; reflexivity.
Qed.
Lemma restore_shape : forall (flags a n : word) md,
vm_maps (m_vmmaps (restore_md flags a n md)) = (a, n) :: vm_maps (m_vmmaps md) /\
vm_noaccess (m_vmmaps (restore_md flags a n md)) = (a, n) :: vm_noaccess (m_vmmaps md) /\
vm_reserved (m_vmmaps (restore_md flags a n md)) = vm_reserved (m_vmmaps md) /\
vm_limit (m_vmmaps (restore_md flags a n md)) = vm_limit (m_vmmaps md) /\
vm_mmap_base (m_vmmaps (restore_md flags a n md)) = vm_mmap_base (m_vmmaps md) /\
vm_init_sp (m_vmmaps (restore_md flags a n md)) = vm_init_sp (m_vmmaps md) /\
m_vm_materialized (restore_md flags a n md) = m_vm_materialized md /\
m_vm_lazy (restore_md flags a n md) = (if mmap_noreserve_b flags then lazy_interior a n else []) ++ m_vm_lazy md.
Proof.
intros flags a n md. unfold restore_md, noaccess_model, with_mmap_backing, vm_add_lazy.
destruct (mmap_noreserve_b flags); model_proj; cbn [vm_maps vm_noaccess vm_reserved vm_limit vm_mmap_base vm_init_sp]; repeat split; reflexivity.
Qed.
Theorem commit_node3 : forall (hole : bool) regs (pc : word) mem rom md (flags addr : word) (len : Z),
m_halted md = None ->
getr regs 17 = Z_to_bv 64 222 ->
getr regs 10 = addr -> bv_unsigned addr mod page_size = 0 -> 0 < bv_unsigned addr ->
getr regs 11 = Z_to_bv 64 len -> 0 < len -> bv_unsigned addr + page_round_up_Z len <= alloc_top (m_vmmaps md) ->
getr regs 12 = Z_to_bv 64 3 -> getr regs 13 = flags -> mmap_flags_core flags = 50 ->
getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
let n := Z_to_bv 64 (page_round_up_Z len) in
(if hole then region_free (vm_reserved (m_vmmaps md) ++ vm_maps (m_vmmaps md)) addr n = true
else region_free (vm_reserved (m_vmmaps md)) addr n = true /\ map_contains (vm_maps (m_vmmaps md)) addr n = true) ->
(if hole then mmap_noreserve_backed_ok flags md (page_round_up_Z len) = true else mmap_fixed_rw_budget_ok flags md addr n = true) ->
exists (I : Type) (nx : I -> config) (bit : I -> Z) (i0 : I),
node_ok segs (mkCfg (pend_at regs pc mem rom) md) I (fun _ => []) nx /\
bit i0 = 1 /\
forall i, exists md_i,
m_halted md_i = None /\ same_io md md_i /\
bit i = 1 /\ nx i = mkCfg (mkst (regupd regs 10 addr) (v_addi pc 4) (zfill addr n mem) rom) md_i /\ md_i = grant_md hole flags addr n md.
Proof.
intros hole regs pc mem rom md flags addr len Hh H17 H10 Hal Hpos H11 Hlen Hce H12 H13 Hcore H14 H15 n Hplace Hbud.
pose proof (alloc_top_room (m_vmmaps md)) as Hcv. unfold two_pow_64, stack_max_size in Hcv. pose proof (u64_range addr) as Har.
assert (Hno : bv_unsigned (getr regs 17) = 222) by (rewrite H17; apply u64_lit; lia).
assert (Hlen' : len < 2 ^ 64) by (pose proof (page_round_up_Z_bounds len ltac:(lia)); lia).
assert (Haddr_ne : errno_ret_in mmap_errnos addr = false).
{ apply errno_ret_in_below; [reflexivity|]. unfold two_pow_64. pose proof (page_round_up_Z_bounds len ltac:(lia)). lia. }
assert (Herr : forall e, In e mmap_errnos -> e = ENOMEM) by (intros e [<-|[]]; reflexivity).
assert (RT : forall r, advance_past_svc (apply_effect (pend_at regs pc mem rom) (mkEffectU r [] [] [] [] [])) = mkst (regupd regs 10 r) (v_addi pc 4) mem rom).
{ intros r. rewrite adv_pend. cbn [eff_ret]. rewrite effmem_ret_only. reflexivity. }
assert (ZF : forall r a k, advance_past_svc (apply_effect (pend_at regs pc mem rom) (mkEffectU r [] [(a, k)] [] [] [])) = mkst (regupd regs 10 r) (v_addi pc 4) (zfill a k mem) rom).
{ intros r a k. rewrite adv_pend. cbn [eff_ret]. rewrite effmem_zeros. unfold zfill. rewrite (apply_zeros_one mem a k). reflexivity. }
assert (UF : forall r a k, advance_past_svc (apply_effect (pend_at regs pc mem rom) (mkEffectU r [] [] [(a, k)] [] [])) = mkst (regupd regs 10 r) (v_addi pc 4) (unfill a k mem) rom).
{ intros r a k. rewrite adv_pend. cbn [eff_ret]. rewrite effmem_unmaps, apply_unmaps_one. reflexivity. }
pose proof (pend_gpr0 regs pc mem rom) as G0. pose proof (pend_gpr1 regs pc mem rom) as G1. pose proof (pend_gpr2 regs pc mem rom) as G2.
pose proof (pend_gpr3 regs pc mem rom) as G3. pose proof (pend_gpr4 regs pc mem rom) as G4. pose proof (pend_gpr5 regs pc mem rom) as G5.
rewrite H10 in G0. rewrite H11 in G1. rewrite H12 in G2. rewrite H13 in G3. rewrite H14 in G4. rewrite H15 in G5.
set (ms := pend_at regs pc mem rom) in *.
destruct hole.
-
pose proof (fun eff => mmap_fixed_rw_free_check segs ms (getr regs 17) md eff flags addr len Hno G0 Hal Hpos G1 Hlen Hce G2 G3 Hcore G4 G5 Hplace) as Hchk.
cbv zeta in Hchk. fold n in Hchk. rewrite Hbud in Hchk.
pose proof (YA09.fixed_addr_not_errno (m_vmmaps md) addr len Hlen Hce) as Hnot.
pose (effs := fun i : unit => mkEffectU addr [] [(addr, n)] [] [] []).
pose (ms' := fun i : unit => with_mmap_backing flags addr n (mmap_model addr n md)).
exists unit, (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)), (fun _ => 1), tt.
split; [| split; [reflexivity |]].
+ apply (YA09.node_chk_grant_mat segs ms md (getr regs 17) unit tt effs ms' _ Hh eq_refl
(YA09.off222 segs ms _ Hno) (YA09.rb222 segs ms _ md Hno)).
* intros []; cbv beta iota delta [effs ms']; rewrite Hchk.
rewrite Hnot, bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
* intros []. exact Hnot.
* intros [r ws zs us cs ci] m' evs Hc Her. cbn [eff_ret] in Her. rewrite Hchk in Hc.
destruct ws; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
rewrite Her in Hc.
destruct (bv_eqb r addr) eqn:Eb; [|discriminate]. destruct (listNN_eqb zs [(addr, n)]) eqn:Hl; [|discriminate].
apply bv_eqb_eq in Eb. apply listNN_eqb_eq in Hl. subst r zs. cbn [andb] in Hc. injection Hc as <- <-.
exists tt. repeat split; reflexivity.
* intros [r ws zs us cs ci] m' evs Hc Her. cbn [eff_ret] in Her. rewrite Hchk in Hc.
destruct ws; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
rewrite Her in Hc. destruct zs; [|discriminate]. injection Hc as <- <-. exact Hh.
* intros []; cbv beta iota delta [ms']; rewrite with_mmap_backing_halted; unfold mmap_model; rewrite with_vmmaps_halted; exact Hh.
* intros []; reflexivity.
+ intros []; cbv beta iota delta [effs ms'].
exists (with_mmap_backing flags addr n (mmap_model addr n md)). split; [rewrite with_mmap_backing_halted; unfold mmap_model; rewrite with_vmmaps_halted; exact Hh|].
split; [exact (same_io_grant true flags addr n md)|]. split; [reflexivity|]. split; [| reflexivity].
subst ms. rewrite ZF. reflexivity.
-
destruct Hplace as [Hrf Hmc].
pose (effs := fun i : unit => mkEffectU addr [] [(addr, n)] [] [] []).
pose (ms' := fun i : unit => fixedin_ok_model 3 flags addr n md).
exists unit, (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)), (fun _ => 1), tt.
split; [| split; [reflexivity |]].
+ exact (node_mmap_fixedin segs ms (getr regs 17) md 3 flags addr len Hh eq_refl Hno (or_intror eq_refl) Hcore
G0 Hal Hpos G1 Hlen G2 G3 G4 G5 Hce Hrf Hmc (fun _ => Hbud)).
+ intros []; cbv beta iota delta [effs ms'].
exists (fixedin_ok_model 3 flags addr n md). split; [unfold fixedin_ok_model; rewrite with_mmap_replacement_halted', with_vmmaps_halted; exact Hh|].
split; [exact (same_io_grant false flags addr n md)|]. split; [reflexivity|]. split; [| reflexivity].
subst ms. rewrite ZF. reflexivity.
Qed.
Theorem destroyed_AI : forall (Hh : word -> bool) A md (addr : word) (len : Z),
AI segs Hh A md -> MWF md ->
bv_unsigned addr mod page_size = 0 -> 0 < len -> bv_unsigned addr + page_round_up_Z len <= alloc_top (m_vmmaps md) ->
let n := Z_to_bv 64 (page_round_up_Z len) in
(AI segs Hh A (fixedin_destroyed_model addr n md) /\ MWF (fixedin_destroyed_model addr n md)) /\
eager_used (fixedin_destroyed_model addr n md) <= eager_used md.
Proof.
intros Hh A md addr len HAI HW Hal Hlen Hce n.
pose proof (alloc_top_room (m_vmmaps md)) as Hcv. unfold two_pow_64, stack_max_size in Hcv. pose proof (u64_range addr) as Ra.
pose proof (page_round_up_Z_bounds len ltac:(lia)) as PR. pose proof (page_round_up_Z_mod len) as PM. unfold page_size in PR, PM.
assert (Un : bv_unsigned n = page_round_up_Z len) by (unfold n; apply u64_lit; lia).
pose proof HW as [(Wm & Wn & Wl & Wi) Ws]. pose proof HAI as (HH1 & HH2 & HH3 & HH4 & HH5).
set (lo := bv_unsigned addr) in *. set (hi := lo + bv_unsigned n).
assert (Hlh : 0 <= lo <= hi) by (subst hi; rewrite Un; lia). assert (Hhi : hi < 2 ^ 64) by (subst hi; rewrite Un; lia).
assert (Hhm : hi mod 4096 = 0).
{ subst hi. rewrite Un. unfold page_size in Hal. apply Z.mod_divide in Hal as [q Hq]; [|lia]. apply Z.mod_divide in PM as [r Hr]; [|lia].
rewrite Hq, Hr. apply Z.mod_divide; [lia|]. exists (q + r). lia. }
pose proof (eager_used_sem md (conj Wm (conj Wn (conj Wl Wi)))) as EQ0.
assert (W' : model_ivs_wf (fixedin_destroyed_model addr n md)).
{ unfold fixedin_destroyed_model, with_mmap_destroyed, fixedin_destroyed_vmmaps. fold lo. fold hi. apply model_ivs_wf_vm_forget_range; [lia|].
apply model_ivs_wf_with_vmmaps; [exact (conj Wm (conj Wn (conj Wl Wi))) | | | reflexivity]; cbn [vm_maps vm_noaccess]; apply maps_subtract_wf; [exact Wm | lia | exact Wn | lia]. }
assert (E_destr : eager_used (fixedin_destroyed_model addr n md) <= eager_used md).
{ rewrite (eager_used_sem _ W'), EQ0. unfold fixedin_destroyed_model, with_mmap_destroyed, fixedin_destroyed_vmmaps. model_proj. cbn [vm_maps vm_noaccess]. fold lo. fold hi.
destruct (maps_subtract_sem (vm_noaccess (m_vmmaps md)) lo hi Wn ltac:(lia)) as (_ & _ & Cn).
destruct (maps_subtract_sem (m_vm_lazy md) lo hi Wl ltac:(lia)) as (_ & _ & Cl).
destruct (maps_subtract_sem (vm_maps (m_vmmaps md)) lo hi Wm ltac:(lia)) as (_ & Sm & _). rewrite Sm.
apply sum_count_mono. intros x. rewrite !covered_app, Cn, Cl.
destruct (covered (vm_noaccess (m_vmmaps md)) x), (covered (m_vm_lazy md) x), (in_rng lo hi x); cbn; congruence. }
split; [| exact E_destr]. split.
- apply (AI_forget segs Hh A md _ lo hi HAI Wl Hlh Hhi Hal Hhm).
+ rewrite destroyed_halted. exact HH5.
+ unfold fixedin_destroyed_model, with_mmap_destroyed, fixedin_destroyed_vmmaps. model_proj. reflexivity.
+ unfold fixedin_destroyed_model, with_mmap_destroyed, fixedin_destroyed_vmmaps. model_proj. reflexivity.
+ pose proof E_destr as ED. destruct HH4 as [_ _ _ _ N5]. destruct (destroyed_shape addr n md) as (_ & _ & _ & DL & _). rewrite DL. lia.
- split; [exact W'|].
destruct (destroyed_shape addr n md) as (DM & _). rewrite DM. fold lo. fold hi.
apply seps_maps_subtract; [exact Wm | lia | exact Hhi | exact Ws].
Qed.
Theorem destroyed_nonempty : forall (addr n : word) md, maps_nonempty md -> maps_nonempty (fixedin_destroyed_model addr n md).
Proof.
intros addr n md H. unfold maps_nonempty. destruct (destroyed_shape addr n md) as (DM & _). rewrite DM.
apply cn_maps_subtract_nonempty. exact H.
Qed.
Lemma region_free_subtract_self : forall l (a n : word),
0 < bv_unsigned n -> bv_unsigned a + bv_unsigned n < 2 ^ 64 ->
region_free (maps_subtract l (bv_unsigned a) (bv_unsigned a + bv_unsigned n)) a n = true.
Proof.
intros l a n Hn Hhi. pose proof (u64_range a) as Ra. pose proof (u64_range n) as Rn.
induction l as [|[b s] l IH]; cbn [maps_subtract]; [reflexivity|].
rewrite YK13.region_free_app, IH, andb_true_r.
pose proof (u64_range b) as Rb. pose proof (u64_range s) as Rs.
unfold iv_subtract. rewrite YK13.region_free_app. apply andb_true_iff. split.
- destruct (Z.ltb_spec (bv_unsigned b) (bv_unsigned a)) as [El|El]; [|reflexivity]. cbn [region_free]. rewrite andb_true_r.
apply negb_true_iff. unfold iv_overlap. rewrite u64_lit by lia. apply andb_false_iff. left. apply Z.ltb_ge. lia.
- destruct (Z.ltb_spec (bv_unsigned a + bv_unsigned n) (bv_unsigned b + bv_unsigned s)) as [Er|Er]; [|reflexivity]. cbn [region_free]. rewrite andb_true_r.
apply negb_true_iff. unfold iv_overlap. rewrite !u64_lit by lia. apply andb_false_iff. right. apply Z.ltb_ge. lia.
Qed.
Theorem destroyed_free : forall (addr : word) (len : Z) md,
0 < len -> bv_unsigned addr + page_round_up_Z len <= alloc_top (m_vmmaps md) ->
let n := Z_to_bv 64 (page_round_up_Z len) in
region_free (vm_reserved (m_vmmaps md)) addr n = true ->
region_free (vm_reserved (m_vmmaps (fixedin_destroyed_model addr n md)) ++ vm_maps (m_vmmaps (fixedin_destroyed_model addr n md))) addr n = true /\
alloc_top (m_vmmaps (fixedin_destroyed_model addr n md)) = alloc_top (m_vmmaps md).
Proof.
intros addr len md Hlen Hce n Hrf.
pose proof (alloc_top_room (m_vmmaps md)) as Hcv. unfold two_pow_64, stack_max_size in Hcv. pose proof (u64_range addr) as Ra.
pose proof (page_round_up_Z_bounds len ltac:(lia)) as PR. unfold page_size in PR.
assert (Un : bv_unsigned n = page_round_up_Z len) by (unfold n; apply u64_lit; lia).
destruct (destroyed_shape addr n md) as (DM & _ & DR & _ & _ & DS & _).
split.
- rewrite DR, DM, YK13.region_free_app, Hrf. cbn [andb]. apply region_free_subtract_self; rewrite Un; lia.
- unfold alloc_top. rewrite DS. reflexivity.
Qed.
Theorem kept_occupied : forall l1 l2 (addr n : word), 0 < bv_unsigned n -> map_contains l2 addr n = true -> region_free (l1 ++ l2) addr n = false.
Proof.
intros l1 l2 addr n Hn Hmc. rewrite YK13.region_free_app. apply andb_false_iff. right.
destruct (map_contains_In l2 addr n Hmc) as ([b s] & Hin & Q1 & Q2). unfold B, YK0g.S in Q1, Q2. cbn [fst snd] in Q1, Q2.
clear Hmc. induction l2 as [|[b' s'] l IH]; [destruct Hin|]. cbn [region_free]. destruct Hin as [E|Hin].
- injection E as -> ->. apply andb_false_iff. left. apply negb_false_iff. unfold iv_overlap. apply andb_true_iff. split; apply Z.ltb_lt; lia.
- rewrite (IH Hin). apply andb_false_r.
Qed.
Theorem restore_AI : forall (Hh : word -> bool) A md (flags addr : word) (len : Z),
AI segs Hh A md -> MWF md -> mmap_noreserve_b flags = true ->
bv_unsigned addr mod page_size = 0 -> 0 < len -> bv_unsigned addr + page_round_up_Z len <= alloc_top (m_vmmaps md) ->
let n := Z_to_bv 64 (page_round_up_Z len) in
region_free (vm_reserved (m_vmmaps md) ++ vm_maps (m_vmmaps md)) addr n = true ->
(forall w : word, bv_unsigned addr <= bv_unsigned w < bv_unsigned addr + page_round_up_Z len -> Hh w = false -> page_allowedb A (page_base w) = true) ->
(AI segs Hh A (restore_md flags addr n md) /\ MWF (restore_md flags addr n md)) /\
eager_used (restore_md flags addr n md) <= eager_used md.
Proof.
intros Hh A md flags addr len HAI HW Hnr Hal Hlen Hce n Hplace HAL.
pose proof (alloc_top_room (m_vmmaps md)) as Hcv. unfold two_pow_64, stack_max_size in Hcv. pose proof (u64_range addr) as Ra.
pose proof (page_round_up_Z_bounds len ltac:(lia)) as PR. pose proof (page_round_up_Z_mod len) as PM. unfold page_size in PR, PM.
assert (Un : bv_unsigned n = page_round_up_Z len) by (unfold n; apply u64_lit; lia).
pose proof HW as [(Wm & Wn & Wl & Wi) Ws]. pose proof HAI as (HH1 & HH2 & HH3 & HH4 & HH5).
set (lo := bv_unsigned addr) in *. set (hi := lo + bv_unsigned n).
assert (Hlh : 0 <= lo <= hi) by (subst hi; rewrite Un; lia). assert (Hhi : hi < 2 ^ 64) by (subst hi; rewrite Un; lia).
assert (LI : lazy_interior addr n = [(addr, n)]).
{ apply lazy_interior_aligned; unfold page_size; [exact Hal | rewrite Un; exact PM | rewrite Un; lia | fold lo; lia]. }
destruct (restore_shape flags addr n md) as (RM & RN & RR & RL & RB & RS & RMat & RLz). rewrite Hnr, LI in RLz. cbn [app] in RLz.
pose proof (eager_used_sem md (conj Wm (conj Wn (conj Wl Wi)))) as EQ0.
assert (IVn : iv_wf (addr, n)) by (unfold iv_wf, B, YK0g.S; cbn [fst snd]; fold lo; lia).
assert (WOK : model_ivs_wf (restore_md flags addr n md)).
{ unfold model_ivs_wf. rewrite RM, RN, RLz. split; [apply ivs_wf_cons; [exact IVn | exact Wm]|]. split; [apply ivs_wf_cons; [exact IVn | exact Wn]|].
split; [apply ivs_wf_cons; [exact IVn | exact Wl] |]. unfold init_sp_ok in *. rewrite RS. exact Wi. }
assert (EOKle : eager_used (restore_md flags addr n md) <= eager_used md).
{ rewrite (eager_used_sem _ WOK), EQ0, RM, RN, RLz. cbn [sum_count].
assert (Z0 : iv_count (fun x => negb (covered (((addr, n) :: vm_noaccess (m_vmmaps md)) ++ (addr, n) :: m_vm_lazy md) x)) (addr, n) = 0).
{ unfold iv_count. apply zcount_false. intros x Hx. apply negb_false_iff. cbn [app covered existsb]. unfold in_iv, in_rng, B, YK0g.S. cbn [fst snd].
unfold B, YK0g.S in Hx. cbn [fst snd] in Hx. fold lo in Hx |- *. pose proof (u64_range n) as Rn. rewrite Z2Nat.id in Hx by lia.
apply orb_true_iff. left. apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
rewrite Z0. cbn [Z.add].
apply sum_count_mono. intros x Hx. apply negb_true_iff in Hx. apply negb_true_iff.
rewrite covered_app in Hx |- *.
change (covered ((addr, n) :: vm_noaccess (m_vmmaps md)) x) with (in_iv (addr, n) x || covered (vm_noaccess (m_vmmaps md)) x) in Hx.
change (covered ((addr, n) :: m_vm_lazy md) x) with (in_iv (addr, n) x || covered (m_vm_lazy md) x) in Hx.
destruct (in_iv (addr, n) x), (covered (vm_noaccess (m_vmmaps md)) x), (covered (m_vm_lazy md) x); cbn in Hx |- *; congruence. }
split; [| exact EOKle]. split.
- split; [exact HH1|]. split; [exact HH2|]. split.
+ intros w Hl Hw. rewrite RLz in Hl. rewrite page_in_ranges_cons in Hl. cbn [fst snd] in Hl. apply orb_true_iff in Hl as [Hl|Hl].
* apply andb_true_iff in Hl as [L1 L2]. apply Z.leb_le in L1. apply Z.leb_le in L2. fold lo in L1, L2.
pose proof (page_base_facts w) as PB. unfold page_size in *. apply (HAL w); [| exact Hw]. rewrite <- Un. fold hi. lia.
* exact (HH3 w Hl Hw).
+ split; [| rewrite restore_halted; exact HH5]. destruct HH4 as [N1 N2 N3 N4 N5]. constructor; rewrite ?RMat, ?RLz, ?RL.
* exact N1.
* exact N2.
* exact N3.
* intros p Hp. rewrite page_in_ranges_cons. rewrite (N4 p Hp). apply orb_true_r.
* lia.
- split; [exact WOK|]. rewrite RM. apply seps_cons; [| exact Ws].
rewrite YK13.region_free_app in Hplace. apply andb_true_iff in Hplace as [_ Hrf].
apply Forall_forall. intros [a sz] Hin. unfold iv_disjoint. cbn [fst snd].
assert (X : iv_overlap addr n a sz = false).
{ clear - Hrf Hin. induction (vm_maps (m_vmmaps md)) as [|[b s] l IH]; [destruct Hin|]. cbn [region_free] in Hrf.
apply andb_true_iff in Hrf as [H1 H2]. destruct Hin as [Heq | Hin]; [injection Heq as -> ->; apply negb_true_iff in H1; exact H1 | exact (IH H2 Hin)]. }
unfold iv_overlap in X. apply andb_false_iff in X as [X|X]; apply Z.ltb_ge in X; fold lo in X; lia.
Qed.
Theorem restore_nonempty : forall (flags addr n : word) md, 0 < bv_unsigned n -> maps_nonempty md -> maps_nonempty (restore_md flags addr n md).
Proof.
intros flags addr n md Hn H. unfold maps_nonempty. destruct (restore_shape flags addr n md) as (RM & _). rewrite RM.
intros q [<-|Hq]; [exact Hn | exact (H q Hq)].
Qed.
End K.
End c.
