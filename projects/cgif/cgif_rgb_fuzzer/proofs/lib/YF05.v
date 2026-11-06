(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK16 YK0o YK11 YK0i YK0j YK14 YK1c YK0v YK02 YK0q YK15 YK18 YK0y YK1b YK00 YK01 YK13 YQ0k YK05 YK06 YA0i YA0l YA05 YA09 YK0h YA08 YG0b.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG0h YG0u.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section K.
Variable segs : list Segment.




Theorem anon_node : forall regs (pc : word) mem rom md (flags : word) (len : Z),
m_halted md = None ->
getr regs 17 = Z_to_bv 64 222 ->
getr regs 10 = Z_to_bv 64 0 ->
getr regs 11 = Z_to_bv 64 len -> 0 < len < 2 ^ 64 ->
getr regs 12 = Z_to_bv 64 3 -> getr regs 13 = flags -> mmap_flags_core flags = 34 ->
getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
let nZ := page_round_up_Z len in let n := Z_to_bv 64 nZ in
(exists a, grant_ok_na_pin md a nZ = true) -> mmap_noreserve_backed_ok flags md nZ = true ->
exists (I : Type) (nx : I -> config) (bit : I -> Z) (ga : I -> word) (i0 i1 : I),
node_ok segs (mkCfg (pend_at regs pc mem rom) md) I (fun _ => []) nx /\
bit i0 = 1 /\ bit i1 = 0 /\
forall i, exists md_i,
m_halted md_i = None /\ same_io md md_i /\
( (bit i = 0 /\ nx i = mkCfg (mkst (regupd regs 10 (errno_ret ENOMEM)) (v_addi pc 4) mem rom) md_i /\ md_i = md)
\/ (bit i = 1 /\ grant_ok_na_pin md (ga i) nZ = true /\
nx i = mkCfg (mkst (regupd regs 10 (ga i)) (v_addi pc 4) (zfill (ga i) n mem) rom) md_i /\
md_i = with_mmap_backing flags (ga i) n (mmap_model (ga i) n md))).
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
pose (effs := fun i : unit + IB => match i with
| inl _ => mkEffectU (errno_ret ENOMEM) [] [] [] [] []
| inr (exist _ a _) => mkEffectU a [] [(a, n)] [] [] [] end).
pose (ms' := fun i : unit + IB => match i with
| inl _ => md
| inr (exist _ a _) => with_mmap_backing flags a n (mmap_model a n md) end).
exists (unit + IB)%type, (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)),
(fun i => match i with inl _ => 0 | inr _ => 1 end),
(fun i => match i with inl _ => Z_to_bv 64 0 | inr (exist _ a _) => a end),
(inr (exist _ a0 Ha0)), (inl tt).
split; [| split; [reflexivity | split; [reflexivity |]]].
- apply (node_chk_noacc segs ms md (getr regs 17) (unit + IB) effs ms' Hh eq_refl).
+ intros [[] | [a Ha]]; cbn [effs ms']; rewrite Hchk.
* rewrite (errno_ret_in_intro _ _ ENOMEM_in_mmap_errnos). reflexivity.
* rewrite (grant_na_pin_not_errno md a nZ Hn0 Ha), Ha. cbn [andb]. rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
+ intros [r ws zs us cs ci] m' evs Hc. rewrite Hchk in Hc.
destruct ws; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
destruct (errno_ret_in mmap_errnos r) eqn:Er.
* destruct zs; [|discriminate]. injection Hc as <- <-.
destruct (proj1 (errno_ret_in_true _ _) Er) as (e & He & ->). rewrite (mmap_errnos_ENOMEM e He). exists (inl tt). repeat split; reflexivity.
* destruct (grant_ok_na_pin md r nZ) eqn:Hg; [|discriminate]. cbn [andb] in Hc.
destruct (listNN_eqb zs [(r, n)]) eqn:Hl; [|discriminate].
apply listNN_eqb_eq in Hl. subst zs. injection Hc as <- <-.
exists (inr (exist _ r Hg)). repeat split; reflexivity.
+ intros [r ws zs us cs ci] Hc. rewrite Hchk in Hc.
destruct ws; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
destruct (errno_ret_in mmap_errnos r); [destruct zs; discriminate|].
destruct (grant_ok_na_pin md r nZ && true && listNN_eqb zs [(r, n)])%bool; discriminate.
+ intros [[] | [a Ha]]; cbn [ms']; [exact Hh | rewrite with_mmap_backing_halted; unfold mmap_model; rewrite with_vmmaps_halted; exact Hh].
+ intros [[] | [a Ha]]; reflexivity.
- intros [[] | [a Ha]]; cbn [effs ms'].
+ exists md. split; [exact Hh|]. split; [apply same_io_refl|]. left. split; [reflexivity|]. split; [| reflexivity].
subst ms. rewrite RT. reflexivity.
+ exists (with_mmap_backing flags a n (mmap_model a n md)).
split; [rewrite with_mmap_backing_halted; unfold mmap_model; rewrite with_vmmaps_halted; exact Hh|].
split; [eapply same_io_trans; [apply same_io_with_vmmaps | apply same_io_with_mmap_backing]|].
right. split; [reflexivity|]. split; [exact Ha|]. split; [| reflexivity].
subst ms. rewrite ZF. reflexivity.
Qed.
End K.
End b.
