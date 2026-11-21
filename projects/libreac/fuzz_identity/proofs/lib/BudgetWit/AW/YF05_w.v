(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from projects/cgif/cgif_file_fuzzer/proofs/lib/YF05.v (donor image sha256 7093581aab04), with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from Reusable/YF05.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
(* Theorem Labs, 2026-11: cut for the usage path at 16 GiB: the pruning removed declarations that this path does not use; some unused declarations can remain. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (changed anon_node). *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK16 YK0n YK11 YK0h YK0i YK14 YK1c YK0v YK02 YK0p YK15.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import YK18_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK0y YK1b YK00 YK01 YK13 YP0n YK04.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import YK05_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YA0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import YA0n_w YA05_w YA09_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK0g.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import YA08_w YG0b_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0f.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import YG0n_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import RomBase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
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
(exists a, grant_ok_na_pin (Z_to_bv 64 0) md a nZ = true) -> mmap_noreserve_backed_ok flags md nZ = true ->
exists (I : Type) (nx : I -> config) (bit : I -> Z) (ga : I -> word) (i0 : I),
(node_ok segs (mkCfg (pend_at regs pc mem rom) md) I (fun _ => []) nx /\ bnode_ok segs (mkCfg (pend_at regs pc mem rom) md)) /\
bit i0 = 1 /\
forall i, exists md_i,
m_halted md_i = None /\ same_io md md_i /\
bit i = 1 /\ grant_ok_na_pin (Z_to_bv 64 0) md (ga i) nZ = true /\
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
(* #146: [mmap_rw_check] gained the decline premise, in position 9, after G5 and
before the [let nZ].  This trace pins a0 to the literal 0 (H10), and a NULL hint
fails [place_declined_b]'s first conjunct.  Qualified because this file reaches
[YK0v] transitively rather than by its own Require, as it already does for
[YA09_w.node_chk_grant_mat] below. *)
pose proof (fun eff => mmap_rw_check segs ms (getr regs 17) md eff flags Hno Hne1 G2 G3 Hcore G4 G5
ltac:(unfold ms; rewrite pend_gpr0, H10; apply YK0v.place_declined_b_null)) as Hchk.
cbv zeta in Hchk. rewrite Hl1 in Hchk. fold nZ n in Hchk. rewrite Hb0 in Hchk.
(* mmap_rw_check states the hint as the call's addr register; H10 is this trace
   writing NULL into a0, so fold it here. *)
assert (H0' : ms_gpr ms 0 = Z_to_bv 64 0) by (unfold ms; rewrite pend_gpr0; exact H10).
rewrite H0' in Hchk.
pose proof (page_round_up_Z_bounds len ltac:(lia)) as PB. unfold page_size in PB.
assert (HnP : (0 < nZ)%Z) by (unfold nZ in *; lia).
assert (HnAl : (nZ mod page_size = 0)%Z) by (unfold nZ; apply page_round_up_Z_mod).
pose (IB := {a : word | grant_ok_na_pin (Z_to_bv 64 0) md a nZ = true}).
pose (effs := fun i : IB => match i with exist _ a _ => mkEffectU a [] [(a, n)] [] [] [] end).
pose (ms' := fun i : IB => match i with exist _ a _ => with_mmap_backing flags a n (mmap_model a n md) end).
exists IB, (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)),
(fun _ => 1), (fun i => match i with exist _ a _ => a end), (exist _ a0 Ha0).
split; [| split; [reflexivity |]].
- (* Theorem Labs, 2026-11: with the node's budget obligation (YA09_w.node_chk_grant_bmat), from its grant outcome. *)
apply (YA09_w.node_chk_grant_bmat segs ms md (getr regs 17) IB (exist _ a0 Ha0) effs ms' _ Hh eq_refl
ltac:(rewrite Hno; right; left; reflexivity)
(YA09_w.off222 segs ms _ Hno) (YA09_w.rb222 segs ms _ md Hno)
(sys_rob_memfree segs ms md (getr regs 17) eq_refl ltac:(rewrite Hno; exact memfree_222))).
+ intros [a Ha]; cbn [effs ms']; rewrite Hchk.
rewrite (YA09_w.grant_na_pin_not_errno (Z_to_bv 64 0) md a nZ HnP HnAl Ha), Ha. cbn [andb]. rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
+ intros [a Ha]. cbn [effs eff_ret]. exact (YA09_w.grant_na_pin_not_errno (Z_to_bv 64 0) md a nZ HnP HnAl Ha).
+ intros [r ws zs us cs ci] m' evs Hc Her. cbn [eff_ret] in Her. rewrite Hchk in Hc.
destruct ws; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
rewrite Her in Hc.
destruct (grant_ok_na_pin (Z_to_bv 64 0) md r nZ) eqn:Hg; [|discriminate]. cbn [andb] in Hc.
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
