(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s YP0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YQ0g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YA0n YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG0h YG0u.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF8r.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section c. Context {imgk : img}.
Variable W : world tfxsegs.
Definition call_post (ms : machine_state) (md : Model) (D : Z -> Prop) : world tfxsegs -> config -> Prop :=
fun W' c' => W' = W /\ exists regs' mem' mat',
c' = mkCfg (mkst regs' (getr (ms_regs ms) 1) mem' (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md) mat' md) /\
regs_preserved (ms_regs ms) regs' /\
(forall x : word, ~ D (bv_unsigned x) -> mem' x = ms_mem ms x) /\
(forall a, D a -> apresent (w_H W) mem' a).

Lemma call_stretch : forall (k : nat) (E : env) ss ms mat md rs (retpc : Z) (D : Z -> Prop) (Q : world tfxsegs -> config -> Prop),
st_ok tfxsegs E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_atoms_lt k ss = true ->
regions_wf rs = true -> no_cdata rs = true -> mem_atoms_lt k rs = true -> submem rs (ss_mem ss) ->
sr_get (ss_regs ss) 1 = SLit retpc -> 0 <= retpc < 2 ^ 64 ->
(forall r a, In r rs -> base_val E (YQ0b.r_base r) + YQ0b.r_lo r <= a < base_val E (YQ0b.r_base r) + YQ0b.r_hi r -> ~ D a /\ 0 <= a < 2 ^ 64) ->
(forall r, In r rs -> YQ0b.r_whi r <= YQ0b.r_wlo r \/ (YQ0b.r_lo r <= YQ0b.r_wlo r /\ YQ0b.r_whi r <= YQ0b.r_hi r)) ->
SRr tfxsegs W (mkCfg ms (with_vm_backing (m_vm_lazy md) mat md)) (call_post ms md D) ->
(forall regs' mem' mat',
st_ok tfxsegs (havoc E k (map (getr regs') CLOB)) (ss_after_call ss rs k retpc)
(restrict (w_H W) (mkst regs' (Z_to_bv 64 retpc) mem' (seg_rom tfxsegs))) ->
regs_preserved (ms_regs ms) regs' ->
(forall x : word, ~ D (bv_unsigned x) -> mem' x = ms_mem ms x) ->
(forall a, D a -> apresent (w_H W) mem' a) ->
SRr tfxsegs W (mkCfg (mkst regs' (Z_to_bv 64 retpc) mem' (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md) mat' md)) Q) ->
SRr tfxsegs W (mkCfg ms (with_vm_backing (m_vm_lazy md) mat md)) Q.
Proof.
intros k E ss ms mat md rs retpc D Q HS Hrv Hat Hwf Hnc Hmat Hsub Hra Hrpc Hext Hwr HC HK.
img_apply (SRr_bind tfxsegs W _ (call_post ms md D) Q HC).
intros W' c' _ (-> & regs' & mem' & mat' & -> & HP & Hfr & Hpr).
assert (R1 : getr (ms_regs ms) 1 = Z_to_bv 64 retpc).
{ rewrite (st_ok_restrict_reg tfxsegs (w_H W) E ss ms 1 HS), Hra. img_refl. }
rewrite R1. img_apply (HK regs' mem' mat'); [| img_try (img_exact HP) | img_try (img_exact Hfr) | img_try (img_exact Hpr)].
rewrite restrict_mkst_fx.
img_apply (st_ok_after_call tfxsegs k E ss (restrict (w_H W) ms) regs' (mrestrict (w_H W) mem') rs retpc HS Hrv Hat Hwf Hnc Hmat Hsub Hra).
- cbn [ms_regs restrict]. img_exact HP.
- img_apply Forall_forall. intros r Hr. cbn [ms_mem restrict].
assert (PW : forall a, base_val E (YQ0b.r_base r) + YQ0b.r_lo r <= a < base_val E (YQ0b.r_base r) + YQ0b.r_hi r ->
mrestrict (w_H W) mem' (Z_to_bv 64 a) = mrestrict (w_H W) (ms_mem ms) (Z_to_bv 64 a)).
{ intros a Ha. destruct (Hext r a Hr Ha) as [HD Hu]. unfold mrestrict. destruct (w_H W (Z_to_bv 64 a)); [img_refl|].
img_apply Hfr. rewrite unsigned_lit_small by img_exact Hu. img_exact HD. }
split.
+ intros a Ha. unfold mbyte. rewrite (PW a Ha). img_refl.
+ intros a Ha Hw. destruct (Hwr r Hr) as [X|[X1 X2]]; [img_lia|].
unfold writable_at, wview in *. rewrite (PW a ltac:(img_lia)). img_exact Hw.
Qed.
End c.
End b.
