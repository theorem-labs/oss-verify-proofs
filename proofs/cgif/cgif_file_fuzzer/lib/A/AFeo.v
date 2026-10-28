(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0f YG0n.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AF0x.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section c.
Variable W : world tfibsegs.
Definition call_post (ms : machine_state) (md : Model) (D : Z -> Prop) : world tfibsegs -> config -> Prop :=
fun W' c' => W' = W /\ exists regs' mem' mat',
c' = mkCfg (mkst regs' (getr (ms_regs ms) 1) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat' md) /\
regs_preserved (ms_regs ms) regs' /\
(forall x : word, ~ D (bv_unsigned x) -> mem' x = ms_mem ms x) /\
(forall a, D a -> apresent (w_H W) mem' a).
Lemma subregion_trim_lo' : forall r lo, subregion (trim_lo r lo) r.
Proof. exact subregion_trim_lo. Qed.
Lemma call_stretch : forall (k : nat) (E : env) ss ms mat md rs (retpc : Z) (D : Z -> Prop) (Q : world tfibsegs -> config -> Prop),
st_ok tfibsegs E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_atoms_lt k ss = true ->
regions_wf rs = true -> no_cdata rs = true -> mem_atoms_lt k rs = true -> submem rs (ss_mem ss) ->
sr_get (ss_regs ss) 1 = SLit retpc -> 0 <= retpc < 2 ^ 64 ->
(forall r a, In r rs -> base_val E (YP09.r_base r) + YP09.r_lo r <= a < base_val E (YP09.r_base r) + YP09.r_hi r -> ~ D a /\ 0 <= a < 2 ^ 64) ->
(forall r, In r rs -> YP09.r_whi r <= YP09.r_wlo r \/ (YP09.r_lo r <= YP09.r_wlo r /\ YP09.r_whi r <= YP09.r_hi r)) ->
SRr tfibsegs W (mkCfg ms (with_vm_backing (m_vm_lazy md) mat md)) (call_post ms md D) ->
(forall regs' mem' mat',
st_ok tfibsegs (havoc E k (map (getr regs') CLOB)) (ss_after_call ss rs k retpc)
(restrict (w_H W) (mkst regs' (Z_to_bv 64 retpc) mem' (seg_rom tfibsegs))) ->
regs_preserved (ms_regs ms) regs' ->
(forall x : word, ~ D (bv_unsigned x) -> mem' x = ms_mem ms x) ->
(forall a, D a -> apresent (w_H W) mem' a) ->
SRr tfibsegs W (mkCfg (mkst regs' (Z_to_bv 64 retpc) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat' md)) Q) ->
SRr tfibsegs W (mkCfg ms (with_vm_backing (m_vm_lazy md) mat md)) Q.
Proof.
intros k E ss ms mat md rs retpc D Q HS Hrv Hat Hwf Hnc Hmat Hsub Hra Hrpc Hext Hwr HC HK.
apply (SRr_bind tfibsegs W _ (call_post ms md D) Q HC).
intros W' c' _ (-> & regs' & mem' & mat' & -> & HP & Hfr & Hpr).
assert (R1 : getr (ms_regs ms) 1 = Z_to_bv 64 retpc).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W) E ss ms 1 HS), Hra. reflexivity. }
rewrite R1. apply (HK regs' mem' mat'); [| exact HP | exact Hfr | exact Hpr].
rewrite restrict_mkst_fx.
apply (st_ok_after_call tfibsegs k E ss (restrict (w_H W) ms) regs' (mrestrict (w_H W) mem') rs retpc HS Hrv Hat Hwf Hnc Hmat Hsub Hra).
- cbn [ms_regs restrict]. exact HP.
- apply Forall_forall. intros r Hr. cbn [ms_mem restrict].
assert (PW : forall a, base_val E (YP09.r_base r) + YP09.r_lo r <= a < base_val E (YP09.r_base r) + YP09.r_hi r ->
mrestrict (w_H W) mem' (Z_to_bv 64 a) = mrestrict (w_H W) (ms_mem ms) (Z_to_bv 64 a)).
{ intros a Ha. destruct (Hext r a Hr Ha) as [HD Hu]. unfold mrestrict. destruct (w_H W (Z_to_bv 64 a)); [reflexivity|].
apply Hfr. rewrite unsigned_lit_small by exact Hu. exact HD. }
split.
+ intros a Ha. unfold mbyte. rewrite (PW a Ha). reflexivity.
+ intros a Ha Hw. destruct (Hwr r Hr) as [X|[X1 X2]]; [lia|].
unfold writable_at, wview in *. rewrite (PW a ltac:(lia)). exact Hw.
Qed.
End c.
End b.
