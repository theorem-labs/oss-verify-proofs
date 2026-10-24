(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0n YK11 YK0i YK0h YK14.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations.
Open Scope bv_scope.
Section c.
Context {fx : FPState}.
Lemma v_lui_4096 : v_lui 4096 = Z_to_bv 64 4096.
Proof. reflexivity. Qed.
Lemma c_lts_0_0 : c_lts (Z_to_bv 64 0) (Z_to_bv 64 0) = false.
Proof. reflexivity. Qed.
Lemma write_to_mem_below : forall data mem (buf a : word),
(bv_unsigned buf + Z.of_nat (length data) <= 2^64)%Z ->
(bv_unsigned a < bv_unsigned buf)%Z ->
write_to_mem mem buf data a = mem a.
Proof.
intros data mem buf a Hnw Ha.
rewrite write_to_mem_wbytes. apply wbytes_below; assumption.
Qed.
Lemma write_to_mem_above : forall data mem (buf a : word),
(bv_unsigned buf + Z.of_nat (length data) <= bv_unsigned a)%Z ->
write_to_mem mem buf data a = mem a.
Proof.
intros data mem buf a Ha.
rewrite write_to_mem_wbytes. apply wbytes_above; assumption.
Qed.
Lemma rdn_wtm_out : forall segs data m (buf a : word) n,
(bv_unsigned a + Z.of_nat n <= 2^64)%Z ->
(bv_unsigned buf + Z.of_nat (length data) <= 2^64)%Z ->
((bv_unsigned buf + Z.of_nat (length data) <= bv_unsigned a)%Z \/
(bv_unsigned a + Z.of_nat n <= bv_unsigned buf)%Z) ->
rdn segs (write_to_mem m buf data) a n = rdn segs m a n.
Proof.
intros segs data m buf a n Hna Hnb Hd. apply rdn_ext; [exact Hna|].
intros x Hx. destruct Hd as [Hd | Hd].
- apply write_to_mem_above. lia.
- apply write_to_mem_below; [exact Hnb | lia].
Qed.
Lemma rdn_write_to_mem : forall segs data mem (buf : word),
(bv_unsigned buf + Z.of_nat (length data) <= 2^64)%Z ->
rdn segs (write_to_mem mem buf data) buf (length data) = Some data.
Proof.
intros segs data mem buf Hnw.
rewrite write_to_mem_wbytes. apply rdn_wbytes_hit. exact Hnw.
Qed.
Lemma adv_apply_write : forall regs pc sv mem rom ret buf data,
advance_past_svc (apply_effect
{| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc; ms_svc_pending := sv; ms_resv := None; ms_fcsr := fp_csr;
ms_mem := mem; ms_rom := rom |}
(mkEffect ret [(buf, data)] []))
= mkst (regupd regs 10 ret) (v_addi pc 4) (write_to_mem mem buf data) rom.
Proof.
intros regs pc sv mem rom ret buf data.
unfold advance_past_svc, apply_effect, RiscvSemantics.set_reg, ms_pc.
rewrite bv_eqb_neq by (intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate).
cbv beta iota zeta.
cbn [ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom
eff_ret eff_writes eff_zeros eff_unmaps eff_copies apply_copies
apply_zeros apply_unmaps apply_writes].
unfold mkst, regupd.
rewrite b_npc4. reflexivity.
Qed.
Lemma adv_apply_delivered : forall regs pc sv mem rom ret buf data,
advance_past_svc (apply_effect
{| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc; ms_svc_pending := sv; ms_resv := None; ms_fcsr := fp_csr;
ms_mem := mem; ms_rom := rom |}
(mkEffect ret (delivered_writes buf data) []))
= mkst (regupd regs 10 ret) (v_addi pc 4) (write_to_mem mem buf data) rom.
Proof.
intros regs pc sv mem rom ret buf data.
destruct data as [|b rest]; [|apply adv_apply_write].
unfold advance_past_svc, apply_effect, RiscvSemantics.set_reg, ms_pc.
rewrite bv_eqb_neq by (intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate).
cbv beta iota zeta.
cbn [ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom
eff_ret eff_writes eff_zeros eff_unmaps eff_copies apply_copies
apply_zeros apply_unmaps apply_writes
delivered_writes write_to_mem].
unfold mkst, regupd.
rewrite b_npc4. reflexivity.
Qed.
End c.
