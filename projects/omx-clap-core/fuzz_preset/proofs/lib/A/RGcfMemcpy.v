(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-29: copied from proofs/omx-clap-core/fuzz_state/lib/A/FSRealloc_inst.v:293-369 (hub ddc081c1a03, blob c7cb9a4b423e) fs_amemcpy_realizes, ported to omx-clap-core/fuzz_preset's asan image A (musl memcpy 0x9b2b4 = cf_pc_memcpy of CfImg_A, A/AE3c.v tfib_memcpy, A/AE2y.v) and restated as YGcfReallocCompose.wrap_realloc_walk_cf's field rw_memcpy; the overlay normal form conjunct (at_mem_cf) added. *)
(* Modified by Theorem Labs, 2026-10-31: field round 3 part 3c (the record's rw_memcpy no longer states the overlay
   normal form): the at_mem_cf conjunct and its proof (MN2) removed. *)
(* Theorem Labs, 2026-10: fuzz_preset.asan image A, row A5 of the internal file FREE-PIECES-102.md: the copy routine REAL(memcpy) (musl
   memcpy 0x9b2b4, Reallocate's `jalr a3` target through the RELRO cell 0xa2038 -> 0xa3e88): rw_memcpy_A is
   YGcfReallocCompose.wrap_realloc_walk_cf's field rw_memcpy at segs := tfibsegs, ci := CfImg_A: ReallocG.amemcpy_realizes
   at cf_pc_memcpy. The run is A/AE3c.v's tfib_memcpy on the visible memory (the destination is writable, so not
   hidden: AE2y.hidden_not_writable; the source bytes from AE2y.rdn_of_vis), lifted to SRr by YA0n.SRr_msteps. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YP09 YP03.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ReallocG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfMallocCompose.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB1w CfImgA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AF0x AE2y AE3c.
From Stdlib Require Import List.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Existing Instance CfImg_A.

Theorem rw_memcpy_A : forall (W : world tfibsegs) regs mem md d s n,
  ReallocG.rmemcpy_pre tfibsegs W regs mem d s n ->
  SRr tfibsegs W (cfg_at tfibsegs cf_pc_memcpy regs mem md)
  (fun W' c' => W' = W /\ exists regs' mem' md',
    c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
    (forall i, 0 <= i < n -> aview tfibsegs (w_H W) mem' (d + i) = aview tfibsegs (w_H W) mem (s + i)) /\
    (forall x : word, ~ (d <= bv_unsigned x < d + n) -> mem' x = mem x) /\
    (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
Proof.
intros W regs mem md d x n (RA & G10 & G11 & G12 & Hn0 & Hd0 & Hdn & Hx0 & Hxn & HDISJ & HWR & HRD).
set (H := w_H W) in *.
assert (Hnb : n < 2 ^ 64) by lia.
assert (DW : forall a, d <= a < d + n -> H (Z_to_bv 64 a) = false).
{ intros a Ha. destruct (H (Z_to_bv 64 a)) eqn:Hh; [|reflexivity]. exfalso.
  exact (AE2y.hidden_not_writable W mem a ltac:(lia) Hh (HWR a Ha)). }
destruct (AE2y.rdn_of_vis (mrestrict H mem) x (Z.to_nat n) Hx0 ltac:(lia)) as (bs & RDN & LEN & BS).
{ intros i Hi. apply (proj1 (AF0x.aview_vis H mem (x + i))). apply HRD. lia. }
assert (LENZ : Z.of_nat (length bs) = n) by lia.
assert (WD : bv_unsigned (w64 d) + n <= 2 ^ 64 /\ (0 < n -> bv_unsigned (w64 d) = d)).
{ destruct (Z.eq_dec n 0) as [N0|N0]; [pose proof (u64_range (w64 d)); split; lia|].
  unfold w64. rewrite unsigned_lit_small by lia. split; lia. }
assert (WX : bv_unsigned (w64 x) + n <= 2 ^ 64 /\ (0 < n -> bv_unsigned (w64 x) = x)).
{ destruct (Z.eq_dec n 0) as [N0|N0]; [pose proof (u64_range (w64 x)); split; lia|].
  unfold w64. rewrite unsigned_lit_small by lia. split; lia. }
assert (WDISJ : bv_unsigned (w64 d) + Z.of_nat (length bs) <= bv_unsigned (w64 x) \/
                bv_unsigned (w64 x) + Z.of_nat (length bs) <= bv_unsigned (w64 d)).
{ rewrite LENZ. destruct (Z.eq_dec n 0) as [N0|N0]; [subst n; lia|].
  rewrite (proj2 WD), (proj2 WX) by lia. exact HDISJ. }
assert (SOK : store_ok tfibsegs (mrestrict H mem) (w64 d) (length bs) = true).
{ apply store_ok_of_all; [rewrite LENZ; exact (proj1 WD)|].
  intros z Hz. rewrite LENZ in Hz. destruct (Z.eq_dec n 0) as [N0|N0]; [lia|].
  rewrite (proj2 WD) in Hz by lia.
  pose proof (HWR (bv_unsigned z) ltac:(lia)) as Wz. unfold writable_at in Wz. rewrite Z_to_bv_bv_unsigned in Wz. exact Wz. }
destruct (AE3c.tfib_memcpy bs (w64 d) (w64 x) (w64 n) (mrestrict H mem) (seg_rom tfibsegs) regs G10 G11 G12
  ltac:(unfold w64; rewrite unsigned_lit_small by lia; lia) ltac:(rewrite LEN; exact RDN) SOK
  ltac:(rewrite LENZ; exact (proj1 WD)) ltac:(rewrite LENZ; exact (proj1 WX)) WDISJ)
  as (regs2 & Hms & _ & Hkeep).
set (mem2 := munrestrict H mem (wbytes (mrestrict H mem) (w64 d) bs)).
assert (M2out : forall z : word, ~ (d <= bv_unsigned z < d + n) -> mem2 z = mem z).
{ intros z Hz. unfold mem2, munrestrict. destruct (H z) eqn:Hh; [reflexivity|].
  destruct (Z.eq_dec n 0) as [N0|N0].
  - assert (E0 : bs = []) by (destruct bs; [reflexivity | cbn in LENZ; lia]). subst bs. cbn [wbytes].
    unfold mrestrict. rewrite Hh. reflexivity.
  - pose proof (proj2 WD ltac:(lia)) as Ed. pose proof (u64_range z).
    destruct (Z_lt_le_dec (bv_unsigned z) d) as [L|L].
    + rewrite wbytes_below; [unfold mrestrict; rewrite Hh; reflexivity | rewrite LENZ; exact (proj1 WD) | lia].
    + rewrite wbytes_above; [unfold mrestrict; rewrite Hh; reflexivity | rewrite LENZ; lia]. }
assert (M2in : forall z : word, d <= bv_unsigned z < d + n -> mem2 z = Some (nth (Z.to_nat (bv_unsigned z - d)) bs 0%bv)).
{ intros z Hz. pose proof (proj2 WD ltac:(lia)) as Ed. unfold mem2, munrestrict.
  rewrite <- (Z_to_bv_bv_unsigned 64 z), (DW (bv_unsigned z) Hz), Z_to_bv_bv_unsigned.
  rewrite (AE2y.wbytes_inside bs (mrestrict H mem) (w64 d) z); rewrite ?LENZ, ?Ed; [|lia | lia].
  apply nth_error_nth'. lia. }
unfold cfg_at.
eapply (SRr_msteps tfibsegs AF0x.Hwx_tfa W); [rewrite restrict_mkst_fx; exact Hms|].
intros model' Hsbm _. apply SRr_ret.
split; [reflexivity|].
exists regs2, mem2, model'.
split.
{ replace (w64 (raZ regs)) with (v_jalr (getr regs 1) 0) by (rewrite RA; unfold raZ, w64; rewrite Z_to_bv_bv_unsigned; reflexivity).
  reflexivity. }
split.
{ intros r Hr. unfold acallee_saved in Hr.
  assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
               r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  destruct Hc as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
  apply Hkeep; intros E; apply (f_equal (@bv_unsigned 5)) in E; vm_compute in E; discriminate E. }
split; [exact Hsbm|].
split.
{ intros i Hi. unfold aview.
  assert (Ed : bv_unsigned (w64 d) = d) by exact (proj2 WD ltac:(lia)).
  replace (mbyte tfibsegs (mrestrict H mem2) (d + i)) with (Some (nth (Z.to_nat i) bs 0%bv)).
  2:{ unfold mbyte, mrestrict. rewrite (DW (d + i) ltac:(lia)).
      rewrite (M2in (Z_to_bv 64 (d + i))); rewrite unsigned_lit_small by lia; [|lia].
      replace (Z.to_nat (d + i - d)) with (Z.to_nat i) by lia. reflexivity. }
  replace (x + i) with (x + Z.of_nat (Z.to_nat i)) by lia. rewrite (BS (Z.to_nat i) ltac:(lia)). reflexivity. }
split; [exact M2out|].
intros a (Hh & b & Hb). split; [exact Hh|].
destruct (Z_lt_le_dec (bv_unsigned (Z_to_bv 64 a)) d) as [L1|L1];
[|destruct (Z_lt_le_dec (bv_unsigned (Z_to_bv 64 a)) (d + n)) as [L2|L2]].
- exists b. rewrite M2out by lia. exact Hb.
- eexists. apply M2in. lia.
- exists b. rewrite M2out by lia. exact Hb.
Qed.
End a.
