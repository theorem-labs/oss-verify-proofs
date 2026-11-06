(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec StoreOk SumWalkTac RefMemcpyLib.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Mem Image.
From OSSVerify.Proofs.fast_float.from_chars.lib Require Import UbStartup UbStartupDefs UDrvData UDrvMain.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac bvlit := vm_compute; try (f_equal; repeat (apply (f_equal2 cons); [apply bv_eq; reflexivity|]); try reflexivity).

Section HI.
Variable sp0 : word.
Variables av ev : list (list byte).
Variables uid tid hw : word.
Variable rdraw : EntryDraw.
Variable regs : bvmap 5 word.
Variable mem : word -> option byte.
Hypothesis Hsp : valid_sp sp0.
Hypothesis ME : main_entry sp0 av ev uid tid hw rdraw regs mem.

(* [comment removed for export] *)
#[using="sp0 av ev uid tid hw rdraw regs Hsp ME"] Lemma hi_pristine : forall lo hi, 0 <= lo -> lo <= hi -> hi <= 0xa0000 -> miss_ok lo (Z.to_nat (hi - lo)) = true -> pristine mem lo hi.
Proof. LiaFast.lf_pins (fun (sp0 av ev uid tid hw rdraw regs Hsp ME : LiaFast.U) => LiaFast.u0).
  intros lo hi H0 H1 H2 Hm. split; [lia|]. split; [lia|]. intros i Hi. unfold wa.
  replace i with (lo + (i - lo)) by lia.
  apply (mem_miss sp0 av ev uid tid hw rdraw regs mem Hsp ME lo (Z.to_nat (hi - lo)) (i - lo)); [lia | rewrite Z2Nat.id by lia; lia | exact Hm | rewrite Z2Nat.id by lia; lia].
Qed.

#[using="sp0 av ev uid tid hw rdraw regs Hsp ME"] Lemma hi_rdn_img : forall lo hi (a : Z) (n : nat), 0 <= lo -> lo <= hi -> hi <= 0xa0000 -> miss_ok lo (Z.to_nat (hi - lo)) = true ->
  lo <= a -> a + Z.of_nat n <= hi -> rdn PSEGS mem (wa a) n = rdn PSEGS (fun _ => None) (wa a) n.
Proof. LiaFast.lf_pins (fun (sp0 av ev uid tid hw rdraw regs Hsp ME : LiaFast.U) => LiaFast.u0).
  intros lo hi a n H0 H1 H2 Hm Ha Hn. destruct (hi_pristine lo hi H0 H1 H2 Hm) as (_ & _ & HP).
  apply (rdn_img PSEGS mem a n lo hi); [| lia | lia | lia | lia]. intros i Hi. exact (HP i Hi).
Qed.

(* [comment removed for export] *)
#[using="sp0 av ev uid tid hw rdraw regs Hsp ME"] Lemma hi_kro : pristine mem 0x18288 0x182a8 /\ pristine mem 0x182a8 0x18327.
Proof. LiaFast.lf_pins (fun (sp0 av ev uid tid hw rdraw regs Hsp ME : LiaFast.U) => LiaFast.u0). split; apply hi_pristine; first [lia | vm_compute; reflexivity]. Qed.
#[using="sp0 av ev uid tid hw rdraw regs Hsp ME"] Lemma hi_tables : forall a n, (0x18288 <= a /\ a + Z.of_nat n <= 0x182a8) \/ (0x182a8 <= a /\ a + Z.of_nat n <= 0x18327) ->
  rdn PSEGS mem (wa a) n = rdn PSEGS (fun _ => None) (wa a) n.
Proof. LiaFast.lf_pins (fun (sp0 av ev uid tid hw rdraw regs Hsp ME : LiaFast.U) => LiaFast.u0).
  intros a n [[A B]|[A B]].
  - apply (hi_rdn_img 0x18288 0x182a8); first [lia | vm_compute; reflexivity].
  - apply (hi_rdn_img 0x182a8 0x18327); first [lia | vm_compute; reflexivity].
Qed.

(* [comment removed for export] *)
#[using="sp0 av ev uid tid hw rdraw regs Hsp ME"] Lemma hi_need_locks : rdn PSEGS mem (wa 621603) 1 = Some (word_to_le_bytes 1 (wa 0)).
Proof. LiaFast.lf_pins (fun (sp0 av ev uid tid hw rdraw regs Hsp ME : LiaFast.U) => LiaFast.u0). rewrite (hi_rdn_img 621603 621604) by first [lia | vm_compute; reflexivity]. bvlit. Qed.
(* [comment removed for export] *)
#[using="sp0 av ev uid tid hw rdraw regs Hsp ME"] Lemma hi_got_guard : rdn PSEGS mem (wa 416600) 8 = Some (word_to_le_bytes 8 (wa 0x97c00)).
Proof. LiaFast.lf_pins (fun (sp0 av ev uid tid hw rdraw regs Hsp ME : LiaFast.U) => LiaFast.u0). rewrite (hi_rdn_img 416600 416608) by first [lia | vm_compute; reflexivity]. bvlit. Qed.
(* [comment removed for export] *)
#[using="sp0 av ev uid tid hw rdraw regs Hsp ME"] Lemma hi_lock : rdn PSEGS mem (wa 621712) 4 = Some (word_to_le_bytes 4 (wa 0)).
Proof. LiaFast.lf_pins (fun (sp0 av ev uid tid hw rdraw regs Hsp ME : LiaFast.U) => LiaFast.u0). rewrite (hi_rdn_img 621712 621716) by first [lia | vm_compute; reflexivity]. bvlit. Qed.
(* [comment removed for export] *)
#[using="sp0 av ev uid tid hw regs Hsp ME"] Lemma hi_canary : rdn PSEGS mem (wa 621568) 8 = Some (word_to_le_bytes 8 (wa (bv_unsigned (canary rdraw)))).
Proof. LiaFast.lf_pins (fun (sp0 av ev uid tid hw regs Hsp ME : LiaFast.U) => LiaFast.u0).
  change (wa 621568) with (Z_to_bv 64 0x97c00). rewrite (rdn_guard sp0 av ev uid tid hw rdraw regs mem Hsp ME). f_equal.
  unfold wa. rewrite Z_to_bv_bv_unsigned. unfold word_to_le_bytes. rewrite <- (canary_val rdraw).
  assert (HL : length (canary_bytes rdraw) = 8%nat) by reflexivity.
  rewrite <- HL at 1. symmetry. apply Z_to_le_bytes_lez.
Qed.
#[using="Type"] Lemma hi_can_range : 0 <= bv_unsigned (canary rdraw) <= 2 ^ 64 - 1.
Proof. LiaFast.lf_pins LiaFast.u0. pose proof (bv_unsigned_in_range _ (canary rdraw)) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 64) with (2 ^ 64) in R. lia. Qed.

(* [comment removed for export] *)
#[using="sp0 av ev uid tid hw rdraw regs Hsp ME"] Lemma hi_errno_pristine : pristine mem 0x778ec 0x778f0.
Proof. LiaFast.lf_pins (fun (sp0 av ev uid tid hw rdraw regs Hsp ME : LiaFast.U) => LiaFast.u0). apply hi_pristine; first [lia | vm_compute; reflexivity]. Qed.
#[using="sp0 av ev uid tid hw rdraw regs Hsp ME"] Lemma hi_errno_rd : forall j, 0 <= j < 4 -> exists b, mrd PSEGS mem (wa (0x778ec + j)) = Some b.
Proof. LiaFast.lf_pins (fun (sp0 av ev uid tid hw rdraw regs Hsp ME : LiaFast.U) => LiaFast.u0).
  intros j Hj. destruct hi_errno_pristine as (_ & _ & HP). unfold mrd. rewrite (HP (0x778ec + j)) by lia.
  assert (Hc : forallb (fun j => match seg_rom PSEGS (wa (0x778ec + Z.of_nat j)) with Some _ => true | None => false end) (seq 0 4) = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in Hc. specialize (Hc (Z.to_nat j) ltac:(apply in_seq; lia)). rewrite Z2Nat.id in Hc by lia.
  destruct (seg_rom PSEGS (wa (0x778ec + j))) as [b|]; [exists b; reflexivity | discriminate].
Qed.

(* [comment removed for export] *)
#[using="sp0 av ev uid tid hw rdraw regs Hsp ME"] Lemma hi_ctx : pristine mem 0x97c98 0x98038.
Proof. LiaFast.lf_pins (fun (sp0 av ev uid tid hw rdraw regs Hsp ME : LiaFast.U) => LiaFast.u0). apply hi_pristine; first [lia | vm_compute; reflexivity]. Qed.
End HI.
