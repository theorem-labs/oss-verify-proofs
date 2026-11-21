(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import PropExec CatExec SeqExec StoreOk.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1 Require Import SymEx2Expr SymEx2 MemRel SymAux RomRead.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import ZIface InflateState.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6U Require Import Segs6u.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6S Require Import InflMem.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache.

Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.
Definition ROD6_LO : Z := 0x10000.
Definition ROD6_HI : Z := 0x2c3f8.
Definition rod6_clear (mem : word -> option byte) : Prop :=
  forall x : word, ROD6_LO <= bv_unsigned x < ROD6_HI -> mem x = None.

Definition A6_JTAB : Z := 0x12510.
Definition A6_ORDER : Z := 0x1258c.
Definition A6_LENFIX : Z := 0x126ae.
Definition A6_DISTFIX : Z := 0x12eae.
Definition A6_MOD31 : Z := 0x10688.

Definition arm6_pcs : list Z :=
  [0x1f088; 0x1f2c4; 0x1f238; 0x1f32c; 0x1f338; 0x20390; 0x2067c; 0x20790; 0x20884; 0x1f1d4; 0x1f484;
   0x1f4c0; 0x1f4d0; 0x1f24c; 0x1f5bc; 0x1f5c4; 0x1f350; 0x1f1b8; 0x1f8c0; 0x209cc; 0x209d4; 0x1f134;
   0x20cf0; 0x1f1c8; 0x21020; 0x1f0f4; 0x1f3b8; 0x204f8; 0x214c4; 0x214dc; 0x21650].
Definition jt6_entry (k : Z) : Z := nth (Z.to_nat k) arm6_pcs 0.
Definition arm6_pc (m : Z) : Z := jt6_entry (m - HEAD).
Definition jt6_off (k : Z) : Z := jt6_entry k - A6_JTAB.

Lemma jt6_chk : chk_rom s6u_segs A6_JTAB (ctab_byte jt6_off) (4 * 31) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma jt6_off_range : forall k, 0 <= k < 31 -> 0 <= jt6_off k < 2 ^ 31.
Proof.
  intros k Hk. unfold jt6_off, jt6_entry, A6_JTAB.
  assert (E : exists n, (n < 31)%nat /\ Z.to_nat k = n) by (exists (Z.to_nat k); split; [lia | reflexivity]).
  destruct E as (n & Hn & ->).
  do 31 (destruct n as [|n]; [cbn; lia|]). lia.
Qed.

Lemma jt6_cells : forall mem, rod6_clear mem -> cells s6u_segs mem A6_JTAB 4 4 31 jt6_off.
Proof.
  intros mem HM. apply (rom_code_cells s6u_segs A6_JTAB jt6_off 31 mem jt6_chk); [| unfold A6_JTAB; lia | unfold A6_JTAB; lia].
  intros x Hx. apply HM. unfold A6_JTAB, ROD6_LO, ROD6_HI in *. lia.
Qed.

Lemma jt6_read : forall mem k, rod6_clear mem -> 0 <= k < 31 ->
  exists bs, rdn s6u_segs mem (zw (A6_JTAB + 4 * k)) 4 = Some bs /\ bytes_le_to_Z bs = jt6_off k.
Proof.
  intros mem k HM Hk. pose proof (jt6_cells mem HM k Hk) as C. unfold cell in C.
  pose proof (jt6_off_range k Hk) as Hr.
  eexists. split; [exact C|]. rewrite bytes_le_Z_to_le by lia. apply Z.mod_small.
  change (8 * Z.of_nat 4) with 32. lia.
Qed.

Lemma order6_chk : chk_rom s6u_segs A6_ORDER (tab_byte order_a) (2 * 19) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma order6_u16 : tab_u16 order_a 19 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma order6_cells : forall mem, rod6_clear mem -> cells s6u_segs mem A6_ORDER 2 2 19 (arr_get order_a).
Proof.
  intros mem HM. apply (tab16_cells s6u_segs A6_ORDER order_a 19 mem order6_chk order6_u16); [| unfold A6_ORDER; lia | unfold A6_ORDER; lia].
  intros x Hx. apply HM. unfold A6_ORDER, ROD6_LO, ROD6_HI in *. lia.
Qed.

Lemma lenfix6_chk : chk_rom s6u_segs A6_LENFIX (ctab_byte (arr_get lenfix_a)) (4 * 512) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma distfix6_chk : chk_rom s6u_segs A6_DISTFIX (ctab_byte (arr_get distfix_a)) (4 * 32) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma lenfix6_cells : forall mem, rod6_clear mem -> cells s6u_segs mem A6_LENFIX 4 4 512 (arr_get lenfix_a).
Proof.
  intros mem HM. apply (rom_code_cells s6u_segs A6_LENFIX (arr_get lenfix_a) 512 mem lenfix6_chk); [| unfold A6_LENFIX; lia | unfold A6_LENFIX; lia].
  intros x Hx. apply HM. unfold A6_LENFIX, ROD6_LO, ROD6_HI in *. lia.
Qed.
Lemma distfix6_cells : forall mem, rod6_clear mem -> cells s6u_segs mem A6_DISTFIX 4 4 32 (arr_get distfix_a).
Proof.
  intros mem HM. apply (rom_code_cells s6u_segs A6_DISTFIX (arr_get distfix_a) 32 mem distfix6_chk); [| unfold A6_DISTFIX; lia | unfold A6_DISTFIX; lia].
  intros x Hx. apply HM. unfold A6_DISTFIX, ROD6_LO, ROD6_HI in *. lia.
Qed.

Definition MOD31_MAGIC : Z := 0x0842108421084211.
Lemma mod31_chk : chk_rom s6u_segs A6_MOD31 (tab64_byte (fun _ => MOD31_MAGIC)) (8 * 1) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma mod31_cell : forall mem, rod6_clear mem -> cell s6u_segs mem A6_MOD31 8 MOD31_MAGIC.
Proof.
  intros mem HM.
  pose proof (tab_cell8 s6u_segs mem A6_MOD31 (fun _ => MOD31_MAGIC) 1 0 mod31_chk) as C.
  rewrite Z.mul_0_r, Z.add_0_r in C. apply C; try (unfold A6_MOD31; lia).
  intros x Hx. apply HM. unfold A6_MOD31, ROD6_LO, ROD6_HI in *. lia.
Qed.
End FXG.
