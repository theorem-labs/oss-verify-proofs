(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from PHeapInst.v (ported there to the binaries of release 2026.10.0 and LPS 2afba80c): its type table TYPS and lemmas split out to bound the build's memory. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require PropExec StoreOk CatExec StepTac.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require RefLayout.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require RefLayout MemSplit RefMemcpyLib FxLin FxMem.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.PropExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.StoreOk OSSVerify.Proofs.fast_float.from_chars.lib.Common.CatExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.StepTac OSSVerify.Proofs.fast_float.from_chars.lib.Common.RefLayout.ArgvEnv OSSVerify.Proofs.fast_float.from_chars.lib.Common.RefLayout OSSVerify.Proofs.fast_float.from_chars.lib.Common.MemSplit OSSVerify.Proofs.fast_float.from_chars.lib.Common.RefMemcpyLib OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Mem Image.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Frame.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require Import HIface HIfaceInit.
From OSSVerify.Proofs.fast_float.from_chars.lib Require Import RefStartup RefStartupDefs PDrvData PDrvMain PHeapInit PHeapIGlue.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require Import MallocModel MallocInv.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfKf.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxMalloc MngRepr MngL4 MngL4I.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require MngRz2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Notation ioutside := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.outside.
Open Scope Z_scope.

Local Ltac bvlit := vm_compute; try (f_equal; repeat (apply (f_equal2 cons); [apply bv_eq; reflexivity|]); try reflexivity).

(* LPS 08b1429: the auxv the kernel writes is StackLayout.auxv_entries', not the
   ten-entry table this file used to assume.  Twenty-six types, in the model's own
   order (StackLayout.v:auxv_entries at 75d69e00), and two more when the kernel
   declares rseq; AT_NULL terminates the table, so [MngL4.init_env] finds it at
   AUXV + 16 * length TYPS and the length is NOT a constant any more. *)
Definition TYPS (rseq : bool) : list Z :=
  [33; 40; 41; 42; 43; 44; 45; 46; 47; 51; 16; 6; 17; 3; 4; 5; 7; 8; 9; 11; 12; 13; 14; 23; 25; 31]
  ++ (if rseq then [27; 28] else []).

Lemma TYPS_len : forall r, Z.of_nat (length (TYPS r)) = Z.of_nat (auxv_count r) - 1.
Proof. intros [|]; reflexivity. Qed.

(* MEASURED CURE, 2026-11-07.  [TYPS_pos] below is the single sentence
   that cost 64 GiB.  Named by measuring nine one-sentence twins of
   this file each carrying its header line for line: the header alone (D0), [bview_none]
   (D5), [wview_none] (D6) and [tot_firstn2] (D7) all compiled inside a minute at 2.67 GiB,
   [TYPS_rnd] (D3) compiled green at 2.0 GiB in-process,
   and only this sentence ran away -- monotonically to 9.93 GiB on one core with no error
   and no frontier, the runaway signature.  Its twin in UHeapInst.v is byte-identical and
   is why the P and U builds
   died at the same 64.00 GiB cap inside two
   differently-named targets.
   THE SHAPE: `repeat (destruct i as [|i]; [cbn [nth app]; lia|]); lia` calls [lia] once
   per element and once more at the end -- and [lia] is not Stdlib's here.  This file
   Requires two global rebindings of it (Common/Lib/LiaTuning.v:188 and
   Common/PropExec.v:49), both CONTEXT-READING TIER BATTERIES, and every call runs over a
   context that grows one [S] per iteration.  The list is decided data, so the whole
   question is one closed boolean: [forallb] over [TYPS r], run ONCE on the VM at [Qed]
   via [vm_cast_no_check], the same cure PHeapImgCtx.v measured for [ctx_img_zero] and
   PHeapImgTab.v for [tables_img_ok].
   [TYPS_pos]'s STATEMENT below is unchanged to the character; only its proof differs, and
   [TYPS_pos_b] states the same bounds as the boolean the proof transfers. *)
Lemma TYPS_pos_b : forall r, forallb (fun z => (1 <=? z) && (z <=? 2 ^ 64 - 1))%bool (TYPS r) = true.
Proof. intros [|]; vm_cast_no_check (eq_refl true). Qed.

Lemma TYPS_pos : forall r i, (i < length (TYPS r))%nat -> 1 <= nth i (TYPS r) 0 <= 2 ^ 64 - 1.
Proof.
  intros r i Hi.
  assert (Hin : In (nth i (TYPS r) 0) (TYPS r)) by (apply nth_In; exact Hi).
  pose proof (proj1 (forallb_forall _ _) (TYPS_pos_b r) _ Hin) as Hb.
  apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  split; [exact H1 | exact H2].
Qed.

Lemma TYPS_rnd : forall r, In 25 (TYPS r).
Proof. intros r. unfold TYPS. destruct r; cbn [app]; repeat (first [apply in_eq | apply in_cons]). Qed.

(* 25 (AT_RANDOM) occurs once, at index 24 in either table. *)
(* MEASURED CURE, 2026-11-07.  TYPS_rnd_idx carries the IDENTICAL
   non-termination bug TYPS_pos did, and the first build of the
   cured PHeapTyps.vo hung on it after TYPS_pos passed: `repeat (destruct i as [|i];
   [ ... first [reflexivity | discriminate Hc] |])` has no fixed point, because past the
   end of TYPS the hypothesis is `nth i [] 0 = 25`, i.e. `0 = 25`, which `discriminate`
   closes -- so the bracket succeeds on the out-of-range branch too and `repeat` peels S
   forever, never reaching the trailing `lia`.  Same class, same cure: one closed boolean
   over the concrete list, decided once on the VM.
   The statement below is unchanged to the character; TYPS_rnd_idx_b is an added helper. *)
Lemma TYPS_rnd_idx_b : forall r,
  forallb (fun i => implb (Z.eqb (nth i (TYPS r) 0) 25) (Nat.eqb i 24)) (seq 0 (length (TYPS r))) = true.
Proof. intros [|]; vm_cast_no_check (eq_refl true). Qed.

Lemma TYPS_rnd_idx : forall r i, nth i (TYPS r) 0 = 25 -> (i < length (TYPS r))%nat -> i = 24%nat.
Proof.
  intros r i Hnth Hi.
  assert (Hin : In i (seq 0 (length (TYPS r)))) by
    (apply in_seq; split; [apply Nat.le_0_l | rewrite Nat.add_0_l; exact Hi]).
  pose proof (proj1 (forallb_forall _ _) (TYPS_rnd_idx_b r) i Hin) as Hb.
  cbv beta in Hb.
  rewrite Hnth, Z.eqb_refl in Hb. cbn [implb] in Hb.
  apply Nat.eqb_eq. exact Hb.
Qed.

(* [comment removed for export] *)
Lemma bview_none : forall m x, m (wa x) = None -> bview PSEGS m x = bview PSEGS (fun _ => None) x.
Proof. intros m x H. unfold bview, RiscvSemantics.wview. cbn [RiscvSemantics.ov_read_bytes]. rewrite H. reflexivity. Qed.
Lemma wview_none : forall m a, m a = None -> wview PSEGS m a = wview PSEGS (fun _ => None) a.
Proof. intros m a H. unfold RiscvSemantics.wview. rewrite H. reflexivity. Qed.

Lemma tot_firstn2 : forall l : list (list byte), (2 <= length l)%nat ->
  total_arg_bytes_nat (firstn 2 l) = (total_arg_bytes_nat (firstn 1 l) + length (nth 1 l []) + 1)%nat.
Proof. intros [|a [|b l]] H; cbn [length] in H; try lia. simpl. lia. Qed.
