(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Ported from the released walk of the same libc routine in the leptonica fhmtgen_fuzzer unit,
   projects/leptonica/fhmtgen_fuzzer/proofs/lib/K5/A10/F_sn_write.v (sha256
   49c4c8c7825e), together with its image-B copy
   K5/B10/F_sn_write.v (sha256 1863ce84c887).
   Code match: the donor's routine, decoded out of the leptonica binaries at 0xd9d74 (asan) and
   0xe2618 (asan-ubsan) with this repository's program-tree decoder, gives a tree equal byte for
   byte to sn_write_prog below.  The two walks therefore run the same 55 instructions, and differ
   only in where the routine and memcpy sit, which the Reloc layer keeps symbolic here.
   What the restatement changes: the donor's caller always leaves room, so its two byte counts are
   whole lengths and the routine's two min branches (offsets 68 and 116) are settled by its hypotheses.  Here
   the cookie's remaining count cn may stop either copy short, so each count is a minimum and both
   min branches are live; the walk therefore merges the two arms of each count's branch before going on.
   The donor's shadow-memory side conditions are replaced by this unit's copy_ready obligation,
   which the memcpy contract of CopyCall carries. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib Require Import SFModel Arr.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.P Require Import SFW1_lemmas.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.G Require Import G_memcpy G_fwritex.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.Reloc Require RProgAt.
Import OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.Reloc.RProgAt.RTac.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.Reloc Require Import RProgNotJ.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.Reloc Require Import RProgNot.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.Reloc Require RegFold.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.Reloc Require JunkAbs.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib Require Import NElim.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib Require StoreCache.
Import OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.StoreCache.StoreFast.
Import ListNotations.
Open Scope bv_scope.

(* The 55 instructions of the routine, as this repository's decoder emits them. *)
Definition sn_write_prog (B B_memcpy : Z) : RStep.ptree :=
PNode 120%Z
    (PNode 40%Z
      (PLeaf
          (PJ_OpImm_ALU_ADD_nnn 0 2 2 4032 4
          (PJ_Store_SZ8_nnn 4 2 1 56 4
          (PJ_Store_SZ8_nnn 8 2 8 48 4
          (PJ_Store_SZ8_nnn 12 2 9 40 4
          (PJ_Store_SZ8_nnn 16 2 18 32 4
          (PJ_Store_SZ8_nnn 20 2 19 24 4
          (PJ_Store_SZ8_nnn 24 2 20 16 4
          (PJ_Store_SZ8_nnn 28 2 21 8 4
          (PJ_OpImm_ALU_ADD_nnn 32 8 12 0 4
          (PJ_OpImm_ALU_ADD_nnn 36 18 11 0 4 nil)))))))))))
      (PNode 80%Z
        (PLeaf
            (PJ_OpImm_ALU_ADD_nnn 40 9 10 0 4
            (PJ_Load_SZ8_true_nnn 44 21 10 152 4
            (PJ_Load_SZ8_true_nnn 48 10 10 40 4
            (PJ_Load_SZ8_true_nnn 52 11 9 56 4
            (PJ_Load_SZ8_true_nnn 56 19 21 8 4
            (PJ_Op_ALU_SUB_nnn 60 10 10 11 4
            (PJ_OpImm_ALU_ADD_nnn 64 20 19 0 4
            (PJ_Branch_BC_LTU_nnn 68 19 10 8 4
            (PJ_OpImm_ALU_ADD_nnn 72 20 10 0 4
            (PJ_Load_SZ8_true_nnn 76 10 21 0 4 nil)))))))))))
        (PLeaf
            (PJ_Branch_BC_EQ_nnn 80 20 0 36 4
            (PJ_OpImm_ALU_ADD_nnn 84 12 20 0 4
            (PJ_Jal_nt 88 1 (jimm21 (B_memcpy - (B + 88))) 4
            (PJ_Load_SZ8_true_nnn 92 10 21 0 4
            (PJ_Load_SZ8_true_nnn 96 11 21 8 4
            (PJ_Op_ALU_ADD_nnn 100 10 10 20 4
            (PJ_Op_ALU_SUB_nnn 104 19 11 20 4
            (PJ_Store_SZ8_nnn 108 21 10 0 4
            (PJ_Store_SZ8_nnn 112 21 19 8 4
            (PJ_Branch_BC_LTU_nnn 116 19 8 8 4 nil)))))))))))))
    (PNode 160%Z
      (PLeaf
          (PJ_OpImm_ALU_ADD_nnn 120 19 8 0 4
          (PJ_Branch_BC_EQ_nnn 124 19 0 40 4
          (PJ_OpImm_ALU_ADD_nnn 128 11 18 0 4
          (PJ_OpImm_ALU_ADD_nnn 132 12 19 0 4
          (PJ_Jal_nt 136 1 (jimm21 (B_memcpy - (B + 136))) 4
          (PJ_Load_SZ8_true_nnn 140 10 21 0 4
          (PJ_Load_SZ8_true_nnn 144 11 21 8 4
          (PJ_Op_ALU_ADD_nnn 148 10 10 19 4
          (PJ_Op_ALU_SUB_nnn 152 11 11 19 4
          (PJ_Store_SZ8_nnn 156 21 10 0 4 nil)))))))))))
      (PNode 200%Z
        (PLeaf
            (PJ_Store_SZ8_nnn 160 21 11 8 4
            (PJ_Store_SZ1_nnn 164 10 0 0 4
            (PJ_Load_SZ8_true_nnn 168 10 9 88 4
            (PJ_Store_SZ8_nnn 172 9 10 40 4
            (PJ_Store_SZ8_nnn 176 9 10 56 4
            (PJ_OpImm_ALU_ADD_nnn 180 10 8 0 4
            (PJ_Load_SZ8_true_nnn 184 1 2 56 4
            (PJ_Load_SZ8_true_nnn 188 8 2 48 4
            (PJ_Load_SZ8_true_nnn 192 9 2 40 4
            (PJ_Load_SZ8_true_nnn 196 18 2 32 4 nil)))))))))))
        (PLeaf
            (PJ_Load_SZ8_true_nnn 200 19 2 24 4
            (PJ_Load_SZ8_true_nnn 204 20 2 16 4
            (PJ_Load_SZ8_true_nnn 208 21 2 8 4
            (PJ_OpImm_ALU_ADD_nnn 212 2 2 64 4
            (PJ_Jalr_nnn 216 0 1 0 4 nil)))))))).

(* The routine is reached through a relocation, so every step tactic goes through the Reloc layer
   and the store and call tactics through their StoreFast (`_fast`) forms, as the Ltac lines below
   set them. *)
Local Ltac OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.Step.step2_with rp rpm vh ::= OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.Reloc.RProgAt.RTac.astep2_with rp rpm vh.
Local Ltac OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.SysStep.step_ecall ::= OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.Reloc.RProgAt.RTac.astep_ecall.
Local Ltac OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.Step.solve_load ::= OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.Reloc.RProgAt.RTac.asolve_load.
Local Ltac OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.Step.solve_cond ::= OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.Reloc.RProgAt.RTac.asolve_cond.
Local Ltac OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.Step.step ::= OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.Step.stepz ::= OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.Step.stepz_fast ::= OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.Reloc.RProgAt.RTac.astep2_fast.
Local Ltac OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.SysStep.sys_nret ::= OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.Reloc.RProgAt.RTac.asys_nret.
Local Ltac OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.Tac.post_call segs m ::= OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.Reloc.RProgAt.RTac.apost_call segs m.
Local Ltac OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.Step.simp_regs ::= OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.Reloc.RegFold.simp_regs_f.
Local Ltac OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.Reloc.RProgAt.RTac.find_t_eval k t ::= OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.Reloc.RProgAt.find_t_eval_at k t.
Local Ltac OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.Step.split_for_access H segs m A cs kn n ::=
  OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.Reloc.JunkAbs.split_for_access_abs H segs m A cs kn n.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac lia ::= lia3.

Definition PROGAT_CODE_sn_write (IMG : RImg) := sn_write_prog (sym 0x7f000300) (sym 0x21334).

Import OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.StoreCache.LiaClosure.
(* The statement carries eleven separation disjunctions, and the arithmetic side goals of the step,
   store and call tactics would otherwise case-split on all of them.  Try each side goal without
   them first, and fall back to the full context only when a separation fact is really needed. *)
Local Ltac lia ::= first [ (repeat match goal with H : _ \/ _ |- _ => clear H end); lia4 | lia4 ].
Local Ltac tlia ::= tlia4.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Open Scope Z_scope.

(* How many bytes reach the string buffer: the cookie's remaining count, capped by how much
   there is to write. *)
Definition sn_k (cn : Z) (pend src : list byte) : Z := Z.min cn (Z.of_nat (length pend + length src)).

(* A byte-block cell carries exactly as many bytes as its size says. *)
Lemma rw_CB_len : forall (segs : list Segment) (m : word -> option byte) (a : Z) (n : nat) (l : list byte),
  rw_cells segs m a [CB n l] -> length l = n.
Proof. intros segs m a n l [[[Hwf _] _] _]. exact Hwf. Qed.

(* Cut one writable block in two at offset n1. *)
Lemma rw_CB_split : forall (segs : list Segment) (m : word -> option byte) (a : Z) (n1 n2 : nat) (l : list byte),
  rw_cells segs m a [CB (n1 + n2) l] ->
  rw_cells segs m a [CB n1 (firstn n1 l)] /\ rw_cells segs m (a + Z.of_nat n1) [CB n2 (skipn n1 l)].
Proof.
  intros segs m a n1 n2 l Hblk.
  pose proof (rw_CB_len _ _ _ _ _ Hblk) as Hlen.
  assert (Hsum : sum_nat [n1; n2] = (n1 + n2)%nat) by (cbn; lia).
  pose proof (rw_cells_split_CB segs m a [] _ l [] _ Hblk Hsum) as Hpair.
  cbn [app mk_CB_cells] in Hpair.
  rewrite (firstn_all2 (n := n2)) in Hpair by (rewrite length_skipn; lia).
  change (rw_cells segs m a ([CB n1 (firstn n1 l)] ++ [CB n2 (skipn n1 l)])) in Hpair.
  apply rw_cells_app in Hpair.
  cbn [cells_size csize] in Hpair. rewrite Nat.add_0_r in Hpair. exact Hpair.
Qed.

(* Glue two adjacent writable blocks back into one. *)
Lemma rw_CB_join : forall (segs : list Segment) (m : word -> option byte) (a : Z) (n1 n2 : nat) (l1 l2 : list byte),
  rw_cells segs m a [CB n1 l1] -> rw_cells segs m (a + Z.of_nat n1) [CB n2 l2] ->
  rw_cells segs m a [CB (n1 + n2) (l1 ++ l2)].
Proof.
  intros segs m a n1 n2 l1 l2 Hlo Hhi.
  assert (Hboth : rw_cells segs m a ([] ++ [CB n1 l1; CB n2 l2] ++ [])).
  { cbn [app]. change [CB n1 l1; CB n2 l2] with ([CB n1 l1] ++ [CB n2 l2]).
    apply rw_cells_app. split; [exact Hlo|].
    cbn [cells_size csize]. rewrite Nat.add_0_r. exact Hhi. }
  apply rw_cells_merge in Hboth.
  cbn [app cells_size cells_bytes csize cbytes] in Hboth.
  rewrite Nat.add_0_r, app_nil_r in Hboth. exact Hboth.
Qed.

(* The empty block holds at any in-range address: this is what the arm that copies nothing
   gives back. *)
Lemma rw_CB_nil : forall (segs : list Segment) (m : word -> option byte) (a : Z),
  0 <= a <= 2 ^ 64 -> rw_cells segs m a [CB 0 []].
Proof.
  intros segs m a Ha. split; [split|].
  - exact (conj eq_refl I).
  - apply bytes_at_nil. exact Ha.
  - cbn [cells_size csize]. split; [lia|]. split; [lia|]. intros i Hi. lia.
Qed.

(* The string buffer after both copies and the terminating byte z: the first c bytes of the
   pending buffer followed by the caller's bytes, then z, then what the buffer still held.
   k1n and k2n are how much each copy moved. *)
Lemma sn_bytes : forall (pend src dst : list byte) (c k1n k2n : nat) (z : byte),
  k1n = Nat.min c (length pend) ->
  k2n = Nat.min (c - k1n) (length src) ->
  (k1n + k2n < length dst)%nat ->
  firstn k1n pend ++ firstn k2n src ++ upd (skipn k2n (skipn k1n dst)) 0 z
  = firstn c (pend ++ src) ++ z :: skipn (S (k1n + k2n)) dst.
Proof.
  intros pend src dst c k1n k2n z Hk1 Hk2 Hroom.
  assert (Hcap : forall (l : list byte) n, firstn (Nat.min n (length l)) l = firstn n l).
  { intros l n. destruct (Nat.le_ge_cases n (length l)) as [Hn | Hn].
    - rewrite Nat.min_l by exact Hn. reflexivity.
    - rewrite Nat.min_r by exact Hn. rewrite firstn_all, firstn_all2 by exact Hn. reflexivity. }
  rewrite upd_firstn_skipn by (rewrite !length_skipn; lia).
  rewrite firstn_O, app_nil_l.
  rewrite (skipn_skipn k2n k1n), (skipn_skipn 1 (k2n + k1n)), firstn_app, <- app_assoc.
  replace (1 + (k2n + k1n))%nat with (S (k1n + k2n)) by lia.
  subst k1n k2n. rewrite !Hcap.
  replace (c - Nat.min c (length pend))%nat with (c - length pend)%nat by lia.
  reflexivity.
Qed.

Lemma le1_z0 : le1 (Z_to_bv 64 0) = [Z_to_bv 8 0].
Proof. reflexivity. Qed.

(* A wrapper that keeps a hypothesis out of the way of the transport tactics. *)
Definition hid (P : Prop) : Prop := P.

From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA Require Import CopyCall.

Local Ltac wstep := zstep.
(* The statement carries eleven separation disjunctions.  Each one a tactic can see costs it a
   case split, so a phase that does not need one hides it behind [hid]. *)
Local Ltac park H := let T := type of H in change (hid T) in H.
Local Ltac unpark H := unfold hid in H.
Local Ltac park_seps := repeat match goal with H : _ \/ _ |- _ => park H end.
Local Ltac klia := repeat match goal with H : _ \/ _ |- _ => clear H end; lia.

(* The frame stores touch only the frame.  Hide every memory fact that is not about the stack
   across all seven of them, then move them all past the stores with one transport. *)
Local Ltac park_off_stack H A sp :=
  lazymatch A with context [bv_unsigned sp] => fail | _ => park H end.
Local Ltac park_mem sp n MUF WMF :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
    pose proof (munch_refl [(bv_unsigned sp - n, bv_unsigned sp)] m) as MUF;
    pose proof (wmono_refl segs m) as WMF;
    repeat match goal with
    | H : rw_cells segs m ?A _ |- _ => park_off_stack H A sp
    | H : bytes_at segs m ?A _ |- _ => park_off_stack H A sp
    end
  end.
Local Ltac unpark_mem MUF WMF :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch type of MUF with munch _ ?m _ =>
      unfold hid in *; transport_after_call segs m mm MUF WMF; clear MUF WMF end end.

Local Ltac bcase K := if_cases K; zify_cond K.
(* Run [t] only in the arm where the count the branch tested is zero (resp. is not). *)
Local Ltac when_zero K t := lazymatch type of K with Z.of_nat _ = 0 => t | _ => idtac end.
Local Ltac when_nonzero K t := lazymatch type of K with Z.of_nat _ = 0 => idtac | _ => t end.

(* Each of the two byte counts is computed by a branch whose arms meet again one instruction
   later.  Cut the walk at the meeting point, with the count's register set to [v]. *)
Local Ltac meet_at slot v :=
  lazymatch goal with
  | |- evt ?sg _ (MS (mkR ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 ?x12 ?x13 ?x14 ?x15 ?x16 ?x17 ?x18 ?x19 ?x20 ?x21 ?x22 ?x23 ?x24 ?x25 ?x26 ?x27 ?x28 ?x29 ?x30 ?x31) ?FF (if _ then ?pT else _) ?fcc ?rv ?mm ?ro) =>
      let R' := lazymatch slot with
        | 19%nat => constr:(mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 v x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        | 20%nat => constr:(mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 v x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        end in
      apply (evt_cut sg (fun ms => ms = MS R' FF pT fcc rv mm ro))
  end.

Section Img.
  Context {IMG : RImg}.
  Context {CODE_sn_write : CodeAtT img_segs (sym 0x7f000300) (PROGAT_CODE_sn_write IMG)}.
  Context {RB_sn_write : RelCode (sym 0x7f000300) 220}.
  Context {RN_B_memcpy_7f000300 : RelNear (sym 0x7f000300) (sym 0x21334)}.
  Variable copy_ready : (word -> option byte) -> Z -> Z -> Z -> Z -> Prop.
  Context {SPEC_memcpy : memcpy_stack_contract copy_ready}.

(* What one call of memcpy from this routine leaves behind.  The source bytes are not named in
   the post: the walk carries them over the call itself. *)
Definition memcpy_postk (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (a0 : word) (Dst : Z) (n : nat) (src : list byte)
    (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom img_segs)
    /\ munch [(Dst, Dst + Z.of_nat n); (bv_unsigned sp - COPY_DEPTH, bv_unsigned sp)] m m'
    /\ wmono img_segs m m' /\ mem_inv img_segs m'
    /\ stk img_segs m' (bv_unsigned sp - COPY_DEPTH) (bv_unsigned sp)
    /\ rw_cells img_segs m' Dst [CB n src].

Lemma memcpy_callk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Dst Src : Z) (n : nat) (src junk : list byte),
  bv_unsigned a0 = Dst ->
  bv_unsigned a1 = Src ->
  bv_unsigned a2 = Z.of_nat n ->
  bytes_at img_segs m Src src ->
  length src = n ->
  rw_cells img_segs m Dst [CB n junk] ->
  Src + Z.of_nat n <= Dst \/ Dst + Z.of_nat n <= Src ->
  Src + Z.of_nat n <= bv_unsigned sp - COPY_DEPTH \/ bv_unsigned sp <= Src ->
  mem_inv img_segs m ->
  stk img_segs m (bv_unsigned sp - COPY_DEPTH) (bv_unsigned sp) ->
  copy_ready m (bv_unsigned sp) Dst Src (Z.of_nat n) ->
  evt img_segs (memcpy_postk ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 Dst n src m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (sym 0x21334)) fc None m (seg_rom img_segs)).
Proof.
  intros until junk. intros HD HS HN SRC LEN DST SEP SSEP MI ST READY. subst Dst Src.
  eapply evt_mono.
  { eapply (SPEC_memcpy ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m src junk);
      rewrite ?HN, ?Nat2Z.id; [exact SRC | exact LEN | exact DST | exact SEP | exact SSEP | exact MI | exact ST | exact READY]. }
  intros ms' P. unfold memcpy_stack_post in P. unfold memcpy_postk. rewrite HN, Nat2Z.id in P.
  destruct P as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & m' & E & MU & WM & MI' & ST' & DC & SC).
  exists y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, m'. tauto.
Qed.

(* Call a routine whose contract [t] applies, and carry on where it returns. *)
Local Ltac call_with t :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
      eapply evt_cut;
      [ t
      | intros msq Pq; unfold memcpy_postk, COPY_DEPTH in Pq;
        rewrite unsigned_lit in Pq by klia; revert msq Pq; post_call segs m ]
  end.
(* The sanitizer's memcpy gives the stack region back; take its fact as the current one. *)
Local Ltac retake_stack sp STKn :=
  match goal with H : stk img_segs _ (bv_unsigned sp + -64 - 2240) _ |- _ =>
    try clear STKn; rename H into STKn end;
  replace (bv_unsigned sp + -64 - 2240) with (bv_unsigned sp - (64 + 2240)) in STKn by klia.


(* After the call the string buffer holds the first sn_k bytes of what was offered, zero
   terminated; the cookie's cursor and count have moved by sn_k; the FILE's write window is
   back to the empty buffer. *)
Definition sn_write_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (f bufp CK cs cn : Z) (pend src dst : list byte)
    (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (Z.of_nat (length src))) a1 a2 a3 a4 a5 a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom img_segs)
    /\ munch [(bv_unsigned sp - SN_WRITE_DEPTH, bv_unsigned sp); (f + 40, f + 48); (f + 56, f + 64);
              (CK, CK + 16); (cs, cs + Z.of_nat (length dst))] m m'
    /\ wmono img_segs m m'
    /\ mem_inv img_segs m'
    /\ stk img_segs m' (bv_unsigned sp - SN_WRITE_DEPTH) (bv_unsigned sp)
    /\ rw_cells img_segs m' (f + 40) [C8 (Z_to_bv 64 bufp)]
    /\ rw_cells img_segs m' (f + 56) [C8 (Z_to_bv 64 bufp)]
    /\ rw_cells img_segs m' CK [C8 (Z_to_bv 64 (cs + sn_k cn pend src)); C8 (Z_to_bv 64 (cn - sn_k cn pend src))]
    /\ rw_cells img_segs m' cs
         [CB (length dst) (firstn (Z.to_nat cn) (pend ++ src)
                           ++ Z_to_bv 8 0 :: skipn (S (Z.to_nat (sn_k cn pend src))) dst)].

Definition sn_write_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (f WB bufp CK cs cn : Z) (pend src dst : list byte),
  a0 = Z_to_bv 64 f ->
  bytes_at img_segs m (bv_unsigned a1) src ->
  bv_unsigned a2 = Z.of_nat (length src) ->
  rw_cells img_segs m (f + 40) [C8 (Z_to_bv 64 (WB + Z.of_nat (length pend)))] ->
  rw_cells img_segs m (f + 56) [C8 (Z_to_bv 64 WB)] ->
  rw_cells img_segs m (f + 88) [C8 (Z_to_bv 64 bufp)] ->
  rw_cells img_segs m (f + 152) [C8 (Z_to_bv 64 CK)] ->
  rw_cells img_segs m CK [C8 (Z_to_bv 64 cs); C8 (Z_to_bv 64 cn)] ->
  bytes_at img_segs m WB pend ->
  WB + Z.of_nat (length pend) < 2 ^ 64 ->
  rw_cells img_segs m cs [CB (length dst) dst] ->
  0 <= cn < 2 ^ 64 ->
  sn_k cn pend src < Z.of_nat (length dst) ->
  stk img_segs m (bv_unsigned sp - SN_WRITE_DEPTH) (bv_unsigned sp) ->
  SN_WRITE_DEPTH <= bv_unsigned sp ->
  mem_inv img_segs m ->
  sn_write_ready copy_ready m (bv_unsigned sp) f CK cs (Z.of_nat (length dst)) WB
    (Z.of_nat (length pend)) (bv_unsigned a1) (Z.of_nat (length src)) ->
  f + 160 <= bv_unsigned sp - SN_WRITE_DEPTH \/ bv_unsigned sp <= f + 40 ->
  CK + 16 <= bv_unsigned sp - SN_WRITE_DEPTH \/ bv_unsigned sp <= CK ->
  cs + Z.of_nat (length dst) <= bv_unsigned sp - SN_WRITE_DEPTH \/ bv_unsigned sp <= cs ->
  WB + Z.of_nat (length pend) <= bv_unsigned sp - SN_WRITE_DEPTH \/ bv_unsigned sp <= WB ->
  bv_unsigned a1 + Z.of_nat (length src) <= bv_unsigned sp - SN_WRITE_DEPTH
  \/ bv_unsigned sp <= bv_unsigned a1 ->
  CK + 16 <= f + 40 \/ f + 160 <= CK ->
  cs + Z.of_nat (length dst) <= f + 40 \/ f + 160 <= cs ->
  cs + Z.of_nat (length dst) <= CK \/ CK + 16 <= cs ->
  WB + Z.of_nat (length pend) <= cs \/ cs + Z.of_nat (length dst) <= WB ->
  bv_unsigned a1 + Z.of_nat (length src) <= cs \/ cs + Z.of_nat (length dst) <= bv_unsigned a1 ->
  bv_unsigned a1 + Z.of_nat (length src) <= CK \/ CK + 16 <= bv_unsigned a1 ->
  evt img_segs (sn_write_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f bufp CK cs cn pend src dst m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (sym 0x7f000300)) fc None m (seg_rom img_segs)).

Lemma sn_write_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (f WB bufp CK cs cn : Z) (pend src dst : list byte),
  a0 = Z_to_bv 64 f ->
  bytes_at img_segs m (bv_unsigned a1) src ->
  bv_unsigned a2 = Z.of_nat (length src) ->
  rw_cells img_segs m (f + 40) [C8 (Z_to_bv 64 (WB + Z.of_nat (length pend)))] ->
  rw_cells img_segs m (f + 56) [C8 (Z_to_bv 64 WB)] ->
  rw_cells img_segs m (f + 88) [C8 (Z_to_bv 64 bufp)] ->
  rw_cells img_segs m (f + 152) [C8 (Z_to_bv 64 CK)] ->
  rw_cells img_segs m CK [C8 (Z_to_bv 64 cs); C8 (Z_to_bv 64 cn)] ->
  bytes_at img_segs m WB pend ->
  WB + Z.of_nat (length pend) < 2 ^ 64 ->
  rw_cells img_segs m cs [CB (length dst) dst] ->
  0 <= cn < 2 ^ 64 ->
  sn_k cn pend src < Z.of_nat (length dst) ->
  stk img_segs m (bv_unsigned sp - SN_WRITE_DEPTH) (bv_unsigned sp) ->
  SN_WRITE_DEPTH <= bv_unsigned sp ->
  mem_inv img_segs m ->
  sn_write_ready copy_ready m (bv_unsigned sp) f CK cs (Z.of_nat (length dst)) WB
    (Z.of_nat (length pend)) (bv_unsigned a1) (Z.of_nat (length src)) ->
  f + 160 <= bv_unsigned sp - SN_WRITE_DEPTH \/ bv_unsigned sp <= f + 40 ->
  CK + 16 <= bv_unsigned sp - SN_WRITE_DEPTH \/ bv_unsigned sp <= CK ->
  cs + Z.of_nat (length dst) <= bv_unsigned sp - SN_WRITE_DEPTH \/ bv_unsigned sp <= cs ->
  WB + Z.of_nat (length pend) <= bv_unsigned sp - SN_WRITE_DEPTH \/ bv_unsigned sp <= WB ->
  bv_unsigned a1 + Z.of_nat (length src) <= bv_unsigned sp - SN_WRITE_DEPTH
  \/ bv_unsigned sp <= bv_unsigned a1 ->
  CK + 16 <= f + 40 \/ f + 160 <= CK ->
  cs + Z.of_nat (length dst) <= f + 40 \/ f + 160 <= cs ->
  cs + Z.of_nat (length dst) <= CK \/ CK + 16 <= cs ->
  WB + Z.of_nat (length pend) <= cs \/ cs + Z.of_nat (length dst) <= WB ->
  bv_unsigned a1 + Z.of_nat (length src) <= cs \/ cs + Z.of_nat (length dst) <= bv_unsigned a1 ->
  bv_unsigned a1 + Z.of_nat (length src) <= CK \/ CK + 16 <= bv_unsigned a1 ->
  evt img_segs (sn_write_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f bufp CK cs cn pend src dst m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (sym 0x7f000300)) fc None m (seg_rom img_segs)).
Proof.
  intros until dst.
  intros -> SRCB LSRC CPOS CBASE CBUF CCK CKC PENDB WHI DSTC CNR ROOM STK SPLO MINV RDY
    X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11.
  (* name the length register by its value, keeping its range *)
  assert (LHI : Z.of_nat (length src) < 2 ^ 64).
  { rewrite <- LSRC. pose proof (bv_unsigned_in_range 64 a2) as Ra. unfold bv_modulus in Ra. exact (proj2 Ra). }
  assert (Ea2 : a2 = Z_to_bv 64 (Z.of_nat (length src))) by (rewrite <- LSRC; symmetry; apply Z_to_bv_bv_unsigned).
  subst a2. clear LSRC.
  pose proof (rw_cells_bound _ _ _ _ CPOS) as BP. cbn [cells_size csize Nat.add] in BP.
  pose proof (rw_cells_bound _ _ _ _ CCK) as BC. cbn [cells_size csize Nat.add] in BC.
  pose proof (rw_cells_bound _ _ _ _ CKC) as BK. cbn [cells_size csize Nat.add] in BK.
  pose proof (rw_cells_bound _ _ _ _ DSTC) as BD. cbn [cells_size csize Nat.add] in BD.
  pose proof (bytes_at_bound _ _ _ _ SRCB) as BS.
  pose proof (bytes_at_bound _ _ _ _ PENDB) as BW.
  unfold sn_k in ROOM.
  unfold SN_WRITE_DEPTH, COPY_DEPTH, sn_write_ready, sn_write_footprint in *.
  (* the two byte counts the routine computes *)
  remember (Nat.min (Z.to_nat cn) (length pend)) as n1 eqn:En1.
  remember (Nat.min (Z.to_nat cn - n1) (length src)) as n2 eqn:En2.
  assert (NR : (n1 + n2 < length dst)%nat) by lia.
  pose proof (munch_refl [(bv_unsigned sp - (64 + 2240), bv_unsigned sp); (f + 40, f + 48); (f + 56, f + 64);
                          (CK, CK + 16); (cs, cs + Z.of_nat (length dst))] m) as MU.
  pose proof (wmono_refl img_segs m) as WM.
  pose_word_ranges.
  carve_frame 64%nat STK.
  (* prologue: save the frame, then move every heap fact past all seven stores at once *)
  park_mem sp 64 MUF WMF.
  do 8 wstep.
  unpark_mem MUF WMF.
  do 7 wstep.
  wstep. replace (WB + Z.of_nat (length pend) - WB) with (Z.of_nat (length pend)) by klia.
  wstep. wstep.
  (* offset 68: the pending count is capped by the cookie's count *)
  meet_at 20%nat (Z_to_bv 64 (Z.of_nat n1)).
  { bcase KM1.
    - apply evt_done. ms_eq.
    - wstep. apply evt_done. ms_eq. }
  intros ms' ->.
  wstep.
  (* cut the string buffer where the pending bytes end *)
  replace (length dst) with (n1 + (length dst - n1))%nat in DSTC at 1 by klia.
  apply rw_CB_split in DSTC. destruct DSTC as [DLO DHI].
  wstep. bcase KZ1.
  (* goal 1: no pending byte is copied (offset 116); goal 2: copy them (offset 84) *)
  1: clear PENDB X9 X4 WHI.
  1: replace (firstn n1 dst) with (firstn n1 pend) in DLO by (replace n1 with 0%nat by klia; reflexivity).
  2: wstep. 2: wstep.
  2: rewrite <- (firstn_skipn n1 pend) in PENDB.
  2: apply (proj1 (bytes_at_app _ _ _ _ _)) in PENDB.
  2: destruct PENDB as [PFX _].
  2: (park X6; park X11).
  2: call_with ltac:(eapply memcpy_callk with (Dst := cs) (Src := WB) (n := n1)
                       (src := firstn n1 pend) (junk := firstn n1 dst);
                     [ apply unsigned_lit; klia | apply unsigned_lit; klia | apply unsigned_lit; klia
                     | exact PFX | rewrite length_firstn; klia | exact DLO
                     | destruct X9; klia
                     | unfold COPY_DEPTH; rewrite unsigned_lit by klia; destruct X4; klia
                     | assumption
                     | unfold COPY_DEPTH; rewrite unsigned_lit by klia;
                       replace (bv_unsigned sp + -64 - 2240) with (bv_unsigned sp - (64 + 2240)) by klia;
                       exact STK
                     | rewrite unsigned_lit by klia;
                       replace (bv_unsigned sp + -64) with (bv_unsigned sp - 64) by klia;
                       eapply RDY; [exact MU | exact WM | klia | klia | klia
                                   | left; split; [reflexivity | klia]] ]).
  2: retake_stack sp STK.
  2: rename POST into DLO.
  (* advance the cookie past the bytes just copied *)
  2: (clear X9 X4 WHI; park_seps; unpark X2; unpark X6; unpark X8; unpark X11).
  2: do 6 wstep.
  (* both goals are at offset 116: cap the source count *)
  all: park_seps.
  all: wstep.
  all: meet_at 19%nat (Z_to_bv 64 (Z.of_nat n2));
       [ bcase KM2; [ apply evt_done; ms_eq | wstep; apply evt_done; ms_eq ] | intros ms' -> ].
  (* cut the rest of the buffer where the copied source bytes end *)
  all: replace (length dst - n1)%nat with (n2 + (length dst - n1 - n2))%nat in DHI by klia.
  all: apply rw_CB_split in DHI.
  all: destruct DHI as [DMID DTOP].
  all: wstep.
  all: bcase KZ2.
  (* where no source byte is copied the goal is at offset 164, otherwise at offset 128 *)
  all: when_zero KZ2 ltac:(clear SRCB X10 X11 X5).
  all: when_zero KZ2 ltac:(replace (firstn n2 (skipn n1 dst)) with (firstn n2 src) in DMID
                             by (replace n2 with 0%nat by klia; reflexivity)).
  all: when_nonzero KZ2 ltac:(do 3 wstep).
  all: when_nonzero KZ2 ltac:(rewrite <- (firstn_skipn n2 src) in SRCB).
  all: when_nonzero KZ2 ltac:(apply (proj1 (bytes_at_app _ _ _ _ _)) in SRCB).
  all: when_nonzero KZ2 ltac:(destruct SRCB as [SFX _]).
  all: when_nonzero KZ2 ltac:(unpark X1; unpark X2; unpark X3; unpark X5; unpark X7; unpark X8; unpark X10).
  all: when_nonzero KZ2 ltac:(idtac;
         call_with ltac:(eapply memcpy_callk with (Dst := cs + Z.of_nat n1) (Src := bv_unsigned a1) (n := n2)
                           (src := firstn n2 src) (junk := firstn n2 (skipn n1 dst));
                         [ first [ reflexivity | rewrite unsigned_lit; klia ] | reflexivity
                         | first [ reflexivity | rewrite unsigned_lit; klia ]
                         | exact SFX | rewrite length_firstn; klia | exact DMID
                         | destruct X10; klia
                         | unfold COPY_DEPTH; rewrite unsigned_lit by klia; destruct X5; klia
                         | assumption
                         | unfold COPY_DEPTH; rewrite unsigned_lit by klia;
                           replace (bv_unsigned sp + -64 - 2240) with (bv_unsigned sp - (64 + 2240)) by klia;
                           exact STK
                         | rewrite unsigned_lit by klia;
                           replace (bv_unsigned sp + -64) with (bv_unsigned sp - 64) by klia;
                           eapply RDY; [exact MU | exact WM | klia | klia | klia
                                       | right; split; [reflexivity | klia]] ])).
  all: when_nonzero KZ2 ltac:(retake_stack sp STK).
  all: when_nonzero KZ2 ltac:(rename POST into DMID).
  all: when_nonzero KZ2 ltac:(clear X10 X5; park_seps; unpark X2; unpark X6; unpark X8).
  all: when_nonzero KZ2 ltac:(do 6 wstep).
  (* all four goals are at offset 164: the terminating zero goes after the copied bytes *)
  all: (park_seps; unpark X3; unpark X7; unpark X8).
  all: pose proof (rw_CB_len _ _ _ _ _ DTOP) as LTOP.
  all: pose proof (u8arr_of_rw_cells _ _ _ _ _ DTOP) as UTOP.
  all: clear DTOP.
  all: lazymatch goal with
       | |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ ?av _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
           pose proof (u8arr_store_ok img_segs _ _ _ 0 av UTOP ltac:(rewrite LTOP; klia)
                         ltac:(unfold wa; f_equal; klia)) as SOK
       end.
  all: wstep.
  all: rewrite le1_z0.
  all: lazymatch goal with
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ ?av _) _) =>
           replace av with (wa (cs + Z.of_nat n1 + Z.of_nat n2 + 0)) by (unfold wa; f_equal; klia)
       end.
  all: pose proof (u8arr_write img_segs _ _ _ 0 (Z_to_bv 8 0) UTOP ltac:(rewrite LTOP; klia)) as UTOP2.
  all: clear UTOP.
  all: store_done.
  all: pose proof (rw_cells_of_u8arr _ _ _ _ UTOP2) as DTOP.
  all: rewrite upd_length, LTOP in DTOP.
  all: clear UTOP2.
  (* point the FILE's write window back at the empty buffer, return the byte count, unwind *)
  all: (unpark X1; unpark X2; unpark X6; park X3; park X8).
  all: do 13 wstep.
  all: release_frame FR STK (bv_unsigned sp).
  all: replace (bv_unsigned sp + -64) with (bv_unsigned sp - 64) in MU by klia.
  all: replace (bv_unsigned sp + -64) with (bv_unsigned sp - 64) in STK by klia.
  all: apply evt_done.
  all: unfold sn_write_post.
  all: repeat (lazymatch goal with |- ex _ => eexists end).
  all: split; [ ms_eq | ].
  all: split; [ exact MU | ].
  all: split; [ exact WM | ].
  all: split; [ assumption | ].
  all: split; [ exact STK | ].
  all: split; [ exact CPOS | ].
  all: split; [ exact CBASE | ].
  (* the cookie has moved on by the number of bytes copied *)
  all: split;
       [ lazymatch goal with
         | H : rw_cells _ ?mm ?A [C8 ?u'; C8 ?v'] |- rw_cells _ ?mm ?A [C8 ?u; C8 ?v] =>
             replace u with u' by (f_equal; unfold sn_k; klia);
             replace v with v' by (f_equal; unfold sn_k; klia); exact H
         end | ].
  (* join the three parts of the buffer and read off the bytes *)
  all: pose proof (rw_CB_join _ _ _ _ _ _ _ DLO DMID) as DJ.
  all: replace (cs + Z.of_nat n1 + Z.of_nat n2) with (cs + Z.of_nat (n1 + n2)) in DTOP by klia.
  all: pose proof (rw_CB_join _ _ _ _ _ _ _ DJ DTOP) as DALL.
  all: rewrite <- app_assoc in DALL.
  all: change (Z.to_nat 0) with 0%nat in DALL.
  all: rewrite (sn_bytes pend src dst (Z.to_nat cn) n1 n2 (Z_to_bv 8 0) En1 En2 NR) in DALL.
  all: replace (n1 + n2 + (length dst - n1 - n2))%nat with (length dst) in DALL by klia.
  all: replace (Z.to_nat (sn_k cn pend src)) with (n1 + n2)%nat by (unfold sn_k; klia).
  all: exact DALL.
Qed.

Lemma sn_write_contract_ok : sn_write_contract.
Proof. exact sn_write_spec. Qed.

End Img.

Existing Class sn_write_contract.
