(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Tac.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes SysStep Decode.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes.ITree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SysStep OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Decode.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Import F_syscalls.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil RunW.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
End ACeilS1.


(* [comment removed for export] *)
Ltac transport_zeros segs m a n Ha Hn Han ::=
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_zeros_other segs m a n Ha Hn Han A2 bs2) in H; [|simpl_sizes; slia]
            | idtac "note: dropping hypothesis (not provably disjoint from zero-fill):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_zeros segs m a n Ha Hn Han A2 n2) in H
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_zeros_other segs m a n Ha Hn Han A2 cs2) in H; [|simpl_sizes; slia]
            | idtac "note: dropping hypothesis (not provably disjoint from zero-fill):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (ro_cells_zeros_other segs m a n Ha Hn Han A2 cs2) in H; [|simpl_sizes; slia]
            | idtac "note: dropping hypothesis (not provably disjoint from zero-fill):" H; clear H ]
  | H : stk segs m ?lo ?hi |- _ => apply (stk_zeros segs m a n Ha Hn Han lo hi) in H
  | H : munch ?W ?m0 m |- _ =>
      first [ apply (munch_zeros m a n Ha Hn Han W m0) in H; [|cbn [inside]; slia]
            | fail 100 "zero-filled range not inside the declared footprint" ]
  | H : wmono segs ?m0 m |- _ => apply (wmono_zeros segs m a n Ha Hn Han m0) in H
  | H : mem_inv segs m |- _ =>
      let H' := fresh "MI" in
      assert (H' : mem_inv segs (apply_zeros m [(wa a, Z_to_bv 64 n)]))
        by (apply (mem_inv_zeros segs m a n Ha Hn Han H); first [assumption | intros; shelve]);
      clear H
  end.

Ltac transport_unmaps segs m a n Ha Hn Han ::=
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_unmaps_other segs m a n Ha Hn Han A2 bs2) in H; [|simpl_sizes; slia]
            | idtac "note: dropping hypothesis (inside unmapped range):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ =>
      first [ apply (wr_at_unmaps_other segs m a n Ha Hn Han A2 n2) in H; [|slia]
            | idtac "note: dropping hypothesis (inside unmapped range):" H; clear H ]
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_unmaps_other segs m a n Ha Hn Han A2 cs2) in H; [|simpl_sizes; slia]
            | idtac "note: dropping hypothesis (inside unmapped range):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (ro_cells_unmaps_other segs m a n Ha Hn Han A2 cs2) in H; [|simpl_sizes; slia]
            | idtac "note: dropping hypothesis (inside unmapped range):" H; clear H ]
  | H : stk segs m ?lo ?hi |- _ =>
      first [ apply (stk_unmaps_other segs m a n Ha Hn Han lo hi) in H; [|slia]
            | idtac "note: dropping hypothesis (inside unmapped range):" H; clear H ]
  | H : munch ?W ?m0 m |- _ =>
      first [ apply (munch_unmaps m a n Ha Hn Han W m0) in H; [|cbn [inside]; slia]
            | fail 100 "unmapped range not inside the declared footprint" ]
  | H : wmono segs ?m0 m |- _ => idtac "note: dropping wmono (not preserved by an unmap):" H; clear H
  | H : mem_inv segs m |- _ => apply (mem_inv_unmaps segs m a n Ha Hn Han) in H
  end.
Section ACeilS2. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


Lemma mmap_len_ge : forall len, (len <= mmap_len len)%Z.
Proof. intros. unfold mmap_len, page_round_up_Z, page_size. Z.div_mod_to_equations. lia. Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition munmap_ret (a : range_ans) : word :=
  match a with RgErr _ => Z_to_bv 64 (-1) | RgDone _ => Z_to_bv 64 0 end.
Definition rg_errno (a : range_ans) (errv : word) : word :=
  match a with RgErr e => Z_to_bv 64 e | RgDone _ => errv end.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma mmap_len_aligned : forall len, (len mod 4096 = 0)%Z -> mmap_len len = len.
Proof. intros. unfold mmap_len, page_round_up_Z, page_size. Z.div_mod_to_equations. lia. Qed.

Lemma land_ldiff_distr' x a b : Z.land x (Z.ldiff a b) = Z.ldiff (Z.land x a) b.
Proof. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, !Z.ldiff_spec, Z.land_spec. destruct (Z.testbit x n), (Z.testbit a n), (Z.testbit b n); reflexivity. Qed.

Lemma land_m4096 x : (0 <= x < 2^64)%Z -> Z.land x 18446744073709547520 = (x - x mod 4096)%Z.
Proof.
  intros Hx.
  assert (E : 18446744073709547520%Z = Z.ldiff (Z.ones 64) (Z.ones 12)) by reflexivity. rewrite E.
  rewrite land_ldiff_distr'. rewrite Z.land_ones by lia. rewrite Z.mod_small by lia.
  rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  change (2^12)%Z with 4096%Z. pose proof (Z.div_mod x 4096). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)    (* [comment removed for export] *)
Definition AGP : Z := 0x1a800.           (* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mmap_fix_errno (e : Z) : Z := if (e =? 1)%Z then 12%Z else e.

(* [comment removed for export] *)
Definition mmap_raw (isnone : bool) (x len : Z) (m : word -> option byte) : word -> option byte :=
  if isnone then apply_unmaps m [(wa x, Z_to_bv 64 (mmap_len len))]
  else apply_zeros m [(wa x, Z_to_bv 64 (mmap_len len))].

(* [comment removed for export] *)
(* [comment removed for export] *)
End ACeilS2.



(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac sys_nret_raw :=
  rewrite nret_MSsvc; rewrite ?mkR_set_a0; simp_regs;
  (lazymatch goal with
   | |- evt _ _ (MS _ _ (Z_to_bv 64 ?p + Z_to_bv 64 4) _ _ _ _) =>
       let p' := eval vm_compute in (p + 4)%Z in
       replace (Z_to_bv 64 p + Z_to_bv 64 4 : word) with (Z_to_bv 64 p' : word) by (rewrite lit_add_lit; reflexivity)
   | _ => idtac
   end);
  first [ rewrite apply_mem_zeros | rewrite apply_mem_unmaps ].
Section ACeilS3. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition fixed_shape (A L : Z) (r : word) (u : bool) : resp :=
  if u then mkEffectU r [] [] [(wa A, Z_to_bv 64 (mmap_len L))] [] [] else mkEffectU r [] [] [] [] [].

(* [comment removed for export] *)

(* [comment removed for export] *)

End ACeilS3.
