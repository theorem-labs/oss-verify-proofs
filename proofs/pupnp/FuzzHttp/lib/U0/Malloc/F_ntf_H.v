(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Image ZBridge SysStep SFModel Arr.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.Malloc Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast MallocTree.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import STree Malloc MallocCtrl.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.Malloc Require Import MallocKit_B MallocModel_B F_ntf_A F_ntf_B F_ntf_C.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.Malloc Require Import MallocKit_B3 F_ntf_F.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Definition ntf_cond (st : mstate) (g : aptr) (i : Z) : bool :=
  let mr := get_meta_rec st g in
  (Z.lor (m_freed mr) (m_avail mr) + bit i =? mask_upto (m_last_idx mr)) && okay_to_free st g.

Section POST.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (st : mstate) (g : aptr) (i : Z) (m1 : word -> option byte).
Local Notation mr := (get_meta_rec st g).
Local Notation sc := (m_sizeclass mr).
Local Notation mask := (Z.lor (m_freed mr) (m_avail mr)).
Local Notation sp' := (Z_to_bv 64 (bv_unsigned sp + -80)).
Local Notation G := (Z_to_bv 64 (conc st g)).
Local Notation SELF := (wz (sxv (2 ^ i))).
Local Notation HD := (pw st (active st sc)).
End POST.

Record entry_hyps (st : mstate) (g : aptr) (i : Z) : Prop := mkEH {
  eh_slot : meta_slot st g;
  eh_mw : mw_ok (get_meta_rec st g);
  eh_avail : 0 <= m_avail (get_meta_rec st g) < 2^32;
  eh_freed : 0 <= m_freed (get_meta_rec st g) < 2^32;
  eh_i : 0 <= i <= m_last_idx (get_meta_rec st g);

  eh_sc : m_sizeclass (get_meta_rec st g) < 48 \/ m_sizeclass (get_meta_rec st g) = 63;

  eh_next : forall nx, m_next (get_meta_rec st g) = Some nx -> meta_slot st nx;
  eh_head : forall h, active st (m_sizeclass (get_meta_rec st g)) = Some h -> meta_slot st h;
  eh_ctx : (forall j, 0 <= bounces st j < 256) /\ (m_sizeclass (get_meta_rec st g) < 48 -> 0 <= usage st (m_sizeclass (get_meta_rec st g)) < 2^64);

  eh_g50 : ntf_cond st g i = true -> m_next (get_meta_rec st g) <> None -> m_sizeclass (get_meta_rec st g) < 48;
  eh_g51 : ntf_cond st g i = false -> Z.lor (m_freed (get_meta_rec st g)) (m_avail (get_meta_rec st g)) = 0 -> m_sizeclass (get_meta_rec st g) < 48;

  eh_g1 : ntf_cond st g i = false -> Z.lor (m_freed (get_meta_rec st g)) (m_avail (get_meta_rec st g)) = 0 ->
          m_next (get_meta_rec st g) <> None -> active st (m_sizeclass (get_meta_rec st g)) = Some g
}.

Section ENTRY.
Context {HCEIL : HasCeiling}.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m : word -> option byte) (st : mstate) (g : aptr) (i lo : Z).
Local Notation mr := (get_meta_rec st g).
Local Notation sc := (m_sizeclass mr).
Local Notation mask := (Z.lor (m_freed mr) (m_avail mr)).
Local Notation maskw := (Z.lor (sxv (m_freed mr)) (sxv (m_avail mr))).
Local Notation sp' := (Z_to_bv 64 (bv_unsigned sp + -80)).
Local Notation G := (Z_to_bv 64 (conc st g)).
Local Notation SELF := (wz (sxv (2 ^ i))).

Hypothesis EH : entry_hyps st g i.
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOLE : lo <= bv_unsigned sp - 80.

#[using="i EH"] Lemma maskw_zero : maskw = 0 <-> mask = 0.
Proof. apply lor_sxv_zero; [apply (eh_freed _ _ _ EH) | apply (eh_avail _ _ _ EH)]. Qed.
#[using="Type"] Lemma maskw_range : 0 <= maskw < 2^64.
Proof. apply lor_range64; apply sxv_range. Qed.

#[using="Type"] Lemma ntf_cond_unfold :
  ntf_cond st g i = ((mask + bit i =? mask_upto (m_last_idx mr)) && okay_to_free st g)%bool.
Proof. reflexivity. Qed.

#[using="Type"] Lemma okf_unfold :
  okay_to_free st g =
    if m_freeable mr =? 0 then false
    else if (48 <=? sc) || (get_stride mr <? UNIT * size_class sc) then true
    else if m_maplen mr =? 0 then true
    else if negb (optr_eqb (m_next mr) (Some g)) then true
    else if negb (is_bouncing sc st) then true
    else if (9 * (m_last_idx mr + 1) <=? usage st sc) && (m_last_idx mr + 1 <? 20) then true else false.
Proof. reflexivity. Qed.

Ltac post_common MU WM MI ST FR MR m1 junk :=
  apply evt_done; exists m1, junk; split; [| exact (conj MU (conj WM (conj MI (conj ST (conj FR MR)))))].
End ENTRY.