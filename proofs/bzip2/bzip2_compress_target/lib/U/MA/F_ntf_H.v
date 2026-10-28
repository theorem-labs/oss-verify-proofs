(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac Image ZBridge SysStep Arr SFMisc.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast MallocTree.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec Require Import STree Malloc MallocCtrl.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require MallocKit_B MallocModel_B.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require MallocModel_B.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require F_ntf_C.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocKit_B OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocModel_B OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocModel_B.F_ntf_B OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_ntf_C. (* [comment removed for export] *) From Stdlib Require ZArith NArith List Lia Bool. From stdpp Require gmap. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run. From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Tac Image ZBridge SysStep Arr SFMisc. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require F_syscalls MallocRep F_malloc_free. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec Require STree Malloc MallocCtrl. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require MallocTree. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require MallocKit_B MallocModel_B. From Stdlib Require Lia. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ACeil RunW.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Import MallocKit_B3 F_ntf_F.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil RunW.
Section ACeilS1. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


(* [comment removed for export] *)
Definition ntf_cond (st : mstate) (g : aptr) (i : Z) : bool :=
  let mr := get_meta_rec st g in
  (Z.lor (m_freed mr) (m_avail mr) + bit i =? mask_upto (m_last_idx mr)) && okay_to_free st g.

(* [comment removed for export] *)
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
Definition AT (pc : Z) (R : bvmap 5 word) (ms' : machine_state) : Prop := ms' = MS R F (Z_to_bv 64 pc) fc None m1 (seg_rom asegs).

Definition entry_cases (ms' : machine_state) : Prop :=
  (* [comment removed for export] *)
  (ntf_cond st g i = false /\ mask <> 0 /\
   exists t0 t1 t2 a0 a3 a4 a5 a6 a7 t3 t4 t5 t6,
     AT 0x15e1c (mkR ra sp' gp tp t0 t1 t2 s0 s1 a0 SELF G a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) ms')
  \/ (* [comment removed for export] *)
  (ntf_cond st g i = false /\ mask = 0 /\
   exists t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
     AT 0x15dd4 (mkR ra sp' gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 sc) SELF G a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) ms')
  \/ (* [comment removed for export] *)
  (ntf_cond st g i = false /\ mask = 0 /\ active st sc = Some g /\
   exists t0 t1 t2 a0 a3 a4 a5 a6 a7 t3 t4 t5 t6,
     AT 0x15e1c (mkR ra sp' gp tp t0 t1 t2 s0 s1 a0 SELF G a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) ms')
  \/ (* [comment removed for export] *)
  (ntf_cond st g i = true /\ m_next mr = None /\ sc < 48 /\
   exists t0 t2 a3 a5 a6 t3 t4 t5 t6,
     AT 0x15b80 (mkR ra sp' gp tp t0 (Z_to_bv 64 sc) t2 s0 s1 (Z_to_bv 64 sc) SELF G a3 (Z_to_bv 64 CTX) a5 a6 (Z_to_bv 64 (m_last_idx mr)) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) ms')
  \/ (* [comment removed for export] *)
  (ntf_cond st g i = true /\ m_next mr = None /\ 48 <= sc /\
   exists t0 t2 a3 a5 a7 t3 t4 t5 t6,
     AT 0x15ba0 (mkR ra sp' gp tp t0 (Z_to_bv 64 sc) t2 s0 s1 (Z_to_bv 64 sc) SELF G a3 (Z_to_bv 64 CTX) a5 (Z_to_bv 64 (meta_word mr)) a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) ms')
  \/ (* [comment removed for export] *)
  (ntf_cond st g i = true /\ m_next mr = Some g /\ sc < 48 /\
   exists t0 t1 t2 a5 a6 a7 t3 t4 t5 t6,
     AT 0x15c70 (mkR ra sp' gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (sc + 10)) SELF G HD (Z_to_bv 64 CTX) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) ms')
  \/ (* [comment removed for export] *)
  (ntf_cond st g i = true /\ sc < 48 /\
   exists nx, m_next mr = Some nx /\ nx <> g /\
   exists t0 t1 t2 a5 a6 a7 t3 t4 t6,
     AT 0x15b38 (mkR ra sp' gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (sc + 10)) SELF G HD (Z_to_bv 64 CTX) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 (Z_to_bv 64 (conc st nx)) t6) ms').
End POST.

Definition entry_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : mstate) (g : aptr) (i lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists m1 junk,
    entry_cases ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st g i m1 ms'
    /\ munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
    /\ stk asegs m1 lo (bv_unsigned sp + -80)
    /\ rw_cells asegs m1 (bv_unsigned sp + -80) [CB 72 junk; C8 ra]
    /\ mrep st m1.

(* [comment removed for export] *)
Record entry_hyps (st : mstate) (g : aptr) (i : Z) : Prop := mkEH {
  eh_slot : meta_slot st g;
  eh_mw : mw_ok (get_meta_rec st g);
  eh_avail : 0 <= m_avail (get_meta_rec st g) < 2^32;
  eh_freed : 0 <= m_freed (get_meta_rec st g) < 2^32;
  eh_i : 0 <= i <= m_last_idx (get_meta_rec st g);
  (* [comment removed for export] *)
  eh_sc : m_sizeclass (get_meta_rec st g) < 48 \/ m_sizeclass (get_meta_rec st g) = 63;
  (* [comment removed for export] *)
  eh_next : forall nx, m_next (get_meta_rec st g) = Some nx -> meta_slot st nx;
  eh_head : forall h, active st (m_sizeclass (get_meta_rec st g)) = Some h -> meta_slot st h;
  eh_ctx : (forall j, 0 <= bounces st j < 256) /\ (m_sizeclass (get_meta_rec st g) < 48 -> 0 <= usage st (m_sizeclass (get_meta_rec st g)) < 2^64);
  (* [comment removed for export] *)
  eh_g50 : ntf_cond st g i = true -> m_next (get_meta_rec st g) <> None -> m_sizeclass (get_meta_rec st g) < 48;
  eh_g51 : ntf_cond st g i = false -> Z.lor (m_freed (get_meta_rec st g)) (m_avail (get_meta_rec st g)) = 0 -> m_sizeclass (get_meta_rec st g) < 48;
  (* [comment removed for export] *)
  eh_g1 : ntf_cond st g i = false -> Z.lor (m_freed (get_meta_rec st g)) (m_avail (get_meta_rec st g)) = 0 ->
          m_next (get_meta_rec st g) <> None -> active st (m_sizeclass (get_meta_rec st g)) = Some g
}.

Section ENTRY.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m : word -> option byte) (st : mstate) (g : aptr) (i lo : Z).
Local Notation mr := (get_meta_rec st g).
Local Notation sc := (m_sizeclass mr).
Local Notation mask := (Z.lor (m_freed mr) (m_avail mr)).
Local Notation maskw := (Z.lor (sxv (m_freed mr)) (sxv (m_avail mr))).
Local Notation sp' := (Z_to_bv 64 (bv_unsigned sp + -80)).
Local Notation G := (Z_to_bv 64 (conc st g)).
Local Notation SELF := (wz (sxv (2 ^ i))).
Local Notation POST := (entry_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st g i lo m).

Hypothesis EH : entry_hyps st g i.
Hypothesis MI0 : mem_inv asegs m.
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOLE : lo <= bv_unsigned sp - 80.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma ntf_cond_unfold :
  ntf_cond st g i = ((mask + bit i =? mask_upto (m_last_idx mr)) && okay_to_free st g)%bool.
Proof. reflexivity. Qed.

Lemma okf_unfold :
  okay_to_free st g =
    if m_freeable mr =? 0 then false
    else if (48 <=? sc) || (get_stride mr <? UNIT * size_class sc) then true
    else if m_maplen mr =? 0 then true
    else if negb (optr_eqb (m_next mr) (Some g)) then true
    else if negb (is_bouncing sc st) then true
    else if (9 * (m_last_idx mr + 1) <=? usage st sc) && (m_last_idx mr + 1 <? 20) then true else false.
Proof. reflexivity. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
End ENTRY.


End ACeilS1.
