(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Tac Image ZBridge SysStep.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes Decode Arr SFMisc.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Image OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SysStep OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes.ITree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Decode OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Arr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SFMisc.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast MallocTree MallocKit_A.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Import MallocKit_AB.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil RunW.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Section ACeilS1. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
End ACeilS1.


Ltac raw_store_finish A bs' FR ST MU WM SOK :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
    replace (write_to_mem mX a bs) with (write_to_mem mX (wa A) bs')
      by (f_equal; try reflexivity; try (rewrite le1_lit by lia; reflexivity); unfold wa, CTX; f_equal; lia);
    let L := fresh "LEN" in
    assert (L : Z.of_nat (length bs') = Z.of_nat (length bs')) by reflexivity;
    rewrite ?length_le8, ?length_le4, ?length_le2 in L at 1; cbn [length] in L;
    apply (rw_cells_frame asegs mX _ _ A bs') in FR; [| unfold CTX; lia | rewrite <- L; unfold CTX; lia | rewrite <- L; unfold CTX; cbn [cells_size csize Nat.add]; lia];
    apply (stk_write asegs mX _ _ A bs') in ST; [| unfold CTX; lia | rewrite <- L; unfold CTX; lia];
    apply (munch_write _ _ mX A bs') in MU; [| unfold CTX; lia | rewrite <- L; unfold CTX; lia | rewrite <- L; unfold CTX; cbn [inside]; lia];
    apply (wmono_write asegs _ mX (wa A) bs') in WM;
    lazymatch goal with HI : mem_inv asegs mX |- _ =>
      apply (mem_inv_store asegs mX (wa A) bs') in HI;
      [| first [ exact SOK | rewrite <- ?L; replace (wa A) with a by (unfold wa, CTX; f_equal; lia); exact SOK ] ]
    end;
    clear L SOK;
    let m' := fresh "m" in remember (write_to_mem mX (wa A) bs') as m' eqn:Em'; clear Em'
  end.
Section ACeilS2. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma unmap_seqs_empty st : unmap_seqs (upd_ctx (fun c => set_unmap_seq_map ∅ c) st) = zeros 32.
Proof. reflexivity. Qed.
End ACeilS2.


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Import Malloc_fp.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Import MallocKit_A2.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec Require StrFun.
Section ACeilS3. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


Definition big_ml (n : Z) : Z := Z.land ((n + IB + UNIT + 4095) / 4096) (2^52 - 1).
Definition big_meta (rid : N) (n : Z) : meta := mkMeta None None (Some (rid, 0)) 0 0 0 1 63 (big_ml n).
Definition big_metaA (rid : N) : meta := mkMeta None None (Some (rid, 0)) 0 0 0 0 0 0.
(* [comment removed for export] *)
Definition big_st (st : mstate) (g : aptr) (rid : N) (n v : Z) : mstate :=
  upd_ctx (set_mmap_counter v)
    (put_meta g (big_meta rid n)
      (put_group (rid, 0) (Some g) 0 (hdr_havoc (rid, 0) (put_meta g (big_metaA rid) st)))).

Lemma big_ml_eq n : 0 <= n < 2^32 -> big_ml n = (n + 4115) / 4096.
Proof.
  intros Hn. unfold big_ml, IB, UNIT. change (2^52 - 1) with (Z.ones 52). rewrite Z.land_ones by lia.
  replace (n + 4 + 16 + 4095) with (n + 4115) by lia. apply Z.mod_small. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma cell_read_hdr_havoc_fresh : forall st b o,
  (s_shadow st) !! (fst b) = None -> snd b mod 16 = 0 -> 0 <= o < 12 ->
  exists h, cell_read (get_shadow (hdr_havoc b st) (fst b)) (snd b + o) = Unknown h.
Proof.
  intros st b o SH B16 Ho. unfold hdr_havoc, get_shadow, upd_shadow. cbn [s_shadow set_shadow].
  rewrite lookup_insert_eq. cbn [default from_option id]. unfold get_shadow. rewrite SH. cbn [default from_option id r_cells r_hav r_havp shadow0].
  unfold cell_read. cbn [r_cells r_hav r_havp]. rewrite !lookup_empty.
  replace ((snd b + o) / 16) with (snd b / 16) by (Z.div_mod_to_equations; lia).
  rewrite lookup_insert_eq. cbn [default from_option id]. unfold hav_add. cbn.
  replace ((snd b + o) mod 16) with o by (Z.div_mod_to_equations; lia).
  replace (o <? 12) with true by (symmetry; apply Z.ltb_lt; lia). cbn. eexists. reflexivity.
Qed.

(* [comment removed for export] *)

Lemma meta_word_big_range rid n : 0 <= n < 2^32 -> 0 <= meta_word (big_meta rid n) < 2^64.
Proof.
  intros Hn. unfold meta_word, big_meta. cbn [m_last_idx m_freeable m_sizeclass m_maplen]. rewrite big_ml_eq by lia.
  Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

Section SUCC.
Variables (st : mstate) (m : mem) (g : aptr) (rid : N) (x n c lo : Z).
Let G := conc st g.
Hypothesis MR : mrep st m.
Hypothesis TK : ticks_ok st.
Hypothesis G0 : get_meta_rec st g = meta0.
Hypothesis MSL : meta_slot st g.
Hypothesis RR : (s_regions st) !! rid = Some (mkRegion RKGroup x (n + IB + UNIT)).
Hypothesis GN : forall off, (s_groups st) !! (rid, off) = None.
Hypothesis AN : forall off, (s_areas st) !! (rid, off) = None.
Hypothesis SHN : (s_shadow st) !! rid = None.
Hypothesis HC : c_mmap_counter (ctx st) = c.
Hypothesis CR : 0 <= c < 2^32.
Hypothesis NR : MMAP_THRESHOLD <= n < 2^32.
Hypothesis CLO : alloc_ceiling <= lo.

(* [comment removed for export] *)
End SUCC.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

End ACeilS3.
