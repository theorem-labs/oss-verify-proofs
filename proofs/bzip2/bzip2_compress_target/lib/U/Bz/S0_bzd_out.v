(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzDefs BzInv. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTables BzLemmasT BzLemmasMtf.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope bv_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section ACeilS1. Context {ACEIL__ : ACeil}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma shl32_shr30 : forall u, (0 <= u)%Z -> ((u * 4294967296) mod 18446744073709551616 / 1073741824 = 4 * (u mod 2^32))%Z.
Proof.
  intros u Hu. rewrite (Z.div_mod u (2^32)) at 1 by lia.
  rewrite Z.mul_add_distr_r. replace (2 ^ 32 * (u / 2 ^ 32) * 4294967296)%Z with ((u / 2^32) * 18446744073709551616)%Z by lia.
  rewrite Z.add_comm, Z.mod_add by lia. pose proof (Z.mod_pos_bound u (2^32) ltac:(lia)).
  rewrite Z.mod_small by lia.
  replace (u mod 2 ^ 32 * 4294967296)%Z with ((4 * (u mod 2^32)) * 1073741824)%Z by lia. now rewrite Z.div_mul by lia.
Qed.
(* [comment removed for export] *)
Lemma land255_range : forall x, (0 <= Z.land x 255 < 256)%Z.
Proof. intros. change 255%Z with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Record octx := OC {
  o_h : dsh; o_d : dsm; o_b : bzs; o_nbu0 : Z;       (* [comment removed for export] *)
  o_S : Z; o_snb : Z;                                (* [comment removed for export] *)
  o_ttw : list word; o_crcw : list word;             (* [comment removed for export] *)
  o_l16 : list byte; o_l4 : list byte; o_cf : list word;   (* [comment removed for export] *)
  o_g1 : word; o_s1v : word; o_SP : word; o_gp : word; o_tp : word;
  o_F : bvmap 5 word; o_fc : bv 32; o_Q : machine_state -> Prop; o_m0 : word -> option byte;
  o_j1 : list byte; o_j2 : list byte }.

Section Ctx.
  Variable c : octx.
  Notation h := (o_h c). Notation d := (o_d c). Notation b := (o_b c). Notation S := (o_S c). Notation snb := (o_snb c).
  Notation STRM := (sh_strm (o_h c)). Notation TT := (sm_tt (o_d c)). Notation L16 := (sm_ll16 (o_d c)). Notation L4 := (sm_ll4 (o_d c)).
  Notation DST := (bs_dst (o_b c)). Notation dlen := (bs_dlen (o_b c)). Notation n := (sh_n (o_h c)). Notation av0 := (bs_av (o_b c)).
 

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition WB : list ivl :=
    [(S, S + 68); (S + 1092, S + 1096); (S + 3152, S + 3196); (STRM, STRM + 44); (DST, DST + dlen)]%Z.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition bupd (av : Z) (tol toh : word) : bzs :=
    BZS (bs_src b) (bs_len b) (bs_ai b) (bs_til b) (bs_tih b) (bs_q1 b) (bs_dst b) (bs_dlen b) av tol toh (bs_q2 b)
        (bs_S b) (bs_bzalloc b) (bs_bzfree b) (bs_opaque b).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
End Ctx.
End ACeilS1.

Notation WBf := WB (only parsing). Notation WBs := WB (only parsing).

(* [comment removed for export] *)
Notation RR c ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s1 s3 s8 t3 t4 t5 t6 :=
  (mkR ra (o_SP c) (o_gp c) (o_tp c) t0 t1 t2 (Z_to_bv 64 (o_S c)) s1 a0 a1 a2 a3 a4 a5 a6 a7
       (Z_to_bv 64 (o_S c + 1096)) s3 (Z_to_bv 64 (o_S c + 2047))
       (Z_to_bv 64 1) (Z_to_bv 64 2) (Z_to_bv 64 (-1)) s8 (Z_to_bv 64 100000) (Z_to_bv 64 (o_S c + 64080)) (Z_to_bv 64 10) t3 t4 t5 t6) (only parsing).
Section ACeilS2. Context {ACEIL__ : ACeil}.


Section Conts.
  Variable c : octx.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
End Conts.
End ACeilS2.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
