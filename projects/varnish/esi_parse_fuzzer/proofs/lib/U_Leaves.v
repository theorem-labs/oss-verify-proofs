(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import ImgU RU_mkfg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.

Definition memcpy_entry := 0x2aff4.

Definition memcpy_post_z (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (D SRC n : Z) (src : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(D, D + n)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ rw_cells rsegs m' D [CB (length src) src]
    /\ bytes_at rsegs m' SRC src.

(* [comment removed for export] *)
Lemma memcpy_spec_z : forall ra sp gp tp t0 t1 t2 s0 s1 (D SRC n : Z) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (src junk : list byte),
  Z.of_nat (length src) = n ->
  bytes_at rsegs m SRC src ->
  rw_cells rsegs m D [CB (length src) junk] ->
  (SRC + n <= D \/ D + n <= SRC) ->
  D < 2^64 -> SRC < 2^64 ->
  mem_inv rsegs m ->
  evt rsegs (memcpy_post_z ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D SRC n src m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 SRC) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 memcpy_entry) fc None m (seg_rom rsegs)).
Proof.
  intros until junk. intros LEN BS DST SEP DHI SHI MI. subst n.
  pose proof (bytes_at_bound _ _ _ _ BS) as B1.
  pose proof (rw_cells_bound _ _ _ _ DST) as B2. cbn [cells_size csize Nat.add] in B2.
  assert (LB : Z.of_nat (length src) < 2^64) by lia.
  assert (U0 : bv_unsigned (Z_to_bv 64 D) = D) by (apply unsigned_lit; lia).
  assert (U1 : bv_unsigned (Z_to_bv 64 SRC) = SRC) by (apply unsigned_lit; lia).
  assert (U2 : bv_unsigned (Z_to_bv 64 (Z.of_nat (length src))) = Z.of_nat (length src)) by (apply unsigned_lit; lia).
  eapply evt_mono.
  { apply (memcpy_spec ra sp gp tp t0 t1 t2 s0 s1 _ _ _ a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m src junk);
        rewrite ?U0, ?U1, ?U2; [exact BS | lia | rewrite Nat2Z.id; exact DST | lia | exact MI]. }
  intros ms' PO. unfold memcpy_post in PO. unfold memcpy_post_z.
  (first [ dex15 PO as x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 m'; dand6 PO as E MU WM MI' RW BS' | dand21 PO as x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 m' E MU WM MI' RW BS' | destruct PO as (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & m' & E & MU & WM & MI' & RW & BS') ]).
  rewrite ?U0, ?U1, ?U2 in *. rewrite Nat2Z.id in RW.
  exists x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, m'.
  split; [exact E|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact RW| exact BS'].
Qed.

(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import RU_mz6g.
Local Open Scope Z_scope.

Definition memset_entry : Z := 0x2b3f8.

Definition memset_post_z (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (D c n : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(D, D + n)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ rw_cells rsegs m' D [CB (Z.to_nat n) (repeat (Z_to_bv 8 (c mod 256)) (Z.to_nat n))].

Lemma memset_spec_z : forall ra sp gp tp t0 t1 t2 s0 s1 (D c n : Z) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (junk : list byte),
  rw_cells rsegs m D [CB (Z.to_nat n) junk] ->
  0 <= n -> 0 <= c < 2^64 -> D + n < 2^64 ->
  mem_inv rsegs m ->
  evt rsegs (memset_post_z ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D c n m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 c) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 memset_entry) fc None m (seg_rom rsegs)).
Proof.
  intros until junk. intros DST N0 C DHI MI.
  pose proof (rw_cells_bound _ _ _ _ DST) as B2. cbn [cells_size csize Nat.add] in B2.
  rewrite Nat.add_0_r, Z2Nat.id in B2 by lia.
  assert (U0 : bv_unsigned (Z_to_bv 64 D) = D) by (apply unsigned_lit; lia).
  assert (U1 : bv_unsigned (Z_to_bv 64 c) = c) by (apply unsigned_lit; lia).
  assert (U2 : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  eapply evt_mono.
  { apply (memset_spec ra sp gp tp t0 t1 t2 s0 s1 _ _ _ a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m junk);
      rewrite ?U0, ?U2; [exact DST | exact MI]. }
  intros ms' PO. unfold memset_post in PO. unfold memset_post_z.
  (first [ dex15 PO as x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 m'; dand5 PO as E MU WM MI' RW | dand20 PO as x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 m' E MU WM MI' RW | destruct PO as (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & m' & E & MU & WM & MI' & RW) ]).
  rewrite ?U0, ?U1, ?U2 in *.
  exists x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, m'.
  split; [exact E|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. exact RW.
Qed.
