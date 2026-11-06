(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.punycode.lib.Lib Require Import Tac Image SysStep ZBridge.
From OSSVerify.Proofs.openssl.punycode.lib.Lib Require Import StoreFast.
From OSSVerify.Proofs.openssl.punycode.lib.P Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.openssl.punycode.lib.U Require Import Fz_tac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Abbreviation mem := (word -> option byte) (only parsing).

(* [comment removed for export] *)

Definition cmp_frame (jf : list byte) (f3 f2 f1 f0 fra : word) : list cell := [CB 8 jf; C8 f3; C8 f2; C8 f1; C8 f0; C8 fra].

(* [comment removed for export] *)
Lemma cm_w1 : forall (S lo n : Z) (ra gp tp u0 u1 u2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 : word)
    F fc (m : mem) (lv : byte),
  stk usegs m lo S -> 0x354000 <= lo -> lo + 0x1000 <= S -> S < 2^63 -> mem_inv usegs m -> 0 < n < 2^64 ->
  rw_cells usegs m 0x31ee88 [C8 (Z_to_bv 64 0xe1b4c)] -> rw_cells usegs m 0x31da30 [C8 (Z_to_bv 64 0xe1b4c)] ->
  rw_cells usegs m 0x32f7d0 [C1 lv] ->
  evt usegs (fun ms => exists (m1 : mem) (jf : list byte) (lv' : byte) (a1' a2' a3' : word),
      ms = MS (mkR (Z_to_bv 64 0xe1bc8) (Z_to_bv 64 (S + -48)) gp tp u0 u1 u2 (Z_to_bv 64 S) a2 (Z_to_bv 64 n) a1' a2' a3' a4 a5 a6 a7
                   a1 (Z_to_bv 64 n) s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6) F (Z_to_bv 64 0x2b2518) fc None m1 (seg_rom usegs)
      /\ munch [(S + -48, S); (0x32f7d0, 0x32f7d1)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1 /\ stk usegs m1 lo (S + -48)
      /\ rw_cells usegs m1 (S + -48) (cmp_frame jf s3 s2 s1 s0 ra) /\ rw_cells usegs m1 0x32f7d0 [C1 lv'])
    (MS (mkR ra (Z_to_bv 64 S) gp tp u0 u1 u2 s0 s1 (Z_to_bv 64 n) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
        F (Z_to_bv 64 0xe1b4c) fc None m (seg_rom usegs)).
Proof.
  intros until lv. intros ST LOS LO SPH MI Hn HK GT LT.
  unfold cmp_frame.
  pose proof (munch_refl [(S + -48, S); (0x32f7d0, 0x32f7d1)] m) as MU. pose proof (wmono_refl usegs m) as WM.
  carve_frame 48%nat ST.
  apply (rw_cells_split_CB usegs _ _ [] 48 _ [] [8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity].
  cbn [mk_CB_cells app] in FR.
  xs_to 0xe1bb0%Z.

  if_cases KA; zify_cond KA; [exfalso; lia|]. clear KA.
  xs_to 0xe1bb0%Z. xs.

  if_cases KB.
  - xs_to 0x2b2518%Z. apply evt_done. do 6 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR| exact LT].
  - xs_to 0x2b2518%Z. apply evt_done. do 6 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR| exact LT].
Qed.

(* [comment removed for export] *)
Lemma cm_w2 : forall (S lo A r : Z) (gp tp u0 u1 u2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 : word)
    F fc (m : mem) (jf : list byte) (f3 f2 f1 f0 : word),
  stk usegs m lo (S + -48) -> 0x354000 <= lo -> lo + 0x1000 <= S -> S < 2^63 -> mem_inv usegs m -> 0 < A < 2^64 ->
  rw_cells usegs m (S + -48) (cmp_frame jf f3 f2 f1 f0 (Z_to_bv 64 r)) ->
  evt usegs (fun ms =>
      ms = MS (mkR (Z_to_bv 64 r) (Z_to_bv 64 S) gp tp u0 u1 u2 f0 f1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7
                   f2 f3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6) F (ret_pc (Z_to_bv 64 r)) fc None m (seg_rom usegs)
      /\ stk usegs m lo S)
    (MS (mkR (Z_to_bv 64 0xe1bc8) (Z_to_bv 64 (S + -48)) gp tp u0 u1 u2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
        F (Z_to_bv 64 0xe1bc8) fc None m (seg_rom usegs)).
Proof.
  intros until f0. intros ST LOS LO SPH MI HA FR.
  unfold cmp_frame in *.
  xs. if_cases KA; zify_cond KA; [| exfalso; lia]. clear KA.
  do 6 xs.
  release_frame FR ST S.
  xs.
  apply evt_done. split; [reflexivity| exact ST].
Qed.

(* [comment removed for export] *)
Lemma cf_w : forall (S lo : Z) (ra gp tp u0 u1 u2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 : word)
    F fc (m : mem),
  stk usegs m lo S -> 0x354000 <= lo -> lo + 0x1000 <= S -> S < 2^63 -> mem_inv usegs m ->
  rw_cells usegs m 0x31ee98 [C8 (Z_to_bv 64 0xe1ef4)] -> rw_cells usegs m 0x31da40 [C8 (Z_to_bv 64 0xe1ef4)] ->
  evt usegs (fun ms => exists (m1 : mem) (t1' a3' a4' : word),
      ms = MS (mkR ra (Z_to_bv 64 S) gp tp u0 t1' u2 s0 s1 a0 a1 a2 a3' a4' a5 a6 a7
                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6) F (Z_to_bv 64 0x2b23d8) fc None m1 (seg_rom usegs)
      /\ munch [(S + -16, S)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1 /\ stk usegs m1 lo S)
    (MS (mkR ra (Z_to_bv 64 S) gp tp u0 u1 u2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
        F (Z_to_bv 64 0xe1ef4) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros ST LOS LO SPH MI HK GT.
  pose proof (munch_refl [(S + -16, S)] m) as MU. pose proof (wmono_refl usegs m) as WM.
  carve_frame 16%nat ST.
  apply (rw_cells_split_CB usegs _ _ [] 16 _ [] [8; 8]%nat) in FR; [| reflexivity].
  cbn [mk_CB_cells app] in FR.
  xs_to 0xe1f30%Z. xs.
  release_frame FR ST S.
  xs.
  apply evt_done. do 4 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption| exact ST].
Qed.

(* [comment removed for export] *)
Definition fzp_frame (j0 jc jo : list byte) (w16 f2 f1 f0 fra : word) : list cell :=
  [CB 12 j0; CB 16 jc; C4 w16; CB 64 jo; C8 f2; C8 f1; C8 f0; C8 fra].

Lemma fzp_w1 : forall (usp lo D n : Z) (ra gp tp u0 u1 u2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 : word)
    F fc (m : mem),
  stk usegs m lo usp -> 0x354000 <= lo -> lo + 0x1000 <= usp -> usp < 2^63 -> mem_inv usegs m ->
  evt usegs (fun ms => exists (m1 : mem) (j0 jc jo : list byte),
      ms = MS (mkR (Z_to_bv 64 0xe1ac0) (Z_to_bv 64 (usp + -128)) gp tp u0 u1 u2 s0 (Z_to_bv 64 n) (Z_to_bv 64 (n + 1)) (Z_to_bv 64 0x2ce58) (Z_to_bv 64 29)
                   a3 a4 a5 a6 a7 (Z_to_bv 64 D) s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6) F (Z_to_bv 64 0xe1b4c) fc None m1 (seg_rom usegs)
      /\ munch [(usp + -128, usp)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1 /\ stk usegs m1 lo (usp + -128)
      /\ rw_cells usegs m1 (usp + -128) (fzp_frame j0 jc jo (Z_to_bv 64 16) s2 s1 s0 ra))
    (MS (mkR ra (Z_to_bv 64 usp) gp tp u0 u1 u2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
        F (Z_to_bv 64 0xe1a7c) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros ST LOS LO SPH MI.
  unfold fzp_frame.
  pose proof (munch_refl [(usp + -128, usp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
  carve_frame 128%nat ST.
  apply (rw_cells_split_CB usegs _ _ [] 128 _ [] [12; 16; 4; 64; 8; 8; 8; 8]%nat) in FR; [| reflexivity].
  cbn [mk_CB_cells app] in FR.
  xs_to 0xe1b4c%Z.
  apply evt_done. do 4 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST| exact FR].
Qed.

(* [comment removed for export] *)
Lemma fzp_w2 : forall (usp D n A : Z) (gp tp u0 u1 u2 s0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 : word)
    F fc (m : mem),
  0 < A < 2^64 -> usp < 2^63 -> 0x354000 <= usp + -128 ->
  evt usegs (fun ms =>
      ms = MS (mkR (Z_to_bv 64 0xe1ae0) (Z_to_bv 64 (usp + -128)) gp tp u0 u1 u2 (Z_to_bv 64 A) (Z_to_bv 64 n) (Z_to_bv 64 D) (Z_to_bv 64 n)
                   (Z_to_bv 64 (usp + -96)) (Z_to_bv 64 (usp + -100))
                   a4 a5 a6 a7 (Z_to_bv 64 D) s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6) F (Z_to_bv 64 0x215490) fc None m (seg_rom usegs))
    (MS (mkR (Z_to_bv 64 0xe1ac0) (Z_to_bv 64 (usp + -128)) gp tp u0 u1 u2 s0 (Z_to_bv 64 n) (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 D) s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
        F (Z_to_bv 64 0xe1ac0) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros HA SPH SPL.
  xs. if_cases KA; zify_cond KA; [exfalso; lia|]. clear KA.
  xs_to 0x215490%Z.
  apply evt_done. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma fzp_w3 : forall (usp D n A : Z) (ra gp tp u0 u1 u2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 : word)
    F fc (m : mem),
  evt usegs (fun ms =>
      ms = MS (mkR (Z_to_bv 64 0xe1af4) (Z_to_bv 64 (usp + -128)) gp tp u0 u1 u2 (Z_to_bv 64 A) (Z_to_bv 64 n) (Z_to_bv 64 A) (Z_to_bv 64 D)
                   (Z_to_bv 64 n) a3 a4 a5 a6 a7 (Z_to_bv 64 D) s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6) F (Z_to_bv 64 0x2bc8ec) fc None m (seg_rom usegs))
    (MS (mkR ra (Z_to_bv 64 (usp + -128)) gp tp u0 u1 u2 (Z_to_bv 64 A) (Z_to_bv 64 n) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 D) s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
        F (Z_to_bv 64 0xe1ae0) fc None m (seg_rom usegs)).
Proof.
  intros until m.
  xs_to 0x2bc8ec%Z.
  apply evt_done. reflexivity.
Qed.

(* [comment removed for export] *)
Definition a2p_frame (jA jp jbuf jpad : list byte) (f11 f10 f9 f8 f7 f6 f5 f4 f3 f2 f1 f0 fra : word) : list cell :=
  [CB 24 jA; CB 56 jp; CB 2048 jbuf; CB 8 jpad; C8 f11; C8 f10; C8 f9; C8 f8; C8 f7; C8 f6; C8 f5; C8 f4; C8 f3; C8 f2; C8 f1; C8 f0; C8 fra].

Lemma fzp_w4a : forall (S A n : Z) (lo : Z) (ra gp tp u0 u1 u2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 : word)
    F fc (m : mem) (bz : byte),
  stk usegs m lo S -> 0x354000 <= lo -> lo + 0x1000 <= S - 2240 -> S + 128 < 2^63 -> mem_inv usegs m ->
  0 < A -> 0 <= n -> A + n < 2^63 -> rw_cells usegs m (A + n) [C1 bz] -> (A + n + 1 <= lo \/ S <= A + n) ->
  evt usegs (fun ms => exists (m1 : mem) (jA jp jbuf jpad : list byte),
      ms = MS (mkR (Z_to_bv 64 0x2158e8) (Z_to_bv 64 (S + -2240)) gp tp u0 u1 u2 (Z_to_bv 64 S) (Z_to_bv 64 (-1)) (Z_to_bv 64 (S + -2216)) (Z_to_bv 64 (S + 12))
                   (Z_to_bv 64 16) (Z_to_bv 64 0) a4 a5 a6 a7 s2 (Z_to_bv 64 A) s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
              F (Z_to_bv 64 0x128b34) fc None m1 (seg_rom usegs)
      /\ munch [(S + -2240, S); (A + n, A + n + 1)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1 /\ stk usegs m1 lo (S + -2240)
      /\ rw_cells usegs m1 (S + -2240) (a2p_frame jA jp jbuf jpad s11 s10 s9 s8 s7 s6 s5 s4 s3 s2
                                          (Z_to_bv 64 (A + n)) (Z_to_bv 64 A) (Z_to_bv 64 0xe1b18))
      /\ rw_cells usegs m1 (A + n) [C1 (Z_to_bv 8 0)])
    (MS (mkR ra (Z_to_bv 64 S) gp tp u0 u1 u2 (Z_to_bv 64 A) (Z_to_bv 64 n) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
        F (Z_to_bv 64 0xe1af4) fc None m (seg_rom usegs)).
Proof.
  intros until bz. intros ST LOS LO SPH MI HA Hn HAn NUL SEP.
  unfold a2p_frame.
  pose proof (munch_refl [(S + -2240, S); (A + n, A + n + 1)] m) as MU. pose proof (wmono_refl usegs m) as WM.
  xs. rewrite (zb_lxor_ones A) by lia.
  xs. if_cases KB; zify_cond KB; [exfalso; lia|]. clear KB.
  xs. remember (A + n) as e eqn:Ee. xs.
  xs_to 0x21588c%Z.
  carve_frame 2240%nat ST.
  apply (rw_cells_split_CB usegs _ _ [] 2240 _ [] [24; 56; 2048; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity].
  cbn [mk_CB_cells app] in FR.
  xs_to 0x2158d0%Z. xs.
  if_cases KA; zify_cond KA; [exfalso; lia|]. clear KA.
  xs_to 0x128b34%Z.
  apply evt_done. do 5 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR| assumption].
Qed.
