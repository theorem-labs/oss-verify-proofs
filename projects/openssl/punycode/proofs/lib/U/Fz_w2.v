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
From OSSVerify.Proofs.openssl.punycode.lib.U Require Import Fz_tac Fz_w1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Abbreviation mem := (word -> option byte) (only parsing).

Lemma land254_even : forall x, bv_unsigned (Z_to_bv 8 (Z.land x 254)) mod 2 = 0.
Proof.
  intros x. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with (2^8).
  rewrite <- Z.land_ones by lia. rewrite <- Z.land_assoc. change (Z.land 254 (Z.ones 8)) with 254.
  rewrite <- (Z.land_ones _ 1) by lia. rewrite <- Z.land_assoc. change (Z.land 254 (Z.ones 1)) with 0. apply Z.land_0_r.
Qed.

(* [comment removed for export] *)
Definition pkp_cells (out : Z) (j5 j7 : list byte) (eb : byte) : list cell :=
  [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 out); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 16); CB 8 j5; C1 eb; CB 7 j7].
(* [comment removed for export] *)
Definition z32_frame (jz : list byte) (f1 f0 fra : word) : list cell := [CB 8 jz; C8 f1; C8 f0; C8 fra].

Lemma land7_al : forall x, 0 <= x -> x mod 8 = 0 -> Z.land x 7 = 0.
Proof. intros x Hx H. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. exact H. Qed.

Lemma a2p_w4b : forall (L lo pk out : Z) (gp tp u0 u1 u2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 : word)
    F fc (m : mem) (jp : list byte),
  stk usegs m lo L -> 0x354000 <= lo -> lo + 0x1000 <= L -> L < 2^63 -> mem_inv usegs m ->
  L <= pk -> pk + 56 < 2^63 -> pk mod 8 = 0 -> 0 < out < 2^64 -> rw_cells usegs m pk [CB 56 jp] ->
  evt usegs (fun ms => exists (m1 : mem) (jf jz j5 j7 : list byte) (eb : byte) (u1' a3' a4' a5' a6' : word),
      ms = MS (mkR (Z_to_bv 64 0xe1c38) (Z_to_bv 64 (L + -80)) gp tp u0 u1' u2 (Z_to_bv 64 (L + -48)) (Z_to_bv 64 40) (Z_to_bv 64 40) (Z_to_bv 64 0x255ff)
                   (Z_to_bv 64 110) a3' a4' a5' a6' a7 s2 (Z_to_bv 64 0) s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
              F (Z_to_bv 64 0xe1b4c) fc None m1 (seg_rom usegs)
      /\ munch [(L + -80, L); (pk, pk + 56)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1 /\ stk usegs m1 lo (L + -80)
      /\ rw_cells usegs m1 (L + -48) (cmp_frame jf s3 s2 s1 s0 (Z_to_bv 64 0x2158e8))
      /\ rw_cells usegs m1 (L + -80) (z32_frame jz (Z_to_bv 64 pk) (Z_to_bv 64 L) (Z_to_bv 64 0x128c10))
      /\ rw_cells usegs m1 pk (pkp_cells out j5 j7 eb) /\ bv_unsigned eb mod 2 = 0)
    (MS (mkR (Z_to_bv 64 0x2158e8) (Z_to_bv 64 L) gp tp u0 u1 u2 s0 s1 (Z_to_bv 64 pk) (Z_to_bv 64 out) (Z_to_bv 64 16) (Z_to_bv 64 0)
             a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
        F (Z_to_bv 64 0x128b34) fc None m (seg_rom usegs)).
Proof.
  intros until jp. intros ST LOS LO SPH MI PKL PKH PK8 HO CP.
  unfold cmp_frame, z32_frame, pkp_cells.
  apply (rw_cells_split_CB usegs _ _ [] 56 _ [] [8;8;8;8;8;8;1;7]%nat) in CP; [| reflexivity].
  cbn [mk_CB_cells app] in CP.
  pose proof (munch_refl [(L + -80, L); (pk, pk + 56)] m) as MU. pose proof (wmono_refl usegs m) as WM.
  assert (EA : Z.land pk 7 = 0) by (apply land7_al; lia).
  carve_frame 16%nat ST.
  apply (rw_cells_split_CB usegs _ _ [] 16 _ [] [8; 8]%nat) in FR; [| reflexivity].
  cbn [mk_CB_cells app] in FR.
  xs_to 0x128b44%Z. xs.
  if_cases KA; zify_cond KA; [exfalso; lia|]. clear KA.
  xs. xs.
  if_cases KB; zify_cond KB; [exfalso; lia|]. clear KB.
  xs. rewrite EA. xs.
  xs_to 0x128ba8%Z.
  xs.
  release_frame FR ST L.
  xs_to 0x128bc8%Z.
  carve_frame 48%nat ST.
  apply (rw_cells_split_CB usegs _ _ [] 48 _ [] [8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity].
  cbn [mk_CB_cells app] in FR.
  xs_to 0x128be8%Z.
  xs. rewrite EA. xs.
  xs_to 0xe1c1c%Z.
  carve_frame 32%nat ST.
  apply (rw_cells_split_CB usegs _ _ [] 32 _ [] [8; 8; 8; 8]%nat) in FR0; [| reflexivity].
  cbn [mk_CB_cells app] in FR0.
  xs_to 0xe1b4c%Z.
  apply evt_done. do 11 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|]. split; [exact FR0|].
  split; [exact CP| apply land254_even].
Qed.

(* [comment removed for export] *)
Lemma zl_w : forall (Zs lo q : Z) (ra gp tp u0 u1 u2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 : word)
    F fc (m : mem) (jz : list byte) (f1 f0 fra : word),
  stk usegs m lo Zs -> 0x354000 <= lo -> lo <= Zs -> Zs + 32 < 2^63 -> mem_inv usegs m -> 0 < q < 2^64 ->
  rw_cells usegs m Zs (z32_frame jz f1 f0 fra) ->
  evt usegs (fun ms => exists (t1' : word),
      ms = MS (mkR fra (Z_to_bv 64 (Zs + 32)) gp tp u0 t1' u2 f0 f1 (Z_to_bv 64 q) (Z_to_bv 64 0) (Z_to_bv 64 40) a3 a4 a5 a6 a7
                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6) F (Z_to_bv 64 0x2bce6c) fc None m (seg_rom usegs)
      /\ stk usegs m lo (Zs + 32))
    (MS (mkR ra (Z_to_bv 64 Zs) gp tp u0 u1 u2 s0 (Z_to_bv 64 40) (Z_to_bv 64 q) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
        F (Z_to_bv 64 0xe1c38) fc None m (seg_rom usegs)).
Proof.
  intros until fra. intros ST LOS LO SPH MI HQ FR.
  unfold z32_frame in *.
  xs. if_cases KA; zify_cond KA; [exfalso; lia|]. clear KA.
  xs_to 0xe1c50%Z. xs.
  release_frame FR ST (Zs + 32).
  xs.
  apply evt_done. eexists. split; [reflexivity| exact ST].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pkp_cells1 (out q : Z) (j7 : list byte) (eb : byte) : list cell :=
  [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 out); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 16); C8 (Z_to_bv 64 q); C1 eb; CB 7 j7].

Lemma a2p_w6 : forall (L lo pk out q : Z) (ra gp tp u0 u1 u2 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 : word)
    F fc (m : mem) (jf j5 j7 : list byte) (eb : byte) (f3 f2 f1 f0 : word),
  stk usegs m lo (L + -48) -> 0x354000 <= lo -> lo + 0x1000 <= L -> L < 2^63 -> mem_inv usegs m ->
  L <= pk -> pk + 56 < 2^63 -> 0 < q < 2^64 ->
  rw_cells usegs m (L + -48) (cmp_frame jf f3 f2 f1 f0 (Z_to_bv 64 0x2158e8)) ->
  rw_cells usegs m pk (pkp_cells out j5 j7 eb) ->
  evt usegs (fun ms => exists (m1 : mem),
      ms = MS (mkR (Z_to_bv 64 0x2158e8) (Z_to_bv 64 L) gp tp u0 u1 u2 f0 f1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
                   f2 f3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6) F (Z_to_bv 64 0x2158ec) fc None m1 (seg_rom usegs)
      /\ munch [(pk + 40, pk + 48)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1 /\ stk usegs m1 lo L
      /\ rw_cells usegs m1 pk (pkp_cells1 out q j7 eb))
    (MS (mkR ra (Z_to_bv 64 (L + -48)) gp tp u0 u1 u2 (Z_to_bv 64 L) (Z_to_bv 64 pk) (Z_to_bv 64 q) a1 a2 a3 a4 a5 a6 a7
             s2 (Z_to_bv 64 0) s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
        F (Z_to_bv 64 0x128c10) fc None m (seg_rom usegs)).
Proof.
  intros until f0. intros ST LOS LO SPH MI PKL PKH HQ FR CP.
  unfold cmp_frame, pkp_cells, pkp_cells1 in *.
  pose proof (munch_refl [(pk + 40, pk + 48)] m) as MU. pose proof (wmono_refl usegs m) as WM.
  xs. xs. if_cases KA; zify_cond KA; [exfalso; lia|]. clear KA.
  xs_to 0x128c98%Z.
  xs.
  release_frame FR ST L.
  xs. xs.
  apply evt_done. eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST| exact CP].
Qed.

(* [comment removed for export] *)
Lemma a2p_w7 : forall (S lo q : Z) (ra gp tp u0 u1 u2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 : word)
    F fc (m : mem),
  stk usegs m lo (S + -2240) -> 0x354000 <= lo -> lo + 0x1000 <= S + -2240 -> S < 2^63 -> mem_inv usegs m ->
  0 < q -> q + 8 < 2^63 -> (q + 8 <= lo \/ S <= q) -> S mod 8 = 0 -> q mod 8 = 0 ->
  rw_cells usegs m (S + -2176) [C8 (Z_to_bv 64 q)] -> rw_cells usegs m q [C8 (Z_to_bv 64 0)] ->
  evt usegs (fun ms => exists (m1 : mem) (jf : list byte),
      ms = MS (mkR (Z_to_bv 64 0x1295c8) (Z_to_bv 64 (S + -2288)) gp tp u0 u1 u2 (Z_to_bv 64 (S + -2240)) (Z_to_bv 64 (S + -2216)) (Z_to_bv 64 q)
                   (Z_to_bv 64 0x255ff) (Z_to_bv 64 540) a3 a4 a5 a6 a7 (Z_to_bv 64 0x255ff) (Z_to_bv 64 0) s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
              F (Z_to_bv 64 0xe1ef4) fc None m1 (seg_rom usegs)
      /\ munch [(S + -2288, S + -2240)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1 /\ stk usegs m1 lo (S + -2288)
      /\ rw_cells usegs m1 (S + -2288) (cmp_frame jf s3 s2 s1 (Z_to_bv 64 S) (Z_to_bv 64 0x215b98)))
    (MS (mkR ra (Z_to_bv 64 (S + -2240)) gp tp u0 u1 u2 (Z_to_bv 64 S) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
        F (Z_to_bv 64 0x215b8c) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros ST LOS LO SPH MI HQ HQ2 SEP S8 Q8 CS CQ.
  unfold cmp_frame.
  pose proof (munch_refl [(S + -2288, S + -2240)] m) as MU. pose proof (wmono_refl usegs m) as WM.
  assert (EAS : Z.land (S + -2216) 7 = 0) by (apply land7_al; [lia| Z.div_mod_to_equations; lia]).
  assert (EAQ : Z.land q 7 = 0) by (apply land7_al; lia).
  xs_to 0x129574%Z.
  carve_frame 48%nat ST.
  apply (rw_cells_split_CB usegs _ _ [] 48 _ [] [8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity].
  cbn [mk_CB_cells app] in FR.
  do 7 xs. xs.
  if_cases KA; zify_cond KA; [exfalso; lia|]. clear KA.
  xs. xs. rewrite EAS. xs.
  xs_to 0x1295a4%Z. xs.
  if_cases KB; zify_cond KB; [exfalso; lia|]. clear KB.
  xs. xs. xs. rewrite EAQ. xs.
  xs_to 0xe1ef4%Z.
  apply evt_done. do 2 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST| exact FR].
Qed.

(* [comment removed for export] *)
Lemma a2p_w8 : forall (S lo : Z) (ra gp tp u0 u1 u2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 : word)
    F fc (m : mem) (jf jl : list byte) (g3 g2 g1 f11 f10 f9 f8 f7 f6 f5 f4 f3 f2 f1 f0 : word),
  stk usegs m lo (S + -2288) -> 0x354000 <= lo -> lo + 0x1000 <= S + -2288 -> S < 2^63 -> mem_inv usegs m ->
  rw_cells usegs m (S + -2288) (cmp_frame jf g3 g2 g1 (Z_to_bv 64 S) (Z_to_bv 64 0x215b98)) ->
  rw_cells usegs m (S + -2240) [CB 2136 jl; C8 f11; C8 f10; C8 f9; C8 f8; C8 f7; C8 f6; C8 f5; C8 f4; C8 f3; C8 f2; C8 f1; C8 f0;
                                 C8 (Z_to_bv 64 0xe1b18)] ->
  evt usegs (fun ms => exists (m1 : mem),
      ms = MS (mkR (Z_to_bv 64 0xe1b2c) (Z_to_bv 64 S) gp tp u0 u1 u2 f0 f1 f0 (Z_to_bv 64 0x2ce58) (Z_to_bv 64 35) a3 a4 a5 a6 a7
                   f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 u3 u4 u5 u6) F (Z_to_bv 64 0xe1ef4) fc None m1 (seg_rom usegs)
      /\ munch [(S + -2288, S)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1 /\ stk usegs m1 lo S)
    (MS (mkR ra (Z_to_bv 64 (S + -2288)) gp tp u0 u1 u2 s0 (Z_to_bv 64 (S + -2216)) a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 0) s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
        F (Z_to_bv 64 0x1295c8) fc None m (seg_rom usegs)).
Proof.
  intros until f0. intros ST LOS LO SPH MI FR FA.
  unfold cmp_frame in *.
  pose proof (munch_refl [(S + -2288, S)] m) as MU. pose proof (wmono_refl usegs m) as WM.
  xs_to 0x1295e8%Z. xs.
  release_frame FR ST (S + -2240).
  xs. xs. xs.
  xs_to 0x215bd4%Z. xs.
  release_frame FA ST S.
  xs_to 0xe1ef4%Z.
  apply evt_done. eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption| exact ST].
Qed.

(* [comment removed for export] *)
Lemma fzp_w9 : forall (usp lo : Z) (ra gp tp u0 u1 u2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 : word)
    F fc (m : mem) (jx : list byte) (f2 f1 f0 fra : word),
  stk usegs m lo (usp + -128) -> 0x354000 <= lo -> lo <= usp + -128 -> usp < 2^63 -> mem_inv usegs m ->
  rw_cells usegs m (usp + -128) [CB 96 jx; C8 f2; C8 f1; C8 f0; C8 fra] ->
  evt usegs (fun ms =>
      ms = MS (mkR fra (Z_to_bv 64 usp) gp tp u0 u1 u2 f0 f1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
                   f2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6) F (ret_pc fra) fc None m (seg_rom usegs)
      /\ stk usegs m lo usp)
    (MS (mkR ra (Z_to_bv 64 (usp + -128)) gp tp u0 u1 u2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
        F (Z_to_bv 64 0xe1b2c) fc None m (seg_rom usegs)).
Proof.
  intros until fra. intros ST LOS LO SPH MI FR.
  xs_to 0xe1b40%Z. xs.
  release_frame FR ST usp.
  xs.
  apply evt_done. split; [reflexivity| exact ST].
Qed.
