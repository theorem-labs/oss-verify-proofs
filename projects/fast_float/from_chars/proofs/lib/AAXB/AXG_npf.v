(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require Import AxAsan AXG_put AXG_put2 AXG_np AXG_nf1.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Abbreviation SEGS := AsanUbsan.M.loaded_segments.

Lemma store_ok_frame : forall n (m m' : word -> option byte) (a : Z), 0 <= a -> a + Z.of_nat n <= 2^64 ->
  (forall x, a <= x < a + Z.of_nat n -> m' (wa x) = m (wa x)) -> store_ok SEGS m' (wa a) n = store_ok SEGS m (wa a) n.
Proof.
  induction n as [|n IH]; intros m m' a Ha Hn H; [reflexivity|].
  cbn [store_ok].
  assert (EW : wview SEGS m' (wa a) = wview SEGS m (wa a)) by (unfold wview; rewrite (H a) by lia; reflexivity).
  rewrite EW. destruct (wview SEGS m (wa a)); [|reflexivity].
  destruct n as [|n']; [reflexivity|].
  assert (Ea : (wa a + 1)%bv = wa (a + 1)).
  { apply bv_eq. rewrite bv_add_unsigned. rewrite (u_wa_small a) by lia. rewrite (u_wa_small (a + 1)) by lia.
    change (bv_unsigned 1%bv) with 1. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64). rewrite Z.mod_small; lia. }
  rewrite Ea. apply IH; [lia | lia | intros x Hx; apply H; lia].
Qed.
Lemma wr_frame : forall (m m' : word -> option byte) a n, 0 <= a -> a + n <= 2^64 ->
  (forall x, a <= x < a + n -> m' (wa x) = m (wa x)) -> wr m a n -> wr m' a n.
Proof.
  intros m m' a n Ha Hn H W d k Hd Hk. rewrite (store_ok_frame k m m' (a + d)) by first [lia | (intros x Hx; apply H; lia)]. exact (W d k Hd Hk).
Qed.

(* [comment removed for export] *)
Record INV_Co (m : word -> option byte) (CA SB c sz nc newc j : Z) : Prop := {
  io_geo : 1 <= c <= 30 /\ 16 <= sz /\ sz mod 16 = 0 /\ 1 <= nc <= 8 /\ 1 <= j /\ j + nc <= newc /\ newc * sz <= 262144 /\ newc <= 16384 ;
  io_cnt : rd m (REC CA c) 4 (cnt_of nc j) ;
  io_mc : rd m (REC CA c + 4) 4 (2 * nc) ;
  io_sz : rd m (REC CA c + 8) 8 sz ;
  io_chunks : forall i, 0 <= i < cnt_of nc j -> rd m (REC CA c + 16 + 4 * i) 4 ((j + cnt_of nc j - 1 - i) * (sz / 16)) ;
  io_mutex : rd m (RIX SB c) 8 0 ;
  io_nf : rd m (RIX SB c + 16) 8 (newc - nc * b_of nc j) ;
  io_na : exists na, 0 <= na < 2^64 /\ rd m (RIX SB c + 72) 8 na ;
  io_fa : forall k, 0 <= k < newc - nc * b_of nc j -> rd m (FAX SB c + 4 * k) 4 ((newc - 1 - k) * (sz / 16)) ;
  io_wrec : wr m (REC CA c) 80 ;
  io_wri : wr m (RIX SB c) 128
}.
(* [comment removed for export] *)
Definition STATS (m : word -> option byte) (CA : Z) : Prop :=
  (exists st, 0 <= st < 2^64 /\ rd m (CA + 2576) 8 st) /\ (exists st, 0 <= st < 2^64 /\ rd m (CA + 2584) 8 st) /\ wr m (CA + 2560) 32.
Lemma INV_C_o : forall m CA SB c sz nc newc j, INV_C m CA SB c sz nc newc j -> INV_Co m CA SB c sz nc newc j.
Proof. intros m CA SB c sz nc newc j [A B C D E F G H I J K L M N O]. constructor; try assumption. lia. Qed.
Lemma INV_Co_C : forall m CA SB c sz nc newc j, 2 <= c <= 16 -> INV_Co m CA SB c sz nc newc j -> rd m 929848 8 SB -> rd m 929864 8 (SB + 137438953472) ->
  STATS m CA -> INV_C m CA SB c sz nc newc j.
Proof. intros m CA SB c sz nc newc j Hc [A D E F G H I J K M N] B C (L & _ & O). constructor; try assumption. lia. Qed.

(* [comment removed for export] *)
Definition foot_Co (CA SB c newc x : Z) : Prop :=
  REC CA c <= x < REC CA c + 80 \/ RIX SB c <= x < RIX SB c + 128 \/ FAX SB c <= x < FAX SB c + 4 * newc.

Lemma INV_Co_frame : forall m m' CA SB c sz nc newc j, 0 <= CA -> CA + 4096 <= 2^63 -> 0 <= SB -> SB + 137438953472 + 4096 <= 2^63 ->
  (forall x, foot_Co CA SB c newc x -> m' (wa x) = m (wa x)) -> INV_Co m CA SB c sz nc newc j -> INV_Co m' CA SB c sz nc newc j.
Proof.
  intros m m' CA SB c sz nc newc j H1 H2 H3 H4 HF [A D E F G H I J K M N].
  pose proof (cnt_of_range nc j ltac:(lia) ltac:(lia)) as Hcr. pose proof (b_of_pos nc j ltac:(lia) ltac:(lia)) as Hb.
  assert (Hnb : 0 <= newc - nc * b_of nc j <= newc) by (pose proof (b_of_bounds nc j ltac:(lia) ltac:(lia)); nia).
  constructor; try assumption.
  - apply (rd_frame m m'); [lia | cbn; lia | intros x Hx; cbn in Hx; apply HF; unfold foot_Co; lia | exact D].
  - apply (rd_frame m m'); [lia | cbn; lia | intros x Hx; cbn in Hx; apply HF; unfold foot_Co; lia | exact E].
  - apply (rd_frame m m'); [lia | cbn; lia | intros x Hx; cbn in Hx; apply HF; unfold foot_Co; lia | exact F].
  - intros i Hi. apply (rd_frame m m'); [lia | cbn; lia | intros x Hx; cbn in Hx; apply HF; unfold foot_Co; lia | exact (G i Hi)].
  - apply (rd_frame m m'); [lia | cbn; lia | intros x Hx; cbn in Hx; apply HF; unfold foot_Co; lia | exact H].
  - apply (rd_frame m m'); [lia | cbn; lia | intros x Hx; cbn in Hx; apply HF; unfold foot_Co; lia | exact I].
  - destruct J as (na & Hna & Rna). exists na. split; [exact Hna|].
    apply (rd_frame m m'); [lia | cbn; lia | intros x Hx; cbn in Hx; apply HF; unfold foot_Co; lia | exact Rna].
  - intros k Hk. apply (rd_frame m m'); [lia | cbn; lia | intros x Hx; cbn in Hx; apply HF; unfold foot_Co; lia | exact (K k Hk)].
  - apply (wr_frame m m'); [lia | lia | intros x Hx; apply HF; unfold foot_Co; lia | exact M].
  - apply (wr_frame m m'); [lia | lia | intros x Hx; apply HF; unfold foot_Co; lia | exact N].
Qed.

(* [comment removed for export] *)
Record VIRG_C (m : word -> option byte) (CA SB c : Z) : Prop := {
  vc_cnt : rd m (REC CA c) 4 0 ;
  vc_ic : (rd m (REC CA c + 4) 4 0 /\ exists sz0, 0 <= sz0 < 2^64 /\ rd m (REC CA c + 8) 8 sz0) \/
          (rd m (REC CA c + 4) 4 (mc_tbl c) /\ rd m (REC CA c + 8) 8 (sz_tbl c)) ;
  vc_ri : forall i, 0 <= i < 16 -> rd m (RIX SB c + 8 * i) 8 0 ;
  vc_wc : wr m (REC CA c) 80 ;
  vc_wri : wr m (RIX SB c) 128
}.
(* [comment removed for export] *)
Definition SHW_C (m : word -> option byte) (SH c : Z) : Prop := wr m (SH + 536870912 * c) 32768 /\ wr m (SH + 536870912 * c + 469762048) 32768.
Definition foot_V (CA SB c x : Z) : Prop := REC CA c <= x < REC CA c + 80 \/ RIX SB c <= x < RIX SB c + 128.
Lemma VIRG_C_frame : forall m m' CA SB c, 1 <= c <= 30 -> 0 <= CA -> CA + 4096 <= 2^63 -> 0 <= SB -> SB + 137438953472 + 4096 <= 2^63 ->
  (forall x, foot_V CA SB c x -> m' (wa x) = m (wa x)) -> VIRG_C m CA SB c -> VIRG_C m' CA SB c.
Proof.
  intros m m' CA SB c Hc H1 H2 H3 H4 HF [A B C F G].
  constructor.
  - apply (rd_frame m m'); [lia | cbn; lia | intros x Hx; cbn in Hx; apply HF; unfold foot_V; lia | exact A].
  - destruct B as [[B1 (sz0 & Hs & B2)]|[B1 B2]]; [left; split; [|exists sz0; split; [exact Hs|]] | right; split].
    all: apply (rd_frame m m'); [lia | cbn; lia | intros x Hx; cbn in Hx; apply HF; unfold foot_V; lia | assumption].
  - intros i Hi. apply (rd_frame m m'); [lia | cbn; lia | intros x Hx; cbn in Hx; apply HF; unfold foot_V; lia | exact (C i Hi)].
  - apply (wr_frame m m'); [lia | lia | intros x Hx; apply HF; unfold foot_V; lia | exact F].
  - apply (wr_frame m m'); [lia | lia | intros x Hx; apply HF; unfold foot_V; lia | exact G].
Qed.

(* [comment removed for export] *)
Definition RBX (SB c : Z) : Z := SB + 4294967296 * c.
Definition SHX (SH c : Z) : Z := SH + 536870912 * c.
Record POP_C (m : word -> option byte) (SB SH c sz j : Z) : Prop := {
  (* [comment removed for export] *)
  pc_map : forall x, RBX SB c + sz * j <= x < RBX SB c + 262144 -> m (wa x) = Some (Z_to_bv 8 0) ;
  pc_sh : forall x, SHX SH c + sz / 8 * j <= x < SHX SH c + 32768 -> m (wa x) = Some (Z_to_bv 8 250) ;
  (* [comment removed for export] *)
  pc_shm : forall x, SHX SH c <= x < SHX SH c + 32768 -> m (wa x) <> None
}.
Lemma pc_map_nn : forall m SB SH c sz j, POP_C m SB SH c sz j -> forall x, RBX SB c + sz * j <= x < RBX SB c + 262144 -> m (wa x) <> None.
Proof. intros m SB SH c sz j [A _ _] x Hx. rewrite (A x Hx). discriminate. Qed.
Lemma POP_C_frame : forall m m' SB SH c sz j,
  (forall x, RBX SB c + sz * j <= x < RBX SB c + 262144 \/ SHX SH c <= x < SHX SH c + 32768 -> m' (wa x) = m (wa x)) ->
  0 <= sz / 8 * j ->
  POP_C m SB SH c sz j -> POP_C m' SB SH c sz j.
Proof.
  intros m m' SB SH c sz j HF Hj [A B C]. constructor.
  - intros x Hx. rewrite HF by (left; exact Hx). exact (A x Hx).
  - intros x Hx. rewrite HF by (right; lia). exact (B x Hx).
  - intros x Hx. rewrite HF by (right; exact Hx). exact (C x Hx).
Qed.
Lemma POP_C_step : forall m SB SH c sz j, 0 <= sz -> 0 <= j -> POP_C m SB SH c sz j -> POP_C m SB SH c sz (j + 1).
Proof.
  intros m SB SH c sz j Hs Hj [A B C]. constructor.
  - intros x Hx. apply A. nia.
  - intros x Hx. apply B. assert (0 <= sz / 8) by (apply Z.div_pos; lia). nia.
  - exact C.
Qed.
(* [comment removed for export] *)
