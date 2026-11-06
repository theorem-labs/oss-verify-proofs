(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step ValProofs MemProofs.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step MemP.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Section WithSegs.
Variable segs : list Segment.

Lemma region_ok_frame_v : forall priv E m m' k r,
  ev E 0%uint63 = Z_to_bv 64 0 ->
  region_ok segs priv E m k r ->
  (forall a, 0 <= a < two64 ->
     (PrimInt63.eqb k 0%uint63 = false -> bv_unsigned (ev E k) + loZ r <= a < bv_unsigned (ev E k) + hiZ E r) ->
     (PrimInt63.eqb k 0%uint63 = true -> (exists seg, find_segment segs a 1 = Some seg) /\ ~ in_priv priv a) ->
     rb segs m' a = rb segs m a /\ (wb segs m a = true -> wb segs m' a = true)) ->
  region_ok segs priv E m' k r.
Proof.
  intros priv E m m' k r Hz RO FR.
  destruct RO as [Rbst Rrange Rvalid Rcells Rin Rbg].
  assert (HB0 : PrimInt63.eqb k 0%uint63 = true -> bv_unsigned (ev E k) = 0).
  { intros K. apply eqb_correct in K. subst k. apply ev0_zero. exact Hz. }
  rewrite half63 in *.
  constructor.
  - exact Rbst.
  - exact Rrange.
  - intros K a Ha.
    destruct (FR a ltac:(pose proof (Rrange K); lia) (fun _ => Ha) ltac:(intros K'; rewrite K in K'; discriminate K')) as [ER EW].
    destruct (Rvalid K a Ha) as (V1 & V2 & V3). rewrite ER. split; [exact V1|]. split; [|exact V3]. intros W. exact (EW (V2 W)).
  - intros g gr Hf. destruct (Rcells g gr Hf) as [Ss Fc]. split; [exact Ss|].
    apply Forall_forall. intros c Hc. pose proof (proj1 (Forall_forall _ _) Fc c Hc) as (C1 & C2 & C3 & C4).
    split; [exact C1|]. split; [exact C2|]. split; [exact C3|]. intros i Hi.
    pose proof (Rin g gr c i Hf Hc Hi) as [P1 P2]. cbv zeta in P1, P2. rewrite ?half63 in P2.
    replace (bv_unsigned (ev E k) + 8 * keyZ g + to_Z (c_idx c) + i)
      with (bv_unsigned (ev E k) + (8 * keyZ g + to_Z (c_idx c) + i)) by lia.
    assert (ER : rb segs m' (bv_unsigned (ev E k) + (8 * keyZ g + to_Z (c_idx c) + i)) = rb segs m (bv_unsigned (ev E k) + (8 * keyZ g + to_Z (c_idx c) + i))).
    { destruct (PrimInt63.eqb k 0%uint63) eqn:K.
      - destruct (P2 eq_refl) as (Q1 & Q2 & Q3). rewrite (HB0 eq_refl). rewrite Z.add_0_l.
        apply FR; [unfold two64; lia | intros X; discriminate X | intros _; split; assumption].
      - pose proof (P1 eq_refl) as Q. pose proof (Rrange eq_refl) as RR.
        apply FR; [lia | intros _; lia | intros X; discriminate X]. }
    rewrite ER.
    replace (bv_unsigned (ev E k) + (8 * keyZ g + to_Z (c_idx c) + i))
      with (bv_unsigned (ev E k) + 8 * keyZ g + to_Z (c_idx c) + i) by lia.
    apply C4; exact Hi.
  - exact Rin.
  - intros o H1 H2 U. pose proof (Rbg o H1 H2 U) as G. rewrite ?half63 in H2.
    destruct (bg_byte segs E k r o) as [b|]; [|exact I].
    assert (ER : rb segs m' (bv_unsigned (ev E k) + o) = rb segs m (bv_unsigned (ev E k) + o)).
    { destruct (PrimInt63.eqb k 0%uint63) eqn:K.
      - destruct (H2 eq_refl) as (Q1 & [bs Q2] & Q3). rewrite (HB0 eq_refl). rewrite Z.add_0_l.
        apply FR; [unfold two64; lia | intros X; discriminate X | intros _].
        split; [| exact Q3]. apply (memory_read_find_segment segs o bs); [unfold two64; lia| exact Q2].
      - pose proof (H1 eq_refl) as Q. pose proof (Rrange eq_refl) as RR.
        apply FR; [lia | intros _; lia | intros X; discriminate X]. }
    rewrite ER. exact G.
Qed.

Lemma frame_v_of_raw : forall m m' a, m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) ->
  rb segs m' a = rb segs m a /\ (wb segs m a = true -> wb segs m' a = true).
Proof. intros m m' a E. split; [exact (rb_ext segs m m' a E)| rewrite (wb_ext segs m m' a E); exact (fun H => H)]. Qed.
End WithSegs.

Module TwinB.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Sem.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64Proofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.ValProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.MemProofs.

Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step MemP.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Section WithSegs.
Variable segs : list Segment.

Lemma region_ok_frame_v : forall priv E m m' k r,
  ev E 0%uint63 = Z_to_bv 64 0 ->
  region_ok segs priv E m k r ->
  (forall a, 0 <= a < two64 ->
     (PrimInt63.eqb k 0%uint63 = false -> bv_unsigned (ev E k) + loZ r <= a < bv_unsigned (ev E k) + hiZ E r) ->
     (PrimInt63.eqb k 0%uint63 = true -> (exists seg, find_segment segs a 1 = Some seg) /\ ~ in_priv priv a) ->
     rb segs m' a = rb segs m a /\ (wb segs m a = true -> wb segs m' a = true)) ->
  region_ok segs priv E m' k r.
Proof.
  intros priv E m m' k r Hz RO FR.
  destruct RO as [Rbst Rrange Rvalid Rcells Rin Rbg].
  assert (HB0 : PrimInt63.eqb k 0%uint63 = true -> bv_unsigned (ev E k) = 0).
  { intros K. apply eqb_correct in K. subst k. apply ev0_zero. exact Hz. }
  rewrite half63 in *.
  constructor.
  - exact Rbst.
  - exact Rrange.
  - intros K a Ha.
    destruct (FR a ltac:(pose proof (Rrange K); lia) (fun _ => Ha) ltac:(intros K'; rewrite K in K'; discriminate K')) as [ER EW].
    destruct (Rvalid K a Ha) as (V1 & V2 & V3). rewrite ER. split; [exact V1|]. split; [|exact V3]. intros W. exact (EW (V2 W)).
  - intros g gr Hf. destruct (Rcells g gr Hf) as [Ss Fc]. split; [exact Ss|].
    apply Forall_forall. intros c Hc. pose proof (proj1 (Forall_forall _ _) Fc c Hc) as (C1 & C2 & C3 & C4).
    split; [exact C1|]. split; [exact C2|]. split; [exact C3|]. intros i Hi.
    pose proof (Rin g gr c i Hf Hc Hi) as [P1 P2]. cbv zeta in P1, P2. rewrite ?half63 in P2.
    replace (bv_unsigned (ev E k) + 8 * keyZ g + to_Z (c_idx c) + i)
      with (bv_unsigned (ev E k) + (8 * keyZ g + to_Z (c_idx c) + i)) by lia.
    assert (ER : rb segs m' (bv_unsigned (ev E k) + (8 * keyZ g + to_Z (c_idx c) + i)) = rb segs m (bv_unsigned (ev E k) + (8 * keyZ g + to_Z (c_idx c) + i))).
    { destruct (PrimInt63.eqb k 0%uint63) eqn:K.
      - destruct (P2 eq_refl) as (Q1 & Q2 & Q3). rewrite (HB0 eq_refl). rewrite Z.add_0_l.
        apply FR; [unfold two64; lia | intros X; discriminate X | intros _; split; assumption].
      - pose proof (P1 eq_refl) as Q. pose proof (Rrange eq_refl) as RR.
        apply FR; [lia | intros _; lia | intros X; discriminate X]. }
    rewrite ER.
    replace (bv_unsigned (ev E k) + (8 * keyZ g + to_Z (c_idx c) + i))
      with (bv_unsigned (ev E k) + 8 * keyZ g + to_Z (c_idx c) + i) by lia.
    apply C4; exact Hi.
  - exact Rin.
  - intros o H1 H2 U. pose proof (Rbg o H1 H2 U) as G. rewrite ?half63 in H2.
    destruct (bg_byte segs E k r o) as [b|]; [|exact I].
    assert (ER : rb segs m' (bv_unsigned (ev E k) + o) = rb segs m (bv_unsigned (ev E k) + o)).
    { destruct (PrimInt63.eqb k 0%uint63) eqn:K.
      - destruct (H2 eq_refl) as (Q1 & [bs Q2] & Q3). rewrite (HB0 eq_refl). rewrite Z.add_0_l.
        apply FR; [unfold two64; lia | intros X; discriminate X | intros _].
        split; [| exact Q3]. apply (memory_read_find_segment segs o bs); [unfold two64; lia| exact Q2].
      - pose proof (H1 eq_refl) as Q. pose proof (Rrange eq_refl) as RR.
        apply FR; [lia | intros _; lia | intros X; discriminate X]. }
    rewrite ER. exact G.
Qed.

Lemma frame_v_of_raw : forall m m' a, m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) ->
  rb segs m' a = rb segs m a /\ (wb segs m a = true -> wb segs m' a = true).
Proof. intros m m' a E. split; [exact (rb_ext segs m m' a E)| rewrite (wb_ext segs m m' a E); exact (fun H => H)]. Qed.
End WithSegs.
End TwinB.
