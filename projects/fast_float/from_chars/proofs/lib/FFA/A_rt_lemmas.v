(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Shadow.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFA Require Import A_rt_stmt.
From OSSVerify.fast_float.from_chars.images Require Import Asan.

Module A_asan_memcpy2_stmt.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Shadow.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFA Require Import A_rt_stmt.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
Local Ltac lia ::= lia_tc.  (* [comment removed for export] *)
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.

Notation ASEGS := Asan.M.loaded_segments.

Definition asan_memcpy2_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (v : rt_vals) (bs old : list byte) (shlo shn shlo2 shn2 : Z),
    bytes_at ASEGS m (bv_unsigned a1) bs ->
    u8arr ASEGS m (bv_unsigned a0) old ->
    length old = length bs ->
    Z.of_nat (length bs) = bv_unsigned a2 ->
    (bv_unsigned a0 + bv_unsigned a2 <= bv_unsigned a1 \/ bv_unsigned a1 + bv_unsigned a2 <= bv_unsigned a0)%Z ->
    (app2r (bv_unsigned a0) (bv_unsigned a0 + bv_unsigned a2 + 8))%Z -> (bv_unsigned a0 + bv_unsigned a2 + 8 <= KTOP)%Z ->
    (app2r (bv_unsigned a1) (bv_unsigned a1 + bv_unsigned a2 + 8))%Z -> (bv_unsigned a1 + bv_unsigned a2 + 8 <= KTOP)%Z ->
    (bv_unsigned a2 <= 2^40)%Z ->
    shz ASEGS m (ASAN_B + bv_unsigned a0 / 8) ((bv_unsigned a0 + bv_unsigned a2 - 1) / 8 - bv_unsigned a0 / 8 + 1) ->
    shz ASEGS m (ASAN_B + bv_unsigned a1 / 8) ((bv_unsigned a1 + bv_unsigned a2 - 1) / 8 - bv_unsigned a1 / 8 + 1) ->
    rdbl ASEGS m shlo shn ->
    (shlo + 8 <= ASAN_B + bv_unsigned a0 / 8)%Z -> (ASAN_B + (bv_unsigned a0 + bv_unsigned a2) / 8 + 8 <= shlo + shn)%Z ->
    rdbl ASEGS m shlo2 shn2 ->
    (shlo2 + 8 <= ASAN_B + bv_unsigned a1 / 8)%Z -> (ASAN_B + (bv_unsigned a1 + bv_unsigned a2) / 8 + 8 <= shlo2 + shn2)%Z ->
    stk ASEGS m (bv_unsigned sp - IMEMCPY_NEED) (bv_unsigned sp) ->
    (IMG_END <= bv_unsigned sp - IMEMCPY_NEED)%Z -> (KHI <= bv_unsigned sp - IMEMCPY_NEED)%Z -> (bv_unsigned sp <= KTOP)%Z ->
    (bv_unsigned sp mod 16 = 0)%Z ->
    (bv_unsigned sp <= bv_unsigned a0 \/ bv_unsigned a0 + bv_unsigned a2 <= bv_unsigned sp - IMEMCPY_NEED)%Z ->
    (bv_unsigned sp <= bv_unsigned a1 \/ bv_unsigned a1 + bv_unsigned a2 <= bv_unsigned sp - IMEMCPY_NEED)%Z ->
    pristine m RELRO_LO RELRO_HI -> pristine m REALTAB_LO REALTAB_HI ->
    RT m v -> rt_disj v (bv_unsigned sp - IMEMCPY_NEED) (bv_unsigned sp) ->
    rt_disj v (bv_unsigned a0) (bv_unsigned a0 + bv_unsigned a2) ->
    (bv_unsigned ra mod 2 = 0)%Z ->
    evt ASEGS (asan_memcpy_post ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                 F fc (bv_unsigned a1) (bv_unsigned a2) bs m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 A_IMEMCPY) fc None m (seg_rom ASEGS)).

End A_asan_memcpy2_stmt.

Local Ltac lia ::= lia_tc.  (* [comment removed for export] *)
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Open Scope bv_scope.

Notation ASEGS := Asan.M.loaded_segments.

(* [comment removed for export] *)
Definition W_ok_rt (v : rt_vals) (W : list ivl) : Prop :=
  Forall (fun iv => (IMG_END <= fst iv)%Z /\ (rt_disj v (fst iv) (snd iv) \/ (SH_LO <= fst iv /\ snd iv <= KHI))%Z) W.

Lemma disjoint_from_Forall : forall (P : ivl -> Prop) (W : list ivl) (A n : Z),
  Forall P W ->
  (forall lo hi, P (lo, hi)%Z -> (A + n <= lo \/ hi <= A)%Z) ->
  disjoint_from W A n.
Proof.
  intros P W A n HF HP. induction HF as [| [lo hi] W Hiv HF IH]; cbn; [exact I|].
  split; [| exact IH]. apply (HP lo hi). exact Hiv.
Qed.

Lemma rt_disj_sub : forall v lo hi lo' hi',
  rt_disj v lo hi -> (lo <= lo')%Z -> (hi' <= hi)%Z -> rt_disj v lo' hi'.
Proof. unfold rt_disj. intros v lo hi lo' hi' (A & B & C) H1 H2. repeat split; lia. Qed.

Lemma RT_transport : forall m m' v W,
  RT m v -> munch W m m' -> W_ok_rt v W -> RT m' v.
Proof.
  intros m m' v W RTH MU WOK.
  assert (DI : forall A n, (A + n <= IMG_END)%Z -> disjoint_from W A n).
  { intros A n HA. eapply disjoint_from_Forall; [exact WOK|]. cbn [fst snd]. intros lo hi [Hlo _]. lia. }
  pose proof RTH as RTX. unfold RT in RTX.
  destruct RTX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & _ & _ & Ac & _ & At & _ & Ab & _)).
  unfold rt_app in Ac, At, Ab.
  assert (DC : disjoint_from W (rt_ctx v + 152) 8).
  { eapply disjoint_from_Forall; [exact WOK|]. cbn [fst snd]. unfold rt_disj. intros lo hi [_ [(H & _ & _)|[H1 H2]]]; lia. }
  assert (DT : disjoint_from W (rt_thr v + 48) 16).
  { eapply disjoint_from_Forall; [exact WOK|]. cbn [fst snd]. unfold rt_disj. intros lo hi [_ [(_ & H & _)|[H1 H2]]]; lia. }
  assert (DB : disjoint_from W (rt_blk v + 24) 8).
  { eapply disjoint_from_Forall; [exact WOK|]. cbn [fst snd]. unfold rt_disj. intros lo hi [_ [(_ & _ & H)|[H1 H2]]]; lia. }
  clear Ac At Ab.
  unfold RT in RTH |- *.
  destruct RTH as (RT1 & RT2 & RT2b & RT3 & RT4 & (fb & RT5 & Hfb) & RT6 & RT7 & RT8 & RT9 & RT10 & RT11 & RT12 & RT13 & RT14 & RTP).
  destruct RTP as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14).
  repeat match goal with |- _ /\ _ => split end;
  try (eapply ro_cells_transport; [eassumption | exact MU | first [apply DI; cbn; lia | assumption]]);
  try (exists fb; split; [| exact Hfb]; eapply ro_cells_transport; [eassumption | exact MU | apply DI; cbn; lia]);
  first [ assumption | lia ].
Qed.

(* [comment removed for export] *)
Ltac open_RT RTH :=
  unfold RT in RTH;
  let fb := fresh "fb" in let Hfb := fresh "Hfb" in
  destruct RTH as (?RT1 & ?RT2 & ?RT2b & ?RT3 & ?RT4 & (fb & ?RT5 & Hfb) & ?RT6 & ?RT7 & ?RT8 & ?RT9 & ?RT10 & ?RT11 & ?RT12 & ?RT13 & ?RT14 & ?RTP).

Tactic Notation "open_RT_keep" hyp(RTH) :=
  let X := fresh "RTcopy" in
  pose proof RTH as X; unfold RT in X;
  destruct X as (RT1 & RT2 & RT2b & RT3 & RT4 & (fb & RT5 & Hfb) & RT6 & RT7 & RT8 & RT9 & RT10 & RT11 & RT12 & RT13 & RT14 & RTP).

Ltac close_RT :=
  lazymatch goal with
  | |- RT _ _ =>
      unfold RT; repeat match goal with |- _ /\ _ => split end;
      first [ eassumption | lia | eexists; split; [eassumption | first [assumption | lia]] | idtac ]
  end.

(* [comment removed for export] *)
Ltac solve_W_iv :=
  split; [ lia
         | lazymatch goal with
           | |- rt_disj _ ?lo _ \/ _ =>
               lazymatch lo with
               | context [2147450880%Z] => right; split; lia
               | _ => left; first [ match goal with H : rt_disj _ _ _ |- _ => eapply rt_disj_sub; [exact H | lia | lia] end
                                 | unfold rt_disj in *; repeat match goal with |- _ /\ _ => split end; lia ]
               end
           end ].
Ltac solve_W_rt :=
  unfold W_ok_rt; repeat (apply Forall_cons; [ cbn [fst snd]; solve_W_iv | ]); apply Forall_nil.
