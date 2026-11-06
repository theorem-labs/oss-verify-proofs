(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import Tac Image ZBridge Arr Bytes FP.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import ExecF ITreeA Shadow.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.BothW Require Import BImg RtCells ABase.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.

Lemma shad_band : forall lo hi, 0 <= lo -> lo <= hi -> hi <= KEND ->
  KLS <= shad lo /\ shad lo + (shad (hi - 1) + 1 - shad lo) <= 0x10007fff8000.
Proof.
  intros lo hi A B C. rewrite !shad_div. unfold ASHOFF, KLS, KEND in *. Z.div_mod_to_equations. lia.
Qed.

Lemma shad_band1 : forall a, 0 <= a -> a < KEND -> KLS <= shad a < 0x10007fff8000.
Proof.
  intros a A B. rewrite !shad_div. unfold ASHOFF, KLS, KEND in *. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma unpoisoned_munch_wclr : forall W m m' lo hi,
  unpoisoned m lo hi -> munch W m m' -> Forall wclr W -> hi <= KEND -> unpoisoned m' lo hi.
Proof.
  intros W m m' lo hi U MU FW TOP. pose proof U as (A & B & _).
  destruct (Z.leb_spec0 lo hi) as [LE|GT].
  - destruct (shad_band lo hi A LE TOP) as [L H].
    eapply unpoisoned_munch; [exact U| exact MU|]. apply wclr_disjoint_band; [exact FW| exact L| exact H].
  - destruct U as (A' & B' & _). split; [exact A'|]. split; [exact B'|]. intros G H0 H1 H2. exfalso. lia.
Qed.

(* [comment removed for export] *)
Lemma shadow_bytes_munch_wclr : forall W m m' s1 s2 f,
  shadow_bytes m s1 s2 f -> munch W m m' -> Forall wclr W -> KLS <= s1 -> s2 <= 0x10007fff8000 -> shadow_bytes m' s1 s2 f.
Proof.
  intros W m m' s1 s2 f SB MU FW L H.
  destruct (Z.leb_spec0 s1 s2) as [LE|GT].
  - eapply shadow_bytes_munch; [exact SB| exact MU|]. apply wclr_disjoint_band; [exact FW| exact L| lia].
  - eapply shadow_bytes_agree; [exact SB|]. intros s Hs. exfalso. lia.
Qed.

(* [comment removed for export] *)
Lemma rw_cells_transport_band : forall W m m' A cs,
  rw_cells bsegs m A cs -> munch W m m' -> wmono bsegs m m' -> Forall wclr W ->
  KLS <= A -> A + Z.of_nat (cells_size cs) <= 0x10007fff8000 -> rw_cells bsegs m' A cs.
Proof.
  intros W m m' A cs RW MU WM FW L H.
  eapply rw_cells_transport; [exact RW| exact MU| exact WM|]. apply wclr_disjoint_band; [exact FW| exact L| exact H].
Qed.

Lemma bytes_at_transport_band : forall W m m' A bs,
  bytes_at bsegs m A bs -> munch W m m' -> Forall wclr W ->
  KLS <= A -> A + Z.of_nat (length bs) <= 0x10007fff8000 -> bytes_at bsegs m' A bs.
Proof.
  intros W m m' A bs BY MU FW L H.
  eapply bytes_at_transport; [exact BY| exact MU|]. apply wclr_disjoint_band; [exact FW| exact L| exact H].
Qed.

(* [comment removed for export] *)
Lemma byte_keep_band : forall W m m' a, munch W m m' -> Forall wclr W -> KLS <= a < 0x10007fff8000 -> m' (wa a) = m (wa a).
Proof.
  intros W m m' a MU FW B. apply MU. rewrite wa_unsigned by (unfold KLS in B; lia). apply wclr_outside_band; [exact FW| exact B].
Qed.

(* [comment removed for export] *)
Lemma Forall_wclr_app : forall W1 W2, Forall wclr W1 -> Forall wclr W2 -> Forall wclr (W1 ++ W2).
Proof. intros W1 W2 A B. apply Forall_app. split; assumption. Qed.

Lemma wclr_sub : forall lo hi a b, wclr (lo, hi) -> lo <= a -> b <= hi -> a <= b -> wclr (a, b).
Proof. intros lo hi a b W A B AB. unfold wclr, sclr, AIMG_HI, KLS in *. cbn [fst snd] in *. lia. Qed.

(* [comment removed for export] *)
Lemma shr3_lo : forall a, 0 <= a -> 0x7fff8000 <= Z.shiftr a 3 + ASHOFF.
Proof. intros a H. rewrite Z.shiftr_div_pow2 by lia. unfold ASHOFF. Z.div_mod_to_equations. lia. Qed.

(* [comment removed for export] *)
Lemma ablk_ind : forall lo hi, ablk lo hi ->
  exists b : Z, 0 <= b <= 1 /\ hi <= KLS + b * 0x7FFFFF800000 /\ 0x10007fff8000 * b <= lo.
Proof.
  intros lo hi H. atop_facts. unfold ablk, AIMG_HI, KLS in *. destruct H as [(A & B)|(A & B)].
  - exists 0. lia.
  - exists 1. lia.
Qed.

End CANSEC1.

(* [comment removed for export] *)
Ltac band_ind H b :=
  let b0 := fresh b "r" in let b1 := fresh b "hi" in let b2 := fresh b "lo" in
  destruct (ablk_ind _ _ H) as (b & b0 & b1 & b2); unfold KLS in b1.

(* [comment removed for export] *)
Ltac shr_facts :=
  repeat match goal with
  | H : rw_cells _ _ (Z.shiftr ?a 3 + ASHOFF) _ |- _ =>
      lazymatch goal with
      | _ : 0x7fff8000 <= Z.shiftr a 3 + ASHOFF |- _ => fail
      | _ => let Hs := fresh "SHR" in pose proof (shr3_lo a ltac:(lia)) as Hs
      end
  end.

(* [comment removed for export] *)
Ltac wclr1 :=
  first [ apply wclr_high; cbn [fst snd]; unfold KHIGH in *; lia
        | match goal with H : ablk _ _ |- _ => eapply wclr_ablk; [exact H| cbn [fst snd]; lia| cbn [fst snd]; lia] end
        | match goal with H : ablock_range _ _ |- _ => eapply wclr_ablk; [exact (proj1 H)| cbn [fst snd]; lia| cbn [fst snd]; lia] end
        | match goal with H : Forall wclr _ |- _ => eapply (proj1 (Forall_forall wclr _) H); cbn; tauto end ].
Ltac fw_wclr :=
  lazymatch goal with
  | |- Forall wclr (_ ++ _) => apply Forall_wclr_app; fw_wclr
  | |- Forall wclr (_ :: _) => constructor; [wclr1| fw_wclr]
  | |- Forall wclr [] => constructor
  | |- Forall wclr ?W => first [assumption| fail 1 "fw_wclr: abstract write set" W]
  end.

(* [comment removed for export] *)
Ltac band_nowin :=
  first [ unfold KHIGH, KLS in *; lia
        | match goal with H : ablk _ _ |- _ => eapply ablk_clear_band; [eapply ablk_sub; [exact H| lia| lia]| unfold KLS in *; lia] end
        | match goal with H : ablock_range _ _ |- _ => eapply ablk_clear_band; [eapply ablk_sub; [exact (proj1 H)| lia| lia]| unfold KLS in *; lia] end ].
Ltac band_outside :=
  lazymatch goal with
  | |- _ /\ _ => split; [band_outside| band_outside]
  | |- True => exact I
  | |- outside _ _ => cbn [outside]; band_outside
  | |- disjoint_from _ _ _ => cbn [disjoint_from]; band_outside
  | |- _ => band_nowin
  end.
