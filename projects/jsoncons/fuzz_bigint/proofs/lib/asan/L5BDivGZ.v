(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA
     AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5Words L5DefsAB0
     L5CoreAB0 L5CoreSpecsAB0 L5StepAB0 L5BDivPG3.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5ADVGZ.
Import L5A. Import L5CA. Import L5SA. Import L5ADIVPG3.
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Local Ltac inl := apply L5K.in_b; vm_compute; reflexivity.
Local Ltac blia := keep_arith; first [ (repeat match goal with H : _ \/ _ |- _ => clear H end); lia
                                     | match goal with H : _ \/ _ |- _ => clear_disj_but H; destruct H; lia end ].
Local Ltac asm := match goal with H : ?T |- ?G => constr_eq T G; exact H end.
Local Ltac sc := first [ asm | rk | gmem | (arith_goal; first [asm | blia]) | assumption ].
Definition U (R : bvmap 5 word) (k : nat) : Z := bv_unsigned (getr R (reg k)).
Lemma UR R k : 0 <= U R k < 2 ^ 64. Proof. unfold U. apply BL.bvu_range. Qed.
Lemma U_to R k : getr R (reg k) = Z_to_bv 64 (U R k). Proof. unfold U. symmetry. apply Z_to_bv_bv_unsigned. Qed.

Section LOOP.
Variables (E Dq len : Z).
Local Notation SPA := (E - 384).

Definition FPZ (a : Z) : Prop := E - 392 <= a < E - 384 \/ Dq <= a < Dq + 8 * len.
Definition zagree (M0 Mk : word -> option byte) : Prop :=
  mem_grows M0 Mk /\ forall a, 0 <= a < 2 ^ 64 -> ~ FPZ a -> Mk (Z_to_bv 64 a) = M0 (Z_to_bv 64 a).
Lemma zagree_trans M0 M1 M2 : zagree M0 M1 -> zagree M1 M2 -> zagree M0 M2.
Proof. intros [G1 A1] [G2 A2]. split. eapply mem_grows_trans; eassumption. intros a Ha Hn. rewrite A2 by assumption. apply A1; assumption. Qed.

Definition nsh (x lx : Z) : Prop := 2147446784 + 17592186048512 <= x \/ x + lx <= 2147446784.
Definition oim (x lx : Z) : Prop := x + lx <= 65536 \/ 6504448 <= x.

Record zctx (M : word -> option byte) : Prop := ZCTX {
  zc_E : 140735332487680 <= E <= 140737488355328;
  zc_EA : E mod 32 = 0;
  zc_n : 1 <= len <= 134217727;
  zc_fw : L5.writable RSEGS M (E - 400) 400;
  zc_st : L5.img_clear M 860160 884736 /\ L5.u64_at RSEGS M 911160 2147450880 /\ L5.u32_at RSEGS M 911168 1;
  zc_vq : L5.u64_at RSEGS M (E - 136) Dq;
  zc_vz : L5KA.zeros_at M ((E - 136) / 8 + 2147450880) 1;
  zc_q : 4096 <= Dq /\ Dq + 8 * len <= 140737479966720 /\ Dq mod 8 = 0 /\ nsh Dq (8 * len) /\ oim Dq (8 * len);
  zc_qw : L5.writable RSEGS M Dq (8 * len);
  zc_qz : L5KA.zeros_at M (Dq / 8 + 2147450880) len;
  zc_ap : Dq + 8 * len <= E - 400 }.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma zdiv : E mod 32 = 0 -> 140735332487680 <= E <= 140737488355328 -> Dq mod 8 = 0 -> 4096 <= Dq -> Dq + 8 * len <= 140737479966720 -> 1 <= len ->
  17591916560912 <= (E - 136) / 8 /\ (E - 136) / 8 + 1 <= 17592186044416 /\ Dq / 8 * 8 = Dq /\ 0 <= Dq / 8 /\ Dq / 8 + len <= 17592184995840.
Proof. intros. lia. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma sh_not_FPZ M : zctx M -> forall a, 2147450880 <= a < 17594333495296 -> ~ FPZ a.
Proof.
  intros C a Ha. pose proof (zc_E _ C) as ER. pose proof (zc_q _ C) as (_ & _ & _ & NQ & _). pose proof (zc_n _ C) as NL.
  unfold FPZ, nsh in *. intros [X|X]; clear - X Ha ER NQ NL; lia.
Qed.
Lemma img_not_FPZ M : zctx M -> forall a, 65536 <= a < 6504448 -> ~ FPZ a.
Proof.
  intros C a Ha. pose proof (zc_E _ C) as ER. pose proof (zc_q _ C) as (_ & _ & _ & _ & NQ). pose proof (zc_n _ C) as NL.
  unfold FPZ, oim in *. intros [X|X]; clear - X Ha ER NQ NL; lia.
Qed.

Lemma zctx_keep M0 Mk : zctx M0 -> zagree M0 Mk -> zctx Mk.
Proof.
  intros C LA. pose proof LA as [MG AG]. pose proof C as [ER EA NL FW (IMG & S1 & S2) VQ VZ (QR1 & QR2 & QR8 & QNS & QOI) QW QZ AP].
  pose proof (zdiv EA ER QR8 QR1 QR2 ltac:(clear - NL; lia)) as (D1 & D2 & D3 & D4 & D5).
  constructor; try assumption.
  - eapply L5.writable_grows; eassumption.
  - split. { intros i Hi. rewrite AG. apply IMG. exact Hi. lia. apply (img_not_FPZ M0 C). lia. }
    split. { eapply L5C.u64_at_agree. 4: exact S1. 2: lia. 2: lia. intros j Hj. apply AG. lia. apply (img_not_FPZ M0 C). lia. }
    unfold L5.u32_at in *. rewrite (L5C.rdn_agree RSEGS M0 Mk 4 911168 ltac:(lia) ltac:(cbn; lia)). exact S2. intros i Hi. apply AG. cbn in Hi; lia. apply (img_not_FPZ M0 C). cbn in Hi; lia.
  - eapply L5C.u64_at_agree. 4: exact VQ. 2: lia. 2: lia. intros j Hj. apply AG. lia. unfold FPZ. clear - Hj AP NL. lia.
  - apply (L5KA.zeros_at_agree1 M0 Mk). 2: exact VZ. intros i Hi. apply AG. lia. apply (sh_not_FPZ M0 C). lia.
  - split. exact QR1. split. exact QR2. split. exact QR8. split. exact QNS. exact QOI.
  - eapply L5.writable_grows; eassumption.
  - apply (L5KA.zeros_at_agree1 M0 Mk). 2: exact QZ. intros i Hi. apply AG. lia. apply (sh_not_FPZ M0 C). lia.
Qed.

(* [comment removed for export] *)
Definition zkept : list nat := [3; 4; 18; 20; 22; 24; 25; 26; 27]%nat.
Definition zregs (R0 Rk : bvmap 5 word) (i : Z) : Prop :=
  getr Rk (reg 2) = Z_to_bv 64 SPA /\ getr Rk (reg 8) = Z_to_bv 64 E /\ getr Rk (reg 9) = Z_to_bv 64 SPA /\ getr Rk (reg 23) = Z_to_bv 64 2147450880 /\
  getr Rk (reg 19) = Z_to_bv 64 i /\ getr Rk (reg 21) = Z_to_bv 64 18446744073709551615 /\ (forall x, In x zkept -> getr Rk (reg x) = getr R0 (reg x)).
Definition zdone (R0 R' : bvmap 5 word) : Prop :=
  getr R' (reg 2) = Z_to_bv 64 SPA /\ getr R' (reg 8) = Z_to_bv 64 E /\ getr R' (reg 9) = Z_to_bv 64 SPA /\ getr R' (reg 23) = Z_to_bv 64 2147450880 /\
  (forall x, In x zkept -> getr R' (reg x) = getr R0 (reg x)).

Lemma ziter (fx : FPState) R0 Rk Mk i : zctx Mk -> zregs R0 Rk i -> 0 <= i < len ->
  exists (fx' : FPState) R' M', zagree Mk M' /\
    ((i = 0 /\ msteps RSEGS (st fx Rk 0x9319c Mk) (st fx' R' 0x931c4 M') /\ zdone R0 R')
     \/ (1 <= i /\ msteps RSEGS (st fx Rk 0x9319c Mk) (st fx' R' 0x9319c M') /\ zregs R0 R' (i - 1))).
Proof.
  intros C (h2 & h8 & h9 & h23 & h19 & h21 & hK) Hi.
  pose proof C as [ER EA NL FW (IMG & S1 & S2) VQ VZ (QR1 & QR2 & QR8 & QNS & QOI) QW QZ AP].
  unfold nsh, oim in *.
  pose proof (zdiv EA ER QR8 QR1 QR2 ltac:(clear - NL; lia)) as (D1 & D2 & D3 & D4 & D5).
  assert (ER' : 140735332487632 <= E <= 140737488355328 /\ 0 <= E < 2 ^ 64) by (clear - ER; lia). destruct ER' as [ER' ERG].
  assert (EAL : aligned E 32) by exact EA.
  assert (DQAL : aligned Dq 8) by exact QR8.
  assert (QV : 4096 <= Dq <= 140737488355328 /\ 0 <= Dq < 2 ^ 64 /\ 1 <= len <= 134217728 /\ 0 <= len < 2 ^ 64 /\ 4104 <= Dq + 8 * len <= 140737479966720) by (clear - QR1 QR2 NL; lia).
  destruct QV as (QV1 & QV2 & QV3 & QV4 & QV5).
  assert (QF1 : Dq + 8 * len <= Dq / 8 + 2147450880 \/ Dq / 8 + 2147450880 + len <= Dq) by (clear - D3 D4 D5 QNS QR1 QR2 NL; lia).
  assert (QF2 : E - 400 + 400 <= Dq \/ Dq + 8 * len <= E - 400) by (clear - AP; lia).
  assert (QF3 : E - 400 + 400 <= Dq / 8 + 2147450880 \/ Dq / 8 + 2147450880 + len <= E - 400) by (clear - D4 D5 ER; lia).
  assert (QF5 : 65536 + 6438912 <= Dq \/ Dq + 8 * len <= 65536) by (clear - QOI; lia).
  destruct (Z.eq_dec i 0) as [I0|I0].
  - subst i.
    pose proof (v5G5Ll_conc fx Rk Mk (fun j => match j with 2%nat => E | 58%nat => U Rk 1 | 68%nat => Dq | 69%nat => len | _ => 0 end)) as P. cbn beta iota in P.
    feed P ltac:(first [apply UR | apply U_to | sc ]).
    destruct P as (fx1 & R1 & M1 & MG1 & _ & pFZ & (pMS & pKS & _)).
    exists fx1, R1, M1. split.
    { split. exact MG1. intros a Ha Hn. apply pFZ. exact Ha. intros X. apply Hn. unfold FPZ. right. clear - X NL; lia. intros X. apply Hn. unfold FPZ. left. clear - X; lia. }
    left. split. reflexivity. split. exact pMS.
    unfold zdone. rewrite (pKS 2%nat), (pKS 8%nat), (pKS 9%nat), (pKS 23%nat) by inl.
    split. exact h2. split. exact h8. split. exact h9. split. exact h23.
    intros x Hx. rewrite <- (hK x Hx). apply pKS. revert Hx. apply (L5K.incl_b zkept). vm_compute; reflexivity.
  - assert (IR : 1 <= i <= 134217727 /\ 1 <= len - i <= 134217728 /\ 0 <= i < 2 ^ 64) by (clear - Hi I0 NL; lia). destruct IR as (IR1 & IR2 & IR3).
    pose proof (v5G5Lm_conc fx Rk Mk (fun j => match j with 2%nat => E | 58%nat => U Rk 1 | 68%nat => Dq | 69%nat => len | 79%nat => i | _ => 0 end)) as P. cbn beta iota in P.
    feed P ltac:(first [apply UR | apply U_to | sc ]).
    destruct P as (fx1 & R1 & M1 & MG1 & _ & pFZ & (pMS & pKS & _ & _ & _ & _ & _ & _ & p19 & _)).
    exists fx1, R1, M1. split.
    { split. exact MG1. intros a Ha Hn. apply pFZ. exact Ha. intros X. apply Hn. unfold FPZ. right. clear - X Hi; lia. intros X. apply Hn. unfold FPZ. left. clear - X; lia. }
    right. split. exact (proj1 IR1). split. exact pMS.
    unfold zregs. rewrite (pKS 2%nat), (pKS 8%nat), (pKS 9%nat), (pKS 23%nat), (pKS 21%nat) by inl.
    split. exact h2. split. exact h8. split. exact h9. split. exact h23. split. exact p19. split. exact h21.
    intros x Hx. rewrite <- (hK x Hx). apply pKS. revert Hx. apply (L5K.incl_b zkept). vm_compute; reflexivity.
Qed.

Lemma gzero_iter (j : nat) : forall (fx : FPState) R0 Rk Mk, zctx Mk -> zregs R0 Rk (Z.of_nat j) -> Z.of_nat j < len ->
  exists (fx' : FPState) R' M', msteps RSEGS (st fx Rk 0x9319c Mk) (st fx' R' 0x931c4 M') /\ zagree Mk M' /\ zdone R0 R'.
Proof.
  induction j as [|j IH]; intros fx R0 Rk Mk C HR Hj.
  - destruct (ziter fx R0 Rk Mk 0 C HR ltac:(clear - Hj; lia)) as (fx' & R' & M' & LA & [(_ & MS & K5)|(E2 & _)]).
    + exists fx', R', M'. split. exact MS. split. exact LA. exact K5.
    + exfalso. clear - E2. lia.
  - destruct (ziter fx R0 Rk Mk (Z.of_nat (Datatypes.S j)) C HR ltac:(clear - Hj; lia)) as (fx1 & R1 & M1 & LA & [(E1 & _)|(_ & MS & HR')]).
    + exfalso. clear - E1. lia.
    + replace (Z.of_nat (Datatypes.S j) - 1) with (Z.of_nat j) in HR' by (clear; lia).
      destruct (IH fx1 R0 R1 M1 (zctx_keep Mk M1 C LA) HR' ltac:(clear - Hj; lia)) as (fx' & R' & M' & MS' & LA' & K5).
      exists fx', R', M'. split. eapply msteps_trans. exact MS. exact MS'. split. eapply zagree_trans. exact LA. exact LA'. exact K5.
Qed.

(* [comment removed for export] *)
Theorem gzero_run (fx : FPState) R M0 : zctx M0 -> zregs R R (len - 1) ->
  exists (fx' : FPState) R' M', msteps RSEGS (st fx R 0x9319c M0) (st fx' R' 0x931c4 M') /\ zagree M0 M' /\ zdone R R'.
Proof.
  intros C HR. pose proof (zc_n _ C) as NL.
  apply (gzero_iter (Z.to_nat (len - 1)) fx R R M0 C).
  - rewrite Z2Nat.id by (clear - NL; lia). exact HR.
  - rewrite Z2Nat.id by (clear - NL; lia). clear; lia.
Qed.
End LOOP.
End SCFG_1.
End L5ADVGZ.
