(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA
     BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5Words L5DefsAB0 L5CoreAB0 L5CoreSpecsAB0 L5StepAB0.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5BLK.
Import L5A. Import L5CA. Import L5CSA. Import L5SA.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Section SCFG_1.
Context {SCFG_P : ScfgP}.

Definition U (R : bvmap 5 word) (k : nat) : Z := bv_unsigned (getr R (reg k)).
Lemma UR R k : 0 <= U R k < 2 ^ 64. Proof. unfold U. apply BL.bvu_range. Qed.
Lemma U_of R k z : getr R (reg k) = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 -> U R k = z.
Proof. intros H Hz. unfold U. rewrite H. apply L5.unsigned_lit. exact Hz. Qed.
Lemma U_to R k : getr R (reg k) = Z_to_bv 64 (U R k). Proof. unfold U. symmetry. apply Z_to_bv_bv_unsigned. Qed.

Lemma u32_at_agree1 M M' a v : (forall i, a <= i < a + 4 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) -> 0 <= a -> a + 4 <= 2 ^ 64 ->
  L5.u32_at RSEGS M a v -> L5.u32_at RSEGS M' a v.
Proof.
  intros HA Ha H4 Hu. unfold L5.u32_at in *. rewrite <- Hu. apply (L5C.rdn_agree RSEGS M M' 4 a). lia. cbn; lia.
  intros i Hi. apply HA. cbn in Hi. lia.
Qed.

Lemma KS_trans (KS : list nat) R R' R'' : (forall x, In x KS -> getr R' (reg x) = getr R (reg x)) -> (forall x, In x KS -> getr R'' (reg x) = getr R' (reg x)) ->
  forall x, In x KS -> getr R'' (reg x) = getr R (reg x).
Proof. intros A B x Hx. rewrite (B x Hx). apply A. exact Hx. Qed.

Lemma in_firstn {A} (x : A) : forall n (l : list A), In x (firstn n l) -> In x l.
Proof. induction n as [|n IH]; intros l H. destruct H. destruct l as [|a l]. destruct H. cbn [firstn] in H. destruct H as [<-|H]. left; reflexivity. right. apply IH. exact H. Qed.

(* [comment removed for export] *)
Record mfacts (FRX VO VG : Z) (M : word -> option byte) (sp o d cap : Z) : Prop := MF {
  mf_sp : 140735332487168 + FRX <= sp <= 140737488355328 /\ sp mod 16 = 0;
  mf_w : L5.writable RSEGS M (sp - FRX) FRX;
  mf_st : L5.img_clear M 860160 884736 /\ L5.u64_at RSEGS M 911160 2147450880 /\ L5.u32_at RSEGS M 911168 1;
  mf_o : 6504448 <= o <= 140737488355296 /\ o mod 8 = 0 /\ (2147446784 + 17592186048512 <= o \/ o + 32 <= 2147446784) /\ (sp <= o \/ o + 32 <= sp - 4096);
  mf_oz : L5KA.zeros_at M (o / 8 + SB) 4;
  mf_ow : L5.writable RSEGS M o 32;
  mf_d : (4096 <= d /\ d + 8 * cap <= 140737479966720) /\ d mod 8 = 0 /\ (2147446784 + 17592186048512 <= d \/ d + 8 * cap <= 2147446784) /\ 1 <= cap <= 134217728
         /\ (sp <= d \/ d + 8 * cap <= sp - 4096) /\ (o + 16 <= d \/ d + 8 * cap <= o)
         /\ (d + 8 * cap <= d / 8 + SB \/ d / 8 + SB + cap <= d) /\ (d + 8 * cap <= 65536 \/ 6504448 <= d);
  mf_dw : L5.writable RSEGS M d (8 * cap);
  mf_dz : L5KA.zeros_at M (d / 8 + SB) cap;
  mf_vz : L5KA.zeros_at M ((sp - VO) / 8 + SB) VG }.

(* [comment removed for export] *)
Lemma mfacts_keep FRX VO VG M M' sp o d cap :
  0 < FRX <= 4096 -> 0 <= 8 * VG <= VO -> VO <= FRX -> VO mod 8 = 0 ->
  mfacts FRX VO VG M sp o d cap -> mem_grows M M' ->
  (forall i, 0 <= i < 2 ^ 64 -> ~ (d <= i < d + 8 * cap) -> ~ (o <= i < o + 16) -> ~ (sp - FRX <= i < sp) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) -> mfacts FRX VO VG M' sp o d cap.
Proof.
  intros HF HV HVF HV8 [S1 W [I [C1 C2]] O OZ OW D DW DZ VZ] G K.
  constructor; auto.
  - eapply L5.writable_grows; eauto.
  - split. { intros a Ha. rewrite K. apply I. exact Ha. clear - Ha; lia. clear - Ha D O; lia. clear - Ha O; lia. clear - Ha S1 HF; lia. }
    split. eapply L5C.u64_at_agree. 4: exact C1. 2: clear; lia. 2: clear; lia. intros i Hi; apply K. clear - Hi; lia. clear - Hi D O; lia. clear - Hi O; lia. clear - Hi S1 HF; lia.
    eapply u32_at_agree1. 4: exact C2. 2: clear; lia. 2: clear; lia. intros i Hi; apply K. clear - Hi; lia. clear - Hi D O; lia. clear - Hi O; lia. clear - Hi S1 HF; lia.
  - Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    eapply L5KA.zeros_at_agree1. 2: exact OZ. intros i Hi. apply K. clear - Hi O; unfold SB in *; lia. clear - Hi O D; unfold SB in *; lia. clear - Hi O; unfold SB in *; lia. clear - Hi O S1 HF; unfold SB in *; lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  - eapply L5.writable_grows; eauto.
  - eapply L5.writable_grows; eauto.
  - Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    eapply L5KA.zeros_at_agree1. 2: exact DZ. intros i Hi. apply K. clear - Hi D; unfold SB in *; lia. clear - Hi D; unfold SB in *; lia. clear - Hi D O; unfold SB in *; lia. clear - Hi D S1 HF; unfold SB in *; lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  - Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    eapply L5KA.zeros_at_agree1. 2: exact VZ. intros i Hi. apply K.
    clear - Hi S1 HV HVF HF HV8; unfold SB in *; lia. clear - Hi S1 HV HVF HF HV8 D; unfold SB in *; lia. clear - Hi S1 HV HVF HF HV8 O; unfold SB in *; lia. clear - Hi S1 HV HVF HF HV8; unfold SB in *; lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma zeros_of_shadow_zero M lo g a n :
  shadow_zero M lo g -> lo mod 8 = 0 -> a mod 8 = 0 -> 0 <= lo <= a -> (a - lo) / 8 + n <= g -> L5KA.zeros_at M (a / 8 + SB) n.
Proof.
  intros SZ L8 A8 LE HG i Hi. unfold shadow_zero, byte_at in SZ.
  replace (a / 8 + SB + i) with (HeapIfaceA.S lo + ((a - lo) / 8 + i)). 2:{ unfold HeapIfaceA.S, HeapIfaceA.SB, SB. clear - L8 A8 LE. lia. }
  apply SZ. clear - Hi HG LE L8 A8. lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

End SCFG_1.
End L5BLK.
