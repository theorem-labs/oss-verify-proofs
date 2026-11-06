(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OSSVerify.Proofs.boost_beast.http_request.lib.Ref Require Import RSegs RMalloc_iface_stmt HeapSR_iface XRep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition HE_END_OF_STREAM := 1.   Definition HE_PARTIAL_MESSAGE := 2.   Definition HE_NEED_MORE := 3.
Definition HE_BUFFER_OVERFLOW := 7. Definition HE_HEADER_LIMIT := 8.      Definition HE_BODY_LIMIT := 9.
Definition HE_BAD_LINE_ENDING := 11. Definition HE_BAD_METHOD := 12.     Definition HE_BAD_TARGET := 13.
Definition HE_BAD_VERSION := 14.   Definition HE_BAD_FIELD := 17.        Definition HE_BAD_VALUE := 18.
Definition HE_BAD_CONTENT_LENGTH := 19. Definition HE_BAD_TRANSFER_ENCODING := 20. Definition HE_BAD_CHUNK := 21.
Definition HE_BAD_CHUNK_EXTENSION := 22. Definition HE_MULTIPLE_CONTENT_LENGTH := 24.
Definition HE_FIELD_NAME_TOO_LARGE := 27. Definition HE_FIELD_VALUE_TOO_LARGE := 28.

(* [comment removed for export] *)
Definition LOC_TCNE_NAME   := 0x7ae50.  Definition LOC_TCNE_VALUE := 0x7ae68.      (* [comment removed for export] *)
Definition LOC_RDPUT_OVF   := 0x7b6a0.                                              (* [comment removed for export] *)
Definition LOC_RS_OVF      := 0x7bd08.  Definition LOC_RS_EOS := 0x7bd20.          (* [comment removed for export] *)
Definition LOC_PUT_NM      := 0x7bd38.                                              (* [comment removed for export] *)
Definition LOC_PSL_HL      := 0x7bd50.                                              (* [comment removed for export] *)
Definition LOC_ISL_BADVER  := 0x7bd68.  Definition LOC_ISL_NM := 0x7bd80.  Definition LOC_ISL_BADVER2 := 0x7bd98.
Definition LOC_PM_NM := 0x7bdb0. Definition LOC_PM_BAD := 0x7bdc8. Definition LOC_PM_EMPTY := 0x7bde0.   (* [comment removed for export] *)
Definition LOC_PT_NM := 0x7bdf8. Definition LOC_PT_BAD := 0x7be10. Definition LOC_PT_EMPTY := 0x7be28.   (* [comment removed for export] *)
Definition LOC_PV_NM := 0x7be40. Definition LOC_PV_H := 0x7be58. Definition LOC_PV_T1 := 0x7be70. Definition LOC_PV_T2 := 0x7be88.
Definition LOC_PV_P := 0x7bea0. Definition LOC_PV_SLASH := 0x7beb8. Definition LOC_PV_D1 := 0x7bed0. Definition LOC_PV_DOT := 0x7bee8.
Definition LOC_PV_D2 := 0x7bf00.                                                    (* [comment removed for export] *)
Definition LOC_PF_HL := 0x7bf18.                                                    (* [comment removed for export] *)
Definition LOC_IPF_NM := 0x7bf30. Definition LOC_IPF_BADLE := 0x7bf48.              (* [comment removed for export] *)
Definition LOC_PFD_0 := 0x7bf60. Definition LOC_PFD_1 := 0x7bf78. Definition LOC_PFD_2 := 0x7bf90. Definition LOC_PFD_3 := 0x7bfa8.
Definition LOC_PFD_4 := 0x7bfc0. Definition LOC_PFD_5 := 0x7bfd8. Definition LOC_PFD_6 := 0x7bff0. Definition LOC_PFD_7 := 0x7c008.
Definition LOC_PFD_8 := 0x7c020. Definition LOC_PFD_9 := 0x7c038. Definition LOC_PFD_10 := 0x7c050. Definition LOC_PFD_11 := 0x7c068.
                                                                                    (* [comment removed for export] *)
Definition LOC_TTE_NM := 0x7c080. Definition LOC_TTE_NM2 := 0x7c098. Definition LOC_TTE_BADLE := 0x7c0b0. (* [comment removed for export] *)
Definition LOC_DF_TE1 := 0x7c0c8. Definition LOC_DF_TE2 := 0x7c0e0. Definition LOC_DF_BADVAL := 0x7c0f8.
Definition LOC_DF_BADCL := 0x7c110. Definition LOC_DF_MULTICL := 0x7c128.           (* [comment removed for export] *)
Definition LOC_FH_TE1 := 0x7c140. Definition LOC_FH_TE2 := 0x7c158. Definition LOC_FH_BODYLIM := 0x7c170. (* [comment removed for export] *)
Definition LOC_PBE_BODYLIM := 0x7c188.                                              (* [comment removed for export] *)
Definition LOC_PCH_NM := 0x7c1a0. Definition LOC_PCH_BADCRLF := 0x7c1b8. Definition LOC_PCH_NM2 := 0x7c1d0.
Definition LOC_PCH_BADHEX := 0x7c1e8. Definition LOC_PCH_EXT8K := 0x7c200. Definition LOC_PCH_BODYLIM := 0x7c218.
Definition LOC_PCH_EXTJUNK := 0x7c230. Definition LOC_FEOL_BADLE := 0x7c248.        (* [comment removed for export] *)
Definition LOC_PCE_0 := 0x7c260. Definition LOC_PCE_1 := 0x7c278. Definition LOC_PCE_2 := 0x7c290. Definition LOC_PCE_3 := 0x7c2a8.
Definition LOC_DBP_FB := 0x7c2c0.                                                   (* [comment removed for export] *)
Definition LOC_TS_EOF := 0x7c2d8.                                                   (* [comment removed for export] *)
Definition LOC_PEOF_1 := 0x7c2f0. Definition LOC_PEOF_2 := 0x7c308.                 (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition TAB_IS_TOKEN_CHAR : list Z := [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 1; 0; 1; 1; 1; 1; 1; 0; 0; 1; 1; 0; 1; 1; 0; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 0; 0; 0; 0; 0; 0; 0; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 0; 0; 0; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 0; 1; 0; 1; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0]%Z.
(* [comment removed for export] *)
Definition TAB_IS_PATHCHAR : list Z := [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 0; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1]%Z.
(* [comment removed for export] *)
Definition TAB_IS_TOKEN_LIT : list Z := [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 1; 0; 1; 1; 1; 1; 1; 0; 0; 1; 1; 0; 1; 1; 0; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 0; 0; 0; 0; 0; 0; 0; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 0; 0; 0; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 0; 1; 0; 1; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0]%Z.
(* [comment removed for export] *)
Definition TAB_UNHEX : list Z := [-1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; 0; 1; 2; 3; 4; 5; 6; 7; 8; 9; -1; -1; -1; -1; -1; -1; -1; 10; 11; 12; 13; 14; 15; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; 10; 11; 12; 13; 14; 15; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1]%Z.
(* [comment removed for export] *)
Definition TAB_IS_QPCHAR : list Z := [0; 0; 0; 0; 0; 0; 0; 0; 0; 1; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 0; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1]%Z.
(* [comment removed for export] *)
Definition TAB_IS_QDCHAR : list Z := [0; 0; 0; 0; 0; 0; 0; 0; 0; 1; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 1; 1; 0; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 0; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 0; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1]%Z.


(* [comment removed for export] *)
Definition is_tchar (c : Z) : bool := negb (nth (Z.to_nat c) TAB_IS_TOKEN_CHAR 0 =? 0).
Definition is_pathchar (c : Z) : bool := negb (nth (Z.to_nat c) TAB_IS_PATHCHAR 0 =? 0).
Definition unhex (c : Z) : Z := nth (Z.to_nat c) TAB_UNHEX (-1).
Definition is_qpchar (c : Z) : bool := negb (nth (Z.to_nat c) TAB_IS_QPCHAR 0 =? 0).
Definition is_qdchar (c : Z) : bool := negb (nth (Z.to_nat c) TAB_IS_QDCHAR 0 =? 0).
Definition is_digitc (c : Z) : bool := (48 <=? c) && (c <=? 57).
Definition is_ws (c : Z) : bool := (c =? 32) || (c =? 9).
(* [comment removed for export] *)
Definition is_ctl (c : Z) : bool := ((c <? 32) && negb (c =? 9)) || (c =? 127).
(* [comment removed for export] *)
Definition lowerc (c : Z) : Z := if (65 <=? c) && (c <=? 90) then c + 32 else c.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition zb (b : byte) : Z := bv_unsigned b.
Definition zbytes (bs : list byte) : list Z := map zb bs.

(* [comment removed for export] *)
Fixpoint find_ix (f : Z -> bool) (bs : list byte) : option nat :=
  match bs with
  | [] => None
  | b :: bs' => if f (zb b) then Some 0%nat else option_map S (find_ix f bs')
  end.

Lemma find_ix_Some : forall f bs i, find_ix f bs = Some i ->
  (i < length bs)%nat /\ (exists b, nth_error bs i = Some b /\ f (zb b) = true)
  /\ (forall j b, (j < i)%nat -> nth_error bs j = Some b -> f (zb b) = false).
Proof.
  intros f bs. induction bs as [|b bs IH]; intros i H; cbn in H; [discriminate|].
  destruct (f (zb b)) eqn:Fb.
  - inversion H; subst. cbn. split; [lia|]. split; [exists b; split; [reflexivity|exact Fb]|].
    intros j b' Hj. lia.
  - destruct (find_ix f bs) as [i'|] eqn:E; cbn in H; [|discriminate]. inversion H; subst.
    destruct (IH i' eq_refl) as (L & (b1 & N1 & F1) & R). cbn. split; [lia|]. split; [exists b1; split; assumption|].
    intros j b' Hj N. destruct j as [|j]; cbn in N. { inversion N; subst. exact Fb. } apply (R j b'); [lia| exact N].
Qed.

Lemma find_ix_None : forall f bs, find_ix f bs = None -> forall j b, nth_error bs j = Some b -> f (zb b) = false.
Proof.
  intros f bs. induction bs as [|b bs IH]; intros H j b' N; [destruct j; discriminate|].
  cbn in H. destruct (f (zb b)) eqn:Fb; [discriminate|].
  destruct (find_ix f bs) eqn:E; [discriminate|].
  destruct j as [|j]; cbn in N. { inversion N; subst; exact Fb. } exact (IH eq_refl j b' N).
Qed.

Lemma find_ix_first : forall f bs j b,
  (forall j' b', (j' < j)%nat -> nth_error bs j' = Some b' -> f (zb b') = false) ->
  nth_error bs j = Some b -> f (zb b) = true -> find_ix f bs = Some j.
Proof.
  intros f bs. induction bs as [|x bs IH]; intros j b PREV N Fb; [destruct j; discriminate|].
  destruct j as [|j]; cbn in N.
  - inversion N; subst. cbn. rewrite Fb. reflexivity.
  - cbn. rewrite (PREV 0%nat x) by (try lia; reflexivity).
    rewrite (IH j b); [reflexivity| | exact N | exact Fb].
    intros j' b' Hj' N'. apply (PREV (S j') b'); [lia| exact N'].
Qed.

Lemma find_ix_all : forall f bs,
  (forall j b, nth_error bs j = Some b -> f (zb b) = false) -> find_ix f bs = None.
Proof.
  intros f bs. induction bs as [|x bs IH]; intros ALL; [reflexivity|]. cbn.
  rewrite (ALL 0%nat x eq_refl). rewrite IH; [reflexivity|]. intros j b N. exact (ALL (S j) b N).
Qed.

Lemma zb_range : forall b, 0 <= zb b < 256.
Proof. intros b. unfold zb. pose proof (bv_unsigned_in_range 8 b) as H. unfold bv_modulus in H. cbn in H. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section HCW.
  Context {HCEIL : HeapCeil}.

(* [comment removed for export] *)
Record pcore := mkPC {
  pc_blim_has : Z ; pc_blim : Z ; pc_len : Z ; pc_len0 : Z ; pc_skip : Z ;
  pc_hlim : Z ; pc_state : Z ; pc_f : Z }.

Definition ParserCoreCells (c : pcore) (pad7 pad2 : list byte) : list cell :=
  [C8 (wz VP_PARSER); C1 (b8 (pc_blim_has c)); CB 7 pad7; C8 (wz (pc_blim c));
   C8 (wz (pc_len c)); C8 (wz (pc_len0 c)); C8 (wz 0); C8 (wz 0); C8 (wz (pc_skip c));
   C4 (wz (pc_hlim c)); C2 (wz 0); CB 2 pad2; C4 (wz (pc_state c)); C4 (wz (pc_f c))].

Definition pcore_ok (c : pcore) : Prop :=
  (pc_blim_has c = 0 \/ pc_blim_has c = 1) /\ 0 <= pc_blim c <= 2^20 /\ 0 <= pc_len c < 2^64 /\ 0 <= pc_len0 c < 2^64
  /\ 0 <= pc_skip c < 2^64 /\ 0 <= pc_hlim c <= 8194 /\ In (pc_state c) [0;1;2;3;4;7;8;9;10;11] /\ 0 <= pc_f c < 2^14.

Definition ParserCore (m : mem) (P : Z) (c : pcore) : Prop :=
  exists pad7 pad2, rw_cells rsegs m P (ParserCoreCells c pad7 pad2) /\ pcore_ok c.

(* [comment removed for export] *)
Definition FL_EAGER := 2. Definition FL_HASBODY := 8. Definition FL_HTTP11 := 16. Definition FL_EXPECT_CRLF := 64.
Definition FL_CONN_CLOSE := 128. Definition FL_CONN_UPGRADE := 256. Definition FL_CONN_KEEPALIVE := 512.
Definition FL_CONTENT_LENGTH := 1024. Definition FL_CHUNKED := 2048. Definition FL_UPGRADE := 4096. Definition FL_TE := 8192.

(* [comment removed for export] *)
Definition CharBuf (m : mem) (a : Z) (bs : list byte) (junk : list byte) : Prop :=
  rw_cells rsegs m a [C8 (wz (Z.of_nat (length bs))); CB (length bs) bs; CB (4096 - length bs) junk]
  /\ (length bs <= 4096)%nat.

(* [comment removed for export] *)
Definition TokItCells (vp vl it first last : Z) : list cell :=
  [C8 (wz vp); C8 (wz vl); C8 (wz it); C8 (wz first); C8 (wz last)].
Definition OptItCells (lst it vp vl err : Z) (pad7 : list byte) : list cell :=
  [C8 (wz lst); C8 (wz it); C8 (wz vp); C8 (wz vl); C1 (b8 err); CB 7 pad7].

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition FieldsHdrCells (root lmost rmost : Z) (color : Z) (lnext lprev : Z) (mp ml tp tl ver vb : Z) (pad4 : list byte)
  : list cell :=
  [C8 (wz root); C8 (wz lmost); C8 (wz rmost); C4 (wz color); CB 4 pad4;
   C8 (wz lnext); C8 (wz lprev); C8 (wz mp); C8 (wz ml); C8 (wz tp); C8 (wz tl); C4 (wz ver); C4 (wz vb)].

(* [comment removed for export] *)
Definition MBufHdrCells (lnext lprev out insz inpos outpos outend : Z) : list cell :=
  [C8 (wz 0x1fffffffffffffff); C8 (wz lnext); C8 (wz lprev); C8 (wz out); C8 (wz insz); C8 (wz inpos);
   C8 (wz outpos); C8 (wz outend)].

End HCW.
