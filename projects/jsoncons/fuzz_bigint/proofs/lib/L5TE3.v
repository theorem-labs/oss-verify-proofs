(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface
     L5Defs L5Core L5CoreSpecs.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.CJ.Lib Require Import MState Mem Cells Step Frame Exec Tac.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.CJ.Bridge Require Import BrRegs BrBase BrXfer.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.CJ.Ref Require Import F_syscalls RMallocRep.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import L5TopKit L5TopStretch L5TStrS L5TE3W.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)

Module L5TE3.
Import L5CS.
Abbreviation RSEGS := Plain.M.loaded_segments.
Section SCFG_1.
Context {SCFG_P : ScfgP}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ASSERT_THROW : Z := 0x21470.     (* [comment removed for export] *)
Definition RESIZE_RET1 : Z := 0x210e0.      (* [comment removed for export] *)
Definition RESIZE_HUGE_SCR : Z := 128.      (* [comment removed for export] *)
Definition MAXW : Z := 2 ^ 61 - 1.          (* [comment removed for export] *)
Definition U (R : bvmap 5 word) (k : Z) : Z := bv_unsigned (getr R (Z_to_bv 5 k)).

(* [comment removed for export] *)
Definition resize_huge_at (M M' : word -> option byte) (R R' : bvmap 5 word) (o sp n : Z) (b : L5.bigobj) : Prop :=
  (* [comment removed for export] *)
     getr R' 2%bv = Z_to_bv 64 (sp - 128) /\ getr R' 3%bv = getr R 3%bv /\ getr R' 4%bv = getr R 4%bv
  /\ getr R' 1%bv = Z_to_bv 64 RESIZE_RET1
  /\ getr R' 8%bv = Z_to_bv 64 o /\ getr R' 9%bv = Z_to_bv 64 n /\ getr R' 18%bv = Z_to_bv 64 (Z.of_nat (L5.bo_len b))
  /\ getr R' 19%bv = getr R 19%bv /\ getr R' 20%bv = getr R 20%bv /\ getr R' 21%bv = getr R 21%bv /\ getr R' 22%bv = getr R 22%bv
  /\ getr R' 23%bv = getr R 23%bv /\ getr R' 24%bv = getr R 24%bv /\ getr R' 25%bv = getr R 25%bv /\ getr R' 26%bv = getr R 26%bv
  /\ getr R' 27%bv = getr R 27%bv
  /\ getr R' 10%bv = Z_to_bv 64 16 /\ getr R' 11%bv = Z_to_bv 64 n /\ getr R' 12%bv = Z_to_bv 64 MAXW
  (* [comment removed for export] *)
  /\ L5.u64_at RSEGS M' (sp - 8) (U R 1) /\ L5.u64_at RSEGS M' (sp - 16) (U R 8)
  /\ L5.u64_at RSEGS M' (sp - 24) (U R 9) /\ L5.u64_at RSEGS M' (sp - 32) (U R 18)
  (* [comment removed for export] *)
  /\ L5.u64_at RSEGS M' (sp - 72) RESIZE_RET1 /\ L5.u64_at RSEGS M' (sp - 80) o /\ L5.u64_at RSEGS M' (sp - 88) n
  /\ L5.u64_at RSEGS M' (sp - 96) (Z.of_nat (L5.bo_len b))
  /\ L5.u64_at RSEGS M' (sp - 104) (U R 19) /\ L5.u64_at RSEGS M' (sp - 112) (U R 20) /\ L5.u64_at RSEGS M' (sp - 120) (U R 21)
  (* [comment removed for export] *)
  /\ L5.frame_but [(sp - 128, 128)] M M' /\ mem_grows M M'.

Definition resize_huge_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (o sp n : Z) (b : L5.bigobj),
    m_halted model = None -> m_vm_lazy model = [] ->
    getr R 10%bv = Z_to_bv 64 o -> getr R 11%bv = Z_to_bv 64 n -> MAXW <= n < 2 ^ 64 ->
    getr R 2%bv = Z_to_bv 64 sp -> 0x7fff7f800000 + 128 <= sp -> sp <= 2 ^ 47 -> L5.defined M (sp - 128) 128 ->
    L5.big_at RSEGS M o b -> L5.bo_dyn b = true -> 0 <= o -> o + 32 <= 2 ^ 47 -> (o + 32 <= sp - 128 \/ sp <= o) ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte),
        resize_huge_at M M' R R' o sp n b -> srealizes RSEGS SCFG (cfg R' ASSERT_THROW M' model) K) ->
    srealizes RSEGS SCFG (cfg R RESIZE M model) K.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac greg REQ k := rewrite (TK.getr_of_eqv_lit _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ k _ REQ ltac:(lia)); cbn [nth Z.to_nat Pos.to_nat Pos.iter_op Nat.add].

Lemma u64_of_ro : forall m A w cs, ro_cells rsegs m A (C8 w :: cs) -> L5.u64_at rsegs m A (bv_unsigned w).
Proof.
  intros m A w cs [WF HB]. unfold L5.u64_at. rewrite definitions.Z_to_bv_bv_unsigned.
  cbn [cells_bytes cbytes] in HB. apply bytes_at_app in HB. destruct HB as [HB _].
  pose proof HB as (HA & Hn & _).
  change (word_to_le_bytes 8 w) with (le8 w) in HB, Hn |- *. rewrite <- (TSS.rdn_of_bytes_at m (le8 w) A); [reflexivity| lia| |exact HB].
  change (length (le8 w)) with 8%nat in Hn |- *. lia.
Qed.

(* [comment removed for export] *)
Local Tactic Notation "cell_u64" constr(H) integer(off) :=
  let H' := fresh in
  pose proof (TK.ro_of_rw _ _ _ H) as H';
  do off (apply TK.ro_cells_skip1 in H'; cbn [csize Z.of_nat Pos.of_succ_nat Pos.succ] in H');
  apply u64_of_ro in H'; rewrite ?L5.unsigned_lit in H' by lia;
  match type of H' with L5.u64_at _ _ ?a _ => ring_simplify a in H' end; exact H'.

Theorem resize_huge_ok : resize_huge_spec.
Proof.
  intros fx R M model K o sp n b Mh Ml R10 R11 Hn R2 SLO SHI DEF BIG DYN Ho Oh OAP CONT.
  unfold MAXW in Hn.
  destruct b as [fb len st]. unfold L5.bo_dyn in DYN. cbn [L5.bo_fb] in DYN.
  destruct BIG as (FB & Hfb & LEN & ST). cbn [L5.bo_fb L5.bo_len L5.bo_st] in FB, Hfb, LEN, ST.
  destruct st as [v0 v1|cap q]. { destruct ST as (TB & _). rewrite DYN in TB. discriminate. }
  destruct ST as (_ & CAP & _ & LC & HC & _).
  assert (ST0 : stk rsegs M (sp - 128) sp).
  { apply TK.stk_of_defined; [replace (sp - (sp - 128)) with 128 by lia; exact DEF| lia| lia| lia]. }
  eapply (TK.srz_evt_canonMS _ R _ M model K Mh Ml).
  { unfold canon_regs. rewrite R10, R11, R2.
    eapply (TE3W.e3x) with (lo := sp - 128) (fb := fb) (len := Z.of_nat len) (cap := cap);
      unfold TE3W.MAXW; rewrite ?L5.unsigned_lit by lia.
    - exact ST0.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - rewrite Z.add_0_r. apply TK.ro_cells_u8; [exact FB| lia| lia].
    - exact Hfb.
    - exact DYN.
    - apply TK.ro_cells_u64; [exact LEN| lia| lia].
    - apply TK.ro_cells_u64; [exact CAP| lia| lia].
    - lia.
    - lia. }
  2:{ intros ms' (j0 & j1 & m' & -> & _). eexists _, _, _. reflexivity. }
  intros R1c pc1 m1 R1 (j0 & j1 & m' & E & FR & MU & WM & MG & ST1) REQ. inversion E; subst R1c pc1 m1; clear E.
  unfold TE3W.ASSERT_THROW, TE3W.RESIZE_RET1, TE3W.MAXW in REQ, FR. rewrite ?L5.unsigned_lit in REQ, FR, MU, ST1 by lia.
  apply CONT. unfold resize_huge_at, U, RESIZE_RET1, MAXW. cbn [L5.bo_len].
  repeat match goal with |- _ /\ _ => split end.
  - greg REQ 2. unfold wz. f_equal; lia.
  - greg REQ 3. reflexivity.
  - greg REQ 4. reflexivity.
  - greg REQ 1. reflexivity.
  - greg REQ 8. reflexivity.
  - greg REQ 9. reflexivity.
  - greg REQ 18. reflexivity.
  - greg REQ 19. reflexivity.
  - greg REQ 20. reflexivity.
  - greg REQ 21. reflexivity.
  - greg REQ 22. reflexivity.
  - greg REQ 23. reflexivity.
  - greg REQ 24. reflexivity.
  - greg REQ 25. reflexivity.
  - greg REQ 26. reflexivity.
  - greg REQ 27. reflexivity.
  - greg REQ 10. reflexivity.
  - greg REQ 11. reflexivity.
  - greg REQ 12. reflexivity.
  - cell_u64 FR 12.
  - cell_u64 FR 11.
  - cell_u64 FR 10.
  - cell_u64 FR 9.
  - cell_u64 FR 7.
  - cell_u64 FR 6.
  - cell_u64 FR 5.
  - cell_u64 FR 4.
  - cell_u64 FR 3.
  - cell_u64 FR 2.
  - cell_u64 FR 1.
  - (* [comment removed for export] *) intros x OUT. apply MU. cbn. pose proof (bv_unsigned_in_range 64 x) as Hx. unfold bv_modulus in Hx. cbn in Hx.
    specialize (OUT (sp - 128, 128) (or_introl eq_refl)). unfold L5.in_rng in OUT. cbn [fst snd] in OUT.
    split; [lia| exact I].
  - exact MG.
Qed.
End SCFG_1.
End L5TE3.
