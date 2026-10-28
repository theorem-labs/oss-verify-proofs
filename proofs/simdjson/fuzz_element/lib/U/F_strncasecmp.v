(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Layout F_memcmp.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition sncc_entry : Z := 0xd11dc.
Definition tolower_entry : Z := 0xbf504.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition sncc_post (ra : word) (sp : Z) (gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (r a1' a2' : word) (m' : mem),
    ms' = MS (mkR ra (Z_to_bv 64 sp) gp tp t0 t1 t2 s0 s1 r a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(sp - 48, sp)] m m' /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo sp.

Definition keepF (P : Prop) : Prop := P.
Local Ltac hide H := lazymatch type of H with ?T => change (keepF T) in H end.
Local Ltac unhide H := unfold keepF in H.

Ltac retlit := try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?x)) _ _ _ _) =>
  replace (ret_pc (Z_to_bv 64 x)) with (Z_to_bv 64 x) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end).

Section Proofs.
Variables (ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
  (m : mem) (sp lo p q : Z) (bp bq : list byte).
Notation n := (Z.of_nat (length bp)).
Notation BP j := (nth (Z.to_nat j) bp (Z_to_bv 8 0)).
Notation BQ j := (nth (Z.to_nat j) bq (Z_to_bv 8 0)).
Hypothesis LEN : length bq = length bp.
Hypothesis P0 : 0 <= p.
Hypothesis Q0 : 0 <= q.
Hypothesis PH : p + n < 2 ^ 63.
Hypothesis QH : q + n < 2 ^ 63.
Hypothesis LOSP : lo + 48 <= sp.
Hypothesis SPH : sp < 2 ^ 63.
Notation POST := (sncc_post ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo m).

Notation ST1 pc x1 x8 x9 x10 x11 x12 x18 x19 m1 :=
  (MS (mkR x1 (Z_to_bv 64 (sp + -48)) gp tp t0 t1 t2 x8 x9 x10 x11 x12 a3 a4 a5 a6 a7 x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      F (Z_to_bv 64 pc) fc None m1 (seg_rom usegs)).
Definition inside (m1 : mem) (jk : list byte) : Prop :=
  rw_cells usegs m1 (sp + -48) [CB 8 jk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\ bytes_at usegs m1 p bp /\ bytes_at usegs m1 q bq /\
  mem_inv usegs m1 /\ stk usegs m1 lo (sp + -48) /\ munch [(sp - 48, sp)] m m1 /\ wmono usegs m m1.

Ltac fin_post := apply evt_done; unfold sncc_post; do 3 eexists; eexists; split; [cbv delta [mkR]; reflexivity|]; repeat (split; [eassumption|]); eassumption.

Lemma sncc_tail2 : forall (i : Z) (m1 : mem) (jk : list byte) (x1 x9 x10 x11 x12 x18 x19 : word),
  inside m1 jk -> 0 <= i < n ->
  evt usegs POST (ST1 0xd126c x1 (Z_to_bv 64 (q + i)) x9 x10 x11 x12 x18 x19 m1).
Proof using LEN P0 Q0 PH QH LOSP SPH.
  intros i m1 jk x1 x9 x10 x11 x12 x18 x19 (FR & SP & SQ & MI & ST & MU & WM) Hi.
  pose proof (ro_C1_of_bytes m1 (q + i) _ (bytes_at_nth m1 q bq i SQ ltac:(rewrite LEN; lia))) as CQ.
  assert (EU2 : bv_unsigned (Z_to_bv 64 (q + i)) = q + i) by (apply unsigned_lit; lia).
  set (cq := q + i) in *.

  step. zstep. zstep. zstep. zstep. step. retlit.

  zstep. step. step. step. zstep. zstep. zstep. zstep. step. retlit.

  zstep. step. step. step. step. step. step. release_frame FR ST sp. step.
  fin_post.
Qed.

Lemma sncc_tail1 : forall (i : Z) (m1 : mem) (jk : list byte) (x1 x9 x10 x11 x12 x18 x19 : word),
  inside m1 jk -> 0 <= i < n ->
  evt usegs POST (ST1 0xd1258 x1 (Z_to_bv 64 (q + i)) x9 x10 x11 x12 x18 x19 m1).
Proof using LEN P0 Q0 PH QH LOSP SPH.
  intros i m1 jk x1 x9 x10 x11 x12 x18 x19 IN Hi. pose proof IN as (FR & SP & SQ & MI & ST & MU & WM).
  zstep. step. apply (sncc_tail2 i m1 jk); [exact IN| exact Hi].
Qed.

Lemma sncc_body : forall (i : Z) (m1 : mem) (jk : list byte) (x1 x9 x10 x11 x12 : word),
  inside m1 jk -> 0 <= i < n ->
  (forall (x1' x9' x10' x11' x12' : word), n - 1 - i <> 0 ->
     evt usegs POST (ST1 0xd1224 x1' (Z_to_bv 64 (q + (i + 1))) x9' x10' x11' x12' (Z_to_bv 64 (p + (i + 1) + 1)) (Z_to_bv 64 (n - 1 - (i + 1))) m1)) ->
  evt usegs POST (ST1 0xd1224 x1 (Z_to_bv 64 (q + i)) x9 x10 x11 x12 (Z_to_bv 64 (p + i + 1)) (Z_to_bv 64 (n - 1 - i)) m1).
Proof using LEN P0 Q0 PH QH LOSP SPH.
  intros i m1 jk x1 x9 x10 x11 x12 IN Hi CONT. pose proof IN as (FR & SP & SQ & MI & ST & MU & WM).
  pose proof (ro_C1_of_bytes m1 (q + i) _ (bytes_at_nth m1 q bq i SQ ltac:(rewrite LEN; lia))) as CQ.
  assert (EU2 : bv_unsigned (Z_to_bv 64 (q + i)) = q + i) by (apply unsigned_lit; lia).
  assert (EU3 : bv_unsigned (Z_to_bv 64 (n - 1 - i)) = n - 1 - i) by (apply unsigned_lit; lia).
  set (cq := q + i) in *.

  assert (NEXT : forall (x1' x9' x10' x11' x12' : word), n - 1 - i <> 0 ->
    evt usegs POST (ST1 0xd1210 x1' (Z_to_bv 64 cq) x9' x10' x11' x12' (Z_to_bv 64 (p + i + 1)) (Z_to_bv 64 (n - 1 - i)) m1)).
  { intros x1' x9' x10' x11' x12' NZ.
    pose proof (ro_C1_of_bytes m1 (p + (i + 1)) _ (bytes_at_nth m1 p bp (i + 1) SP ltac:(lia))) as CP1.
    replace (p + (i + 1)) with (p + i + 1) in CP1 by lia.
    assert (EU1 : bv_unsigned (Z_to_bv 64 (p + i + 1)) = p + i + 1) by (apply unsigned_lit; lia).
    set (cp1 := p + i + 1) in *.

    zstep. zstep. zstep. zstep.
    subst cq cp1.
    replace (n - 1 - i + -1) with (n - 1 - (i + 1)) by lia. replace (q + i + 1) with (q + (i + 1)) by lia. replace (p + i + 1 + 1) with (p + (i + 1) + 1) by lia.
    step. if_cases KZ.
    - apply (sncc_tail1 (i + 1) m1 jk); [exact IN| lia].
    - apply CONT. exact NZ. }

  zstep. step. if_cases KQ; [apply (sncc_tail1 i m1 jk); [exact IN| lia]|].

  zstep. step. if_cases KN; zify_cond KN; [apply (sncc_tail1 i m1 jk); [exact IN| lia]|].

  step. if_cases KE; [apply NEXT; lia|].

  zstep. step. zstep. zstep. zstep. zstep. step. retlit.
  zstep. step. step. step. zstep. zstep. zstep. zstep. step. retlit.
  step. if_cases KE2; [apply NEXT; lia|].

  pose proof (ro_C1_of_bytes m1 (p + i) _ (bytes_at_nth m1 p bp i SP ltac:(lia))) as CP.
  assert (EU1 : bv_unsigned (Z_to_bv 64 (p + i + 1)) = p + i + 1) by (apply unsigned_lit; lia).
  replace (p + i) with (p + i + 1 + -1) in CP by lia.
  set (cp1 := p + i + 1) in *.
  zstep.
  apply (sncc_tail1 i m1 jk); [exact IN| lia].
Qed.

Lemma sncc_loop : forall (k : nat) (i : Z) (m1 : mem) (jk : list byte) (x1 x9 x10 x11 x12 : word),
  inside m1 jk -> 0 <= i < n -> n - 1 - i <= Z.of_nat k ->
  evt usegs POST (ST1 0xd1224 x1 (Z_to_bv 64 (q + i)) x9 x10 x11 x12 (Z_to_bv 64 (p + i + 1)) (Z_to_bv 64 (n - 1 - i)) m1).
Proof using LEN P0 Q0 PH QH LOSP SPH.
  induction k as [|k IH]; intros i m1 jk x1 x9 x10 x11 x12 IN Hi FUEL; apply (sncc_body i m1 jk); try assumption.
  - intros. exfalso. lia.
  - intros. apply (IH (i + 1) m1 jk); [exact IN| lia| lia].
Qed.

Lemma sncc_spec_s : forall (x12 : word),
  (length bp = 0%nat \/ (p + n <= sp - 48 /\ q + n <= sp - 48)) ->
  bytes_at usegs m p bp -> bytes_at usegs m q bq -> mem_inv usegs m -> stk usegs m lo sp ->
  evt usegs POST (MS (mkR ra (Z_to_bv 64 sp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 q) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                      F (Z_to_bv 64 sncc_entry) fc None m (seg_rom usegs)).
Proof using LEN P0 Q0 PH QH LOSP SPH.
  intros x12 DISJ SP SQ MI ST.
  pose proof (munch_refl [(sp - 48, sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
  assert (EU3 : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  unfold sncc_entry.

  zstep. if_cases K; zify_cond K.
  { zstep. step. fin_post. }
  assert (DJ : p + n <= sp - 48 /\ q + n <= sp - 48) by (destruct DISJ as [D|D]; [lia| exact D]).

  hide SP. hide SQ.
  step. carve_frame 48%nat ST.
  apply (rw_cells_split_CB usegs _ _ [] 48 junk [] [8;8;8;8;8;8]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.
  step. step. step. step. step.
  unhide SP. unhide SQ.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    assert (SP1 : bytes_at usegs mx p bp) by (eapply bytes_at_transport; [exact SP| exact MU|]; cbn [disjoint_from]; lia);
    assert (SQ1 : bytes_at usegs mx q bq) by (eapply bytes_at_transport; [exact SQ| exact MU|]; cbn [disjoint_from]; rewrite LEN; lia);
    clear SP SQ;
    assert (IN : inside mx (take 8 junk)) by (split; [exact FR|]; repeat (split; [assumption|]); assumption) end.

  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    pose proof (ro_C1_of_bytes mx (p + 0) _ (bytes_at_nth mx p bp 0 SP1 ltac:(lia))) as CP end.
  rewrite Z.add_0_r in CP.
  assert (EU1 : bv_unsigned (Z_to_bv 64 p) = p) by (apply unsigned_lit; lia).
  step. zstep. step. if_cases KZ.
  { zstep. lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      pose proof (sncc_tail2 0 mx (take 8 junk)) as T; rewrite Z.add_0_r in T; apply T; [exact IN| lia] end. }

  zstep. zstep. step.
  replace (n + -1) with (n - 1 - 0) by lia. replace (p + 1) with (p + 0 + 1) by lia.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    pose proof (sncc_loop (Z.to_nat (n - 1)) 0 mx (take 8 junk)) as T; rewrite (Z.add_0_r q) in T; apply T; [exact IN| lia| lia] end.
Qed.
End Proofs.
End WithCeiling0.
