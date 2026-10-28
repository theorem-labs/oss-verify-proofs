(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs H_httpmsg_compare HU_list_kit.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Ceiling.
Import ListNotations.
Open Scope Z_scope.
Open Scope bv_scope.

Definition ListFind_entry := 0x162e0%Z.
Ltac sstep := step; fix_lit_store.

Fixpoint lseg (m : mem) (ns : list (Z * Z * Z)) (first pv TAIL : Z) {struct ns} : Prop :=
  match ns with
  | [] => first = TAIL
  | (N, it, id) :: ns' =>
      first = N /\ N <> TAIL /\ N <> 0%Z /\ it <> 0%Z /\ (- 2^31 <= id < 2^31)%Z /\
      exists nx (n1 n2 pad : word),
        rw_cells rsegs m N (node_cells pv nx it) /\
        rw_cells rsegs m it [C8 n1; C8 n2; C4 (wz id); C4 pad] /\
        lseg m ns' nx N TAIL
  end.

Lemma lseg_transport : forall ns m m' W first pv TAIL,
  lseg m ns first pv TAIL -> munch W m m' -> wmono rsegs m m' ->
  (forall N it id, In (N, it, id) ns -> disjoint_from W N 24 /\ disjoint_from W it 24) ->
  lseg m' ns first pv TAIL.
Proof.
  induction ns as [|[[N it] id] ns IH]; intros m m' W first pv TAIL LS MU WM SEP; cbn [lseg] in *; [exact LS|].
  destruct LS as (E & NT & NNZ & ITNZ & IDR & nx & n1 & n2 & pad & NC & IC & LS').
  destruct (SEP N it id (or_introl eq_refl)) as [D1 D2].
  split; [exact E|]. split; [exact NT|]. split; [exact NNZ|]. split; [exact ITNZ|]. split; [exact IDR|].
  exists nx, n1, n2, pad. split; [|split].
  - eapply rw_cells_transport; [exact NC| exact MU| exact WM| exact D1].
  - eapply rw_cells_transport; [exact IC| exact MU| exact WM| exact D2].
  - eapply IH; [exact LS'| exact MU| exact WM|]. intros N0 it0 id0 Hin. apply (SEP N0 it0 id0). right. exact Hin.
Qed.

Definition ListFind_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (ns : list (Z * Z * Z)) (qid : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (r : Z),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' (bv_unsigned sp - 48) (bv_unsigned sp)
    /\ (r = 0 \/ exists it, In (r, it, qid) ns)%Z.

Definition ListFind_stmt : Prop :=
  forall (L IT qid last size flh fk ffree : Z) (ns : list (Z * Z * Z)) (ja : list byte)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (first : Z),
  rw_cells rsegs m L (llist_cells first last size flh fk ffree httpmsg_compare_entry) ->
  lseg m ns first L (L + 24) ->
  rw_cells rsegs m IT [CB 16%nat ja; C4 (wz qid)] -> (- 2^31 <= qid < 2^31)%Z ->
  L <> 0%Z -> (L + 96 < 2^64)%Z -> IT <> 0%Z ->
  stk rsegs m (bv_unsigned sp - 48) (bv_unsigned sp) -> (128 <= bv_unsigned sp)%Z ->
  (L + 96 <= bv_unsigned sp - 48 \/ bv_unsigned sp <= L)%Z ->
  (IT + 20 <= bv_unsigned sp - 48 \/ bv_unsigned sp <= IT)%Z ->
  (forall N it id, In (N, it, id) ns -> (N + 24 <= bv_unsigned sp - 48 \/ bv_unsigned sp <= N) /\ (it + 24 <= bv_unsigned sp - 48 \/ bv_unsigned sp <= it))%Z ->
  (L mod 8 = 0)%Z -> (IT mod 8 = 0)%Z -> (forall N it id, In (N, it, id) ns -> N mod 8 = 0 /\ it mod 8 = 0)%Z ->
  mem_inv rsegs m -> a0 = wz L -> a1 = wz 0 -> a2 = wz IT ->
  evt rsegs (ListFind_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ns qid m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz ListFind_entry) fc None m (seg_rom rsegs)).

Section WALK.
Context {HCEIL : HasCeiling}.
  Variables (L IT qid last size flh fk ffree : Z) (ns0 : list (Z * Z * Z)) (ja : list byte).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem).
  Hypothesis SPR : (128 <= bv_unsigned sp /\ bv_unsigned sp < 2^64)%Z.
  Hypothesis QID : (- 2^31 <= qid < 2^31)%Z.
  Hypothesis LNZ : L <> 0%Z.
  Hypothesis LHI : (L + 96 < 2^64)%Z.
  Hypothesis ITNZ : IT <> 0%Z.
  Hypothesis SEPL : (L + 96 <= bv_unsigned sp - 48 \/ bv_unsigned sp <= L)%Z.
  Hypothesis SEPI : (IT + 20 <= bv_unsigned sp - 48 \/ bv_unsigned sp <= IT)%Z.
  Hypothesis SEPN : (forall N it id, In (N, it, id) ns0 ->
     (N + 24 <= bv_unsigned sp - 48 \/ bv_unsigned sp <= N) /\ (it + 24 <= bv_unsigned sp - 48 \/ bv_unsigned sp <= it))%Z.
  Hypothesis ALL : (L mod 8 = 0)%Z.
  Hypothesis ALI : (IT mod 8 = 0)%Z.
  Hypothesis ALN : (forall N it id, In (N, it, id) ns0 -> N mod 8 = 0 /\ it mod 8 = 0)%Z.

  Notation spw := (Z_to_bv 64 (bv_unsigned sp + -48)).
  Notation POST := (ListFind_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ns0 qid m0).

  Notation LST pc x1 x5 x6 x7 N x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 mm :=
    (MS (mkR x1 spw gp tp x5 x6 x7 (Z_to_bv 64 IT) (Z_to_bv 64 L) x10 x11 x12
             x13 x14 x15 x16 x17 (Z_to_bv 64 N) (Z_to_bv 64 (L + 24)) s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom rsegs)).

  Definition linv (m : mem) (first : Z) : Prop :=
    (exists j8, rw_cells rsegs m (bv_unsigned sp + -48) [CB 8 j8; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
    /\ stk rsegs m (bv_unsigned sp + -48) (bv_unsigned sp + -48)
    /\ rw_cells rsegs m L (llist_cells first last size flh fk ffree httpmsg_compare_entry)
    /\ rw_cells rsegs m IT [CB 16%nat ja; C4 (wz qid)]
    /\ mem_inv rsegs m /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m0 m /\ wmono rsegs m0 m.

  #[using="Type"] Lemma exit_ok : forall (r first : Z) (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31 : word) m,
    linv m first -> (r = 0 \/ exists it, In (r, it, qid) ns0)%Z ->
    evt rsegs POST
      (MS (mkR x1 spw gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 r) x19 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x16330) fc None m (seg_rom rsegs)).
  Proof.
    intros until m. intros ([j8 FR] & ST & LC & ITC & MI & MU & WM) HR.
    step. step. step. step. step. step. step. step.
    release_frame FR ST (bv_unsigned sp). finish.
  Qed.

  #[using="SPR QID LNZ LHI ITNZ SEPL SEPN ALL ALI ALN"] Lemma loop : forall (rest : list (Z * Z * Z)) (N it id pv first : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) m,
    lseg m ((N, it, id) :: rest) N pv (L + 24) ->
    (forall x, In x ((N, it, id) :: rest) -> In x ns0) ->
    linv m first ->
    evt rsegs POST (LST 0x16358 x1 x5 x6 x7 N x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m).
  Proof.
    induction rest as [|[[N' it'] id'] rest IH]; intros until m; intros LS SUB ([j8 FR] & ST & LC & ITC & MI & MU & WM).
    - destruct LS as (_ & NT & NNZ & ITNZ' & IDR & nx & n1 & n2 & pad & NC & IC & LS'). cbn [lseg] in LS'. subst nx.
      pose proof (SEPN N it id (SUB _ (or_introl eq_refl))) as [SN SI].
      destruct (ALN N it id (SUB _ (or_introl eq_refl))) as [NAL IAL].
      pose proof (rw_cells_bound rsegs _ _ _ NC) as NB. cbn [cells_size csize Nat.add node_cells] in NB. unfold node_cells in NC.
      pose proof (rw_cells_bound rsegs _ _ _ IC) as IB. cbn [cells_size csize Nat.add] in IB.
      pose proof (rw_cells_bound rsegs _ _ _ ITC) as ITB. cbn [cells_size csize Nat.add] in ITB.
      pose proof (rw_cells_bound rsegs _ _ _ LC) as LB. cbn [cells_size csize Nat.add llist_cells] in LB.
      unfold llist_cells in LC. unfold httpmsg_compare_entry in LC |- *.
      uwalk_ub_to 0x1637c%Z. step.
      call (httpmsg_compare_spec).
      all: side (first [exact ITC | exact IC | exact MI | reflexivity | lia]).
      destruct (Z.eqb_spec qid id) as [EQ|NE].
      + step. if_cases K; zify_cond K. { exfalso. cbn in K. lia. }
        uwalk_lia_to 0x16330%Z. subst id. apply (exit_ok N first). { split; [eexists; exact FR|]. repeat (split; [assumption|]); assumption. }
        right. exists it. apply SUB. left. reflexivity.
      + step. if_cases K; zify_cond K. 2:{ exfalso. cbn in K. lia. }
        uwalk_lia_to 0x16330%Z. apply (exit_ok 0 first). { split; [eexists; exact FR|]. repeat (split; [assumption|]); assumption. } left. reflexivity.
    - destruct LS as (_ & NT & NNZ & ITNZ' & IDR & nx & n1 & n2 & pad & NC & IC & LS').
      assert (nx = N') by (destruct LS' as [E _]; exact E). subst nx.
      pose proof LS' as LS2. destruct LS2 as (_ & NT' & NNZ' & ITNZ2 & IDR' & nx' & n1' & n2' & pad' & NC' & IC' & _).
      pose proof (SEPN N it id (SUB _ (or_introl eq_refl))) as [SN SI].
      pose proof (SEPN N' it' id' (SUB _ (or_intror (or_introl eq_refl)))) as [SN' SI'].
      destruct (ALN N it id (SUB _ (or_introl eq_refl))) as [NAL IAL].
      destruct (ALN N' it' id' (SUB _ (or_intror (or_introl eq_refl)))) as [NAL' IAL'].
      pose proof (rw_cells_bound rsegs _ _ _ NC) as NB. cbn [cells_size csize Nat.add node_cells] in NB. unfold node_cells in NC.
      pose proof (rw_cells_bound rsegs _ _ _ NC') as NB'. cbn [cells_size csize Nat.add node_cells] in NB'. unfold node_cells in NC'.
      pose proof (rw_cells_bound rsegs _ _ _ IC) as IB. cbn [cells_size csize Nat.add] in IB.
      pose proof (rw_cells_bound rsegs _ _ _ ITC) as ITB. cbn [cells_size csize Nat.add] in ITB.
      pose proof (rw_cells_bound rsegs _ _ _ LC) as LB. cbn [cells_size csize Nat.add llist_cells] in LB.
      unfold llist_cells in LC. unfold httpmsg_compare_entry in LC |- *.
      uwalk_ub_to 0x1637c%Z. step.
      call (httpmsg_compare_spec).
      all: side (first [exact ITC | exact IC | exact MI | reflexivity | lia]).
      destruct (Z.eqb_spec qid id) as [EQ|NE].
      + step. if_cases K; zify_cond K. { exfalso. cbn in K. lia. }
        uwalk_lia_to 0x16330%Z. subst id. apply (exit_ok N first). { split; [eexists; exact FR|]. repeat (split; [assumption|]); assumption. }
        right. exists it. apply SUB. left. reflexivity.
      + step. if_cases K; zify_cond K. 2:{ exfalso. cbn in K. lia. }
        uwalk_lia_to 0x16358%Z.
        apply (IH N' it' id' N first); [exact LS'| intros y Hy; apply SUB; right; exact Hy|].
        split; [eexists; exact FR|]. repeat (split; [assumption|]); assumption.
  Qed.

  #[using="SPR QID LNZ LHI ITNZ SEPL SEPI SEPN ALL ALI ALN"] Lemma body : forall (ns : list (Z * Z * Z)) (first : Z) (x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    lseg m0 ns first L (L + 24) -> (forall x, In x ns -> In x ns0) ->
    rw_cells rsegs m0 L (llist_cells first last size flh fk ffree httpmsg_compare_entry) ->
    rw_cells rsegs m0 IT [CB 16%nat ja; C4 (wz qid)] ->
    stk rsegs m0 (bv_unsigned sp - 48) (bv_unsigned sp) -> mem_inv rsegs m0 ->
    evt rsegs POST
      (MS (mkR ra sp gp tp x5 x6 x7 s0 s1 (Z_to_bv 64 L) (Z_to_bv 64 0) (Z_to_bv 64 IT) x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 ListFind_entry) fc None m0 (seg_rom rsegs)).
  Proof.
    intros until x31. intros LS SUB LC ITC ST MI. unfold ListFind_entry.
    pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m0) as MU. pose proof (wmono_refl rsegs m0) as WM.
    pose proof (rw_cells_bound rsegs _ _ _ ITC) as ITB. cbn [cells_size csize Nat.add] in ITB.
    pose proof (rw_cells_bound rsegs _ _ _ LC) as LB. cbn [cells_size csize Nat.add llist_cells] in LB.
    unfold llist_cells in LC.
    carve_frame 48%nat ST.
    unfold httpmsg_compare_entry in LC |- *.
    uwalk_ub_to 0x16310%Z.
    step. ubr. ub_align. step. ubr.
    destruct ns as [|[[N it] id] rest].
    - cbn [lseg] in LS. subst first.
      uwalk_ub_to 0x16330%Z.
      apply (exit_ok 0 (L + 24)).
      { unfold linv, llist_cells. split; [eexists; exact FR|]. repeat (split; [assumption|]); assumption. } left; reflexivity.
    - assert (LS1 : lseg m ((N, it, id) :: rest) first L (L + 24)).
      { eapply lseg_transport; [exact LS| exact MU| exact WM|].
        intros N0 it0 id0 Hin. destruct (SEPN N0 it0 id0 (SUB _ Hin)) as [A1 A2]. cbn [disjoint_from]. lia. }
      clear LS. rename LS1 into LS. pose proof LS as LS0. destruct LS as (-> & NT & NNZ & ITNZ' & IDR & nx & n1 & n2 & pad & NC & IC & LS').
      pose proof (rw_cells_bound rsegs _ _ _ NC) as NB. cbn [cells_size csize Nat.add node_cells] in NB. unfold node_cells in NC.
      uwalk_ub_to 0x16358%Z.
      apply (loop rest N it id L N); [exact LS0| exact SUB|].
      unfold linv, llist_cells. split; [eexists; exact FR|]. repeat (split; [assumption|]); assumption.
  Qed.
End WALK.

Lemma ListFind_spec : ListFind_stmt.
Proof.
  unfold ListFind_stmt. intros until first. intros LC LS ITC QID LNZ LHI ITNZ ST SPLO SEPL SEPI SEPN AL AI AN MI -> -> ->.
  eapply (body L IT qid last size flh fk ffree ns); eauto. pose proof (word_lt64 sp). lia.
Qed.
