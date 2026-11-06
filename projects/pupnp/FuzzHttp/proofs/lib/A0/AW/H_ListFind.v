(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From stdpp Require Import base list.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Ceiling Arr.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.P0 Require H_httpmsg_compare.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts ATac IcptA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7A0 Require Import ShadowKit.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.AW Require Import HttpRepA AWKit AWAuto.
Import ListNotations.
Open Scope Z_scope.

Definition ListFind_entryA : Z := 0x8b998.

Section W.
Context {HC : HasCeiling}.

#[using="Type"] Lemma httpmsg_compare_shw : forall (q : Z) (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (A B ia ib lo : Z) (ja : list byte) (n1 n2 pad : word),
  rw_cells asegs m A [CB 16%nat ja; C4 (wz ia)] -> rw_cells asegs m B [C8 n1; C8 n2; C4 (wz ib); C4 pad] ->
  - 2^31 <= ia < 2^31 -> - 2^31 <= ib < 2^31 ->
  asan_env asegs m -> shw m A 24 -> shw m B 24 ->
  0x609000 <= A -> A + 24 <= alloc_ceiling -> A mod 8 = 0 ->
  0x609000 <= B -> B + 24 <= alloc_ceiling -> B mod 8 = 0 ->
  stk asegs m lo q -> alloc_ceiling <= lo -> q < 2^64 -> lo <= q - 16 ->
  mem_inv asegs m -> a0 = wz A -> a1 = wz B ->
  evt asegs (httpmsg_compare_post_A ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ia ib lo m)
      (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz httpmsg_compare_entryA) fc None m (seg_rom asegs)).
Proof.
  intros q ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m A B ia ib lo ja n1 n2 pad.
  intros CA CB2 RA RB AE0 SHA SHB ALO AHI ALA BLO BHI ALB ST CLO QHI LO MI -> ->.
  unfold httpmsg_compare_entryA.
  a0_prologue AE0 [(lo, q)]%Z m.
  carve_frame 16%nat ST.
  walk_lia_to 0x86964%Z.
  step.
  replace (v_sltiu (Z_to_bv 64 (Z.lxor (ia mod 18446744073709551616) (ib mod 18446744073709551616))) 1)
    with (P0.H_httpmsg_compare.cmp32_expr ia ib).
  2:{ unfold P0.H_httpmsg_compare.cmp32_expr. rewrite !sx32_lit by lia. rewrite !unsigned_lit_wrap. reflexivity. }
  rewrite P0.H_httpmsg_compare.cmp32_eval by assumption.
  env_now AE0 MU WM.
  step. release_to q. step. step.
  finish.
Qed.

Fixpoint lsegA (m : mem) (ns : list (Z * Z * Z)) (first pv TAIL : Z) {struct ns} : Prop :=
  match ns with
  | [] => first = TAIL
  | (N, it, id) :: ns' =>
      first = N /\ N <> TAIL /\ N <> 0 /\ it <> 0 /\ - 2^31 <= id < 2^31 /\
      exists nx (n1 n2 pad : word),
        rw_cells asegs m N (node_cells pv nx it) /\
        rw_cells asegs m it [C8 n1; C8 n2; C4 (wz id); C4 pad] /\
        lsegA m ns' nx N TAIL
  end.

#[using="Type"] Lemma lsegA_transport : forall ns m m' W first pv TAIL,
  lsegA m ns first pv TAIL -> munch W m m' -> wmono asegs m m' ->
  (forall N it id, In (N, it, id) ns -> disjoint_from W N 24 /\ disjoint_from W it 24) ->
  lsegA m' ns first pv TAIL.
Proof.
  induction ns as [|[[N it] id] ns IH]; intros m m' W first pv TAIL LS MU WM SEP; cbn [lsegA] in *; [exact LS|].
  destruct LS as (E & NT & NNZ & ITNZ & IDR & nx & n1 & n2 & pad & NC & ICc & LS').
  destruct (SEP N it id (or_introl eq_refl)) as [D1 D2].
  split; [exact E|]. split; [exact NT|]. split; [exact NNZ|]. split; [exact ITNZ|]. split; [exact IDR|].
  exists nx, n1, n2, pad. split; [|split].
  - eapply rw_cells_transport; [exact NC| exact MU| exact WM| exact D1].
  - eapply rw_cells_transport; [exact ICc| exact MU| exact WM| exact D2].
  - eapply IH; [exact LS'| exact MU| exact WM|]. intros N0 it0 id0 Hin. apply (SEP N0 it0 id0). right. exact Hin.
Qed.

Definition objA (m : mem) (X n : Z) : Prop := 0x609000 <= X /\ X + n <= alloc_ceiling /\ X mod 8 = 0 /\ shw m X n.

Definition ListFind_post_A (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (ns : list (Z * Z * Z)) (qid lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (r : Z),
    ms' = MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(lo, q)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo q /\ asan_env asegs m'
    /\ (r = 0 \/ exists it, In (r, it, qid) ns).

Definition ListFind_stmt_A : Prop :=
  forall (L IT qid last size flh fk ffree lo : Z) (ns : list (Z * Z * Z)) (ja : list byte)
         (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (first : Z),
  rw_cells asegs m L (llist_cells first last size flh fk ffree httpmsg_compare_entryA) ->
  lsegA m ns first L (L + 24) ->
  rw_cells asegs m IT [CB 16%nat ja; C4 (wz qid)] -> - 2^31 <= qid < 2^31 ->
  objA m L 96 -> objA m IT 24 ->
  (forall N it id, In (N, it, id) ns -> objA m N 24 /\ objA m it 24) ->
  asan_env asegs m -> stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - 64 - 16 -> q < 2^64 ->
  mem_inv asegs m -> a0 = wz L -> a1 = wz 0 -> a2 = wz IT ->
  evt asegs (ListFind_post_A ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ns qid lo m)
      (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz ListFind_entryA) fc None m (seg_rom asegs)).

Section WALK.
  Variables (L IT qid last size flh fk ffree lo : Z) (ns0 : list (Z * Z * Z)) (ja : list byte).
  Variables (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem).
  Hypothesis QID : - 2^31 <= qid < 2^31.
  Hypothesis OL : objA m0 L 96.
  Hypothesis OI : objA m0 IT 24.
  Hypothesis ON : forall N it id, In (N, it, id) ns0 -> objA m0 N 24 /\ objA m0 it 24.
  Hypothesis CLO : alloc_ceiling <= lo.
  Hypothesis LO : lo <= q - 64 - 16.
  Hypothesis QHI : q < 2^64.
  Hypothesis AE0 : asan_env asegs m0.

  Notation POST := (ListFind_post_A ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ns0 qid lo m0).

  Notation LSTF pc x1 x5 x6 x7 N x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 mm :=
    (MS (mkR x1 (wz (q + -64)) gp tp x5 x6 x7 (wz IT) (wz N) x10 x11 x12 x13 x14 x15 x16 x17
             (wz (L + 88)) (wz 0x7fff8000) (wz (L + 24)) (wz (Z.shiftr (L + 88) 3 + 2147450880)) s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (wz pc) fc None mm (seg_rom asegs)).

  Definition linvA (m : mem) (first : Z) : Prop :=
    (exists j8, rw_cells asegs m (q + -64) [CB 8 j8; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
    /\ stk asegs m lo (q + -64)
    /\ rw_cells asegs m L (llist_cells first last size flh fk ffree httpmsg_compare_entryA)
    /\ rw_cells asegs m IT [CB 16%nat ja; C4 (wz qid)]
    /\ mem_inv asegs m /\ munch [(lo, q)] m0 m /\ wmono asegs m0 m.

  #[using="HC CLO LO AE0"] Lemma exit_okA : forall (r first : Z) (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31 : word) m,
    linvA m first -> (r = 0 \/ exists it, In (r, it, qid) ns0) ->
    evt asegs POST
      (MS (mkR x1 (wz (q + -64)) gp tp x5 x6 x7 x8 (wz r) x10 x11 x12 x13 x14 x15 x16 x17
               x18 x19 x20 x21 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (wz 0x8bac4) fc None m (seg_rom asegs)).
  Proof.
    intros r first x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31 m.
    intros ([j8 FR] & ST & LC & ITC & MI & MU & WM) HR.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    walk_lia_to 0x8bae4%Z. release_to q. step. step.
    env_now AE0 MU WM.
    finish.
  Qed.

  #[using="HC QID OL OI ON CLO LO QHI AE0"] Lemma loopA : forall (rest : list (Z * Z * Z)) (N it id pv first : Z) (x1 x5 x6 x7 x11 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) m,
    lsegA m0 ((N, it, id) :: rest) N pv (L + 24) ->
    (forall x, In x ((N, it, id) :: rest) -> In x ns0) ->
    linvA m first ->
    evt asegs POST (LSTF 0x8ba28 x1 x5 x6 x7 N (wz (N + 16)) x11 (wz httpmsg_compare_entryA) x13 x14 x15 x16 x17 x28 x29 x30 x31 m).
  Proof.
    induction rest as [|[[N' it'] id'] rest IH]; intros N it id pv first x1 x5 x6 x7 x11 x13 x14 x15 x16 x17 x28 x29 x30 x31 m;
      intros LS SUB ([j8 FR] & ST & LC & ITC & MI & MU & WM).
    all: pose proof (lsegA_transport _ m0 m _ _ _ _ LS MU WM
           ltac:(intros N0 it0 id0 Hin; destruct (ON N0 it0 id0 (SUB _ Hin)) as [(? & ? & _) (? & ? & _)]; cbn [disjoint_from]; lia)) as LSm.
    - destruct LSm as (_ & NT & NNZ & ITNZ' & IDR & nx & n1 & n2 & pad & NC & ICc & LSm'). cbn [lsegA] in LSm'. subst nx.
      destruct (ON N it id (SUB _ (or_introl eq_refl))) as [(NLO & NHI & NAL & SHWN) (ILO & IHI & IAL & SHWI)].
      destruct OL as (LLO & LHI & LAL & SHWL). destruct OI as (TLO & THI & TAL & SHWT).
      pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
      unfold node_cells in NC. unfold llist_cells in LC. unfold httpmsg_compare_entryA.
      walk_lia_to 0x8ba34%Z. step.
      pose proof (shw_frame _ m0 m IT 24 SHWT MU ltac:(app_ivs_tac)) as SHWTn.
      pose proof (shw_frame _ m0 m it 24 SHWI MU ltac:(app_ivs_tac)) as SHWIn.
      pose proof (asan_env_frame asegs m0 m _ AE0 MU WM ltac:(env_safe_tac)) as AEn.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        eapply evt_cut;
        [ eapply (httpmsg_compare_shw (q + -64)) with (A := IT) (B := it) (ia := qid) (ib := id) (lo := lo);
          first [ exact ITC | exact ICc | exact AEn | exact SHWTn | exact SHWIn | exact ST | exact MI | reflexivity | lia ]
        | post_call asegs mm ] end.
      clear SHWTn SHWIn AEn.
      destruct (Z.eqb_spec qid id) as [EQ|NE].
      +
        walk_lia_to 0x8bac4%Z.
        subst id. apply (exit_okA N first). { unfold linvA, llist_cells. split; [eexists; exact FR|]. repeat (split; [assumption|]); assumption. }
        right. exists it. apply SUB. left. reflexivity.
      + walk_lia_to 0x8bac4%Z.
        apply (exit_okA 0 first). { unfold linvA, llist_cells. split; [eexists; exact FR|]. repeat (split; [assumption|]); assumption. }
        left. reflexivity.
    - destruct LS as (_ & _ & _ & _ & _ & nx0 & _ & _ & _ & _ & _ & LS').
      assert (nx0 = N') by (destruct LS' as [E _]; exact E). subst nx0.
      destruct LSm as (_ & NT & NNZ & ITNZ' & IDR & nx & n1 & n2 & pad & NC & ICc & LSm').
      assert (nx = N') by (destruct LSm' as [E _]; exact E). subst nx.
      destruct LSm' as (_ & NT' & NNZ' & ITNZ2 & IDR' & nx' & n1' & n2' & pad' & NC' & ICc' & _).
      destruct (ON N it id (SUB _ (or_introl eq_refl))) as [(NLO & NHI & NAL & SHWN) (ILO & IHI & IAL & SHWI)].
      destruct (ON N' it' id' (SUB _ (or_intror (or_introl eq_refl)))) as [(NLO' & NHI' & NAL' & SHWN') _].
      destruct OL as (LLO & LHI & LAL & SHWL). destruct OI as (TLO & THI & TAL & SHWT).
      pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
      unfold node_cells in NC, NC'. unfold llist_cells in LC. unfold httpmsg_compare_entryA.
      walk_lia_to 0x8ba34%Z. step.
      pose proof (shw_frame _ m0 m IT 24 SHWT MU ltac:(app_ivs_tac)) as SHWTn.
      pose proof (shw_frame _ m0 m it 24 SHWI MU ltac:(app_ivs_tac)) as SHWIn.
      pose proof (asan_env_frame asegs m0 m _ AE0 MU WM ltac:(env_safe_tac)) as AEn.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        eapply evt_cut;
        [ eapply (httpmsg_compare_shw (q + -64)) with (A := IT) (B := it) (ia := qid) (ib := id) (lo := lo);
          first [ exact ITC | exact ICc | exact AEn | exact SHWTn | exact SHWIn | exact ST | exact MI | reflexivity | lia ]
        | post_call asegs mm ] end.
      clear SHWTn SHWIn AEn.
      destruct (Z.eqb_spec qid id) as [EQ|NE].
      + walk_lia_to 0x8bac4%Z.
        subst id. apply (exit_okA N first). { unfold linvA, llist_cells. split; [eexists; exact FR|]. repeat (split; [assumption|]); assumption. }
        right. exists it. apply SUB. left. reflexivity.
      + walk_lia_to 0x8ba28%Z.
        apply (IH N' it' id' N first); [exact LS'| intros y Hy; apply SUB; right; exact Hy|].
        unfold linvA, llist_cells. split; [eexists; exact FR|]. repeat (split; [assumption|]); assumption.
  Qed.

  #[using="HC QID OL OI ON CLO LO QHI AE0"] Lemma bodyA : forall (ns : list (Z * Z * Z)) (first : Z) (x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    lsegA m0 ns first L (L + 24) -> (forall x, In x ns -> In x ns0) ->
    rw_cells asegs m0 L (llist_cells first last size flh fk ffree httpmsg_compare_entryA) ->
    rw_cells asegs m0 IT [CB 16%nat ja; C4 (wz qid)] ->
    stk asegs m0 lo q -> mem_inv asegs m0 ->
    evt asegs POST
      (MS (mkR ra (wz q) gp tp x5 x6 x7 s0 s1 (wz L) (wz 0) (wz IT) x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (wz ListFind_entryA) fc None m0 (seg_rom asegs)).
  Proof.
    intros ns first x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31. intros LS SUB LC ITC ST MI. unfold ListFind_entryA.
    destruct OL as (LLO & LHI & LAL & SHWL). destruct OI as (TLO & THI & TAL & SHWT).
    a0_prologue AE0 [(lo, q)]%Z m0.
    unfold llist_cells in LC.
    carve_frame 64%nat ST.
    destruct ns as [|[[N it] id] rest].
    -
      cbn [lsegA] in LS. subst first.
      walk_lia_to 0x8bac4%Z.
      apply (exit_okA 0 (L + 24)).
      { unfold linvA, llist_cells. split; [eexists; exact FR|]. repeat (split; [assumption|]); assumption. } left; reflexivity.
    - pose proof LS as LS0. destruct LS as (-> & NT & NNZ & ITNZ' & IDR & nx & n1 & n2 & pad & NC & ICc & LS').
      destruct (ON N it id (SUB _ (or_introl eq_refl))) as [(NLO & NHI & NAL & SHWN) (ILO & IHI & IAL & SHWI)].
      unfold httpmsg_compare_entryA.
      walk_lia_to 0x8ba28%Z.
      apply (loopA rest N it id L N); [exact LS0| exact SUB|].
      unfold linvA, llist_cells. split; [eexists; exact FR|]. repeat (split; [assumption|]); assumption.
  Qed.
End WALK.

#[using="Type"] Lemma ListFind_spec_A : ListFind_stmt_A.
Proof.
  unfold ListFind_stmt_A. intros L IT qid last size flh fk ffree lo ns ja ra q gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m first.
  intros LC LS ITC QID OL OI ON AE ST CLO LO QHI MI -> -> ->.
  eapply (bodyA L IT qid last size flh fk ffree lo ns ja); eauto.
Qed.

End W.
