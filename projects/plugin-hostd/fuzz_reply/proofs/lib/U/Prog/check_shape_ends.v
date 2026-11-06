(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_msgpack_encoder/lib/CJ/Ref/Mh_0118.v, with its module paths, module names and addresses changed; 1147 of its 1229 lines of code are new or changed and 2359 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Prog/drain_b_seg.v, with its module paths, module names and addresses changed; 1800 of its 1911 lines of code are new or changed and 1118 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes Arr ZBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import has_prefix_c next_line_c list_find_c RelayModel HarnessRep CheckRep check_shape_ends_a check_shape_ends_b.
Import ListNotations.
Open Scope Z_scope.

Definition ce_keep (P : Prop) : Prop := P.
Ltac ce_hide H := let T := type of H in change (ce_keep T) in H.
Ltac ce_dj := cbn [disjoint_from]; repeat (apply conj; [lia|]); exact I.

Lemma ce_cut : forall m A cs1 cs2, rw_cells rsegs m A (cs1 ++ cs2) ->
  rw_cells rsegs m A cs1 /\ rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2 [[W B] (H0 & H1 & H)].
  apply cells_wf_app in W. destruct W as [W1 W2].
  rewrite cells_bytes_app in B. apply bytes_at_app in B. destruct B as [B1 B2].
  rewrite (cells_bytes_length cs1 W1) in B2. rewrite cells_size_app in H1, H.
  split; split; try (split; assumption).
  - split; [lia|]. split; [lia|]. intros i Hi. apply H. lia.
  - split; [lia|]. split; [lia|]. intros i Hi.
    replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by lia. apply H. lia.
Qed.

Lemma ce_join : forall m A B cs1 cs2, rw_cells rsegs m A cs1 -> rw_cells rsegs m B cs2 ->
  B = A + Z.of_nat (cells_size cs1) -> rw_cells rsegs m A (cs1 ++ cs2).
Proof.
  intros m A B cs1 cs2 [[W1 B1] (H0 & H1 & H)] [[W2 B2] (G0 & G1 & G)] ->.
  split; split.
  - apply cells_wf_app. split; assumption.
  - rewrite cells_bytes_app. apply bytes_at_app. split; [exact B1|]. rewrite (cells_bytes_length cs1 W1). exact B2.
  - lia.
  - rewrite cells_size_app. split; [lia|]. intros i Hi.
    destruct (Z.lt_ge_cases i (Z.of_nat (cells_size cs1))) as [Hlt|Hge]; [apply H; lia|].
    replace (A + i) with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1))) by lia. apply G. lia.
Qed.

Lemma ce_frame16 : forall m A j, rw_cells rsegs m A [CB 16 j] ->
  exists jn jl, rw_cells rsegs m A [CB 8 jn] /\ rw_cells rsegs m (A + 8) [CB 8 jl].
Proof.
  intros m A j H. pose proof (rw_cells_split_CB rsegs m A [] 16 j [] [8%nat; 8%nat] H eq_refl) as H2.
  cbn [app mk_CB_cells] in H2.
  destruct (ce_cut m A [CB 8 (firstn 8 j)] [CB 8 (firstn 8 (skipn 8 j))] H2) as [H3 H4].
  exists (firstn 8 j), (firstn 8 (skipn 8 j)). split; [exact H3 | exact H4].
Qed.

Lemma ce_frame16j : forall m A x y, rw_cells rsegs m A [C8 x] -> rw_cells rsegs m (A + 8) [C8 y] ->
  exists j, rw_cells rsegs m A [CB 16 j].
Proof.
  intros m A x y H1 H2. pose proof (ce_join m A (A + 8) [C8 x] [C8 y] H1 H2 eq_refl) as H.
  destruct (rw_cells_forget rsegs m A _ H) as [junk HJ]. exists junk. exact HJ.
Qed.

Lemma ce_frame24 : forall m A j, rw_cells rsegs m A [CB 24 j] ->
  exists j0 j1, rw_cells rsegs m A [CB 8 j0] /\ rw_cells rsegs m (A + 8) [CB 16 j1].
Proof.
  intros m A j H. pose proof (rw_cells_split_CB rsegs m A [] 24 j [] [8%nat; 16%nat] H eq_refl) as H2.
  cbn [app mk_CB_cells] in H2.
  destruct (ce_cut m A [CB 8 (firstn 8 j)] [CB 16 (firstn 16 (skipn 8 j))] H2) as [H3 H4].
  exists (firstn 8 j), (firstn 16 (skipn 8 j)). split; [exact H3 | exact H4].
Qed.

Lemma ce_frame24j : forall m A j0 j1, rw_cells rsegs m A [CB 8 j0] -> rw_cells rsegs m (A + 8) [CB 16 j1] ->
  exists j, rw_cells rsegs m A [CB 24 j].
Proof.
  intros m A j0 j1 H1 H2. pose proof (ce_join m A (A + 8) [CB 8 j0] [CB 16 j1] H1 H2 eq_refl) as H.
  destruct (rw_cells_forget rsegs m A _ H) as [junk HJ]. exists junk. exact HJ.
Qed.

Lemma ce_split_nul : forall ln rest, ~ In (Z_to_bv 8 0) ln -> split_nul (ln ++ Z_to_bv 8 0 :: rest) = Some (ln, rest).
Proof.
  induction ln as [|b ln IH]; intros rest NZ; cbn [app split_nul].
  - reflexivity.
  - destruct (Z.eqb_spec (bv_unsigned b) 0) as [E|E].
    + exfalso. apply NZ. left. apply bv_eq. rewrite E. reflexivity.
    + rewrite IH by (intros X; apply NZ; right; exact X). reflexivity.
Qed.

Lemma ce_split_inv : forall d l d', split_nul d = Some (l, d') -> d = l ++ Z_to_bv 8 0 :: d' /\ ~ In (Z_to_bv 8 0) l.
Proof.
  induction d as [|b d IH]; intros l d' H; cbn [split_nul] in H; [discriminate|].
  destruct (Z.eqb_spec (bv_unsigned b) 0) as [E|E].
  - injection H as <- <-. split; [|intros []]. cbn [app]. f_equal. apply bv_eq. rewrite E. reflexivity.
  - destruct (split_nul d) as [[l0 r0]|] eqn:S; [|discriminate]. injection H as <- <-.
    destruct (IH l0 r0 eq_refl) as [-> NZ]. split; [reflexivity|].
    intros [X|X]; [apply E; rewrite X; reflexivity | exact (NZ X)].
Qed.

Lemma ce_nul_eq : forall l1 r1 l2 r2, l1 ++ Z_to_bv 8 0 :: r1 = l2 ++ Z_to_bv 8 0 :: r2 ->
  ~ In (Z_to_bv 8 0) l1 -> ~ In (Z_to_bv 8 0) l2 -> l1 = l2 /\ r1 = r2.
Proof.
  intros l1 r1 l2 r2 E N1 N2.
  pose proof (ce_split_nul l1 r1 N1) as S1. rewrite E, (ce_split_nul l2 r2 N2) in S1.
  injection S1 as <- <-. split; reflexivity.
Qed.

Lemma ce_find_text : forall y rs i, find_text y rs = Some i ->
  (i < length rs)%nat /\ snd (nth i rs (0, [])) = y /\ forall k, (k < i)%nat -> snd (nth k rs (0, [])) <> y.
Proof.
  intros y rs. induction rs as [|r rs IH]; intros i H; cbn [find_text] in H; [discriminate|].
  destruct (list_eqb (bzs (snd r)) (bzs y)) eqn:E.
  - injection H as <-. apply ce_eqb_true in E. apply ce_bzs_inj in E. cbn [length nth].
    split; [lia|]. split; [exact E | intros k Hk; lia].
  - destruct (find_text y rs) as [i0|] eqn:FT; cbn in H; [|discriminate]. injection H as <-.
    destruct (IH i0 eq_refl) as (H1 & H2 & H3). cbn [length nth]. split; [lia|]. split; [exact H2|].
    intros [|k] Hk.
    + intros X. rewrite X in E. rewrite (proj2 (ce_eqb_true (bzs y) (bzs y)) eq_refl) in E. discriminate.
    + apply H3. lia.
Qed.

Lemma ce_nth_skipn : forall {X} (l : list X) k t d, nth t (skipn k l) d = nth (k + t) l d.
Proof.
  intros X l. induction l as [|x l IH]; intros k t d.
  - destruct k; cbn; [reflexivity|]. destruct t; reflexivity.
  - destruct k; cbn; [reflexivity|]. apply IH.
Qed.

Lemma ce_byte : forall m a (ln : list byte) i, bytes_at rsegs m a ln -> (i < length ln)%nat ->
  ov_read_bytes rsegs m (Z_to_bv 64 (a + Z.of_nat i)) 1 = Some [nth i ln (Z_to_bv 8 0)].
Proof.
  intros m a ln i H Hi. change (Z_to_bv 64 (a + Z.of_nat i)) with (wa (a + Z.of_nat i)).
  rewrite (bytes_at_read rsegs m a ln (Z.of_nat i) 1 H ltac:(lia)) by (rewrite Nat2Z.id; lia).
  rewrite Nat2Z.id. clear H. revert ln Hi. induction i as [|i IH]; intros [|b ln] Hi; cbn in Hi |- *; try lia.
  - reflexivity.
  - apply IH. lia.
Qed.

Lemma ce_skip : forall m a (l : list byte) k, bytes_at rsegs m a l -> (k <= length l)%nat ->
  bytes_at rsegs m (a + Z.of_nat k) (skipn k l).
Proof.
  intros m a l k H Hk. rewrite <- (firstn_skipn k l) in H. apply bytes_at_app in H. destruct H as [_ H].
  rewrite length_firstn, Nat.min_l in H by exact Hk. exact H.
Qed.

Lemma ce_first : forall m a (l : list byte) k, bytes_at rsegs m a l -> bytes_at rsegs m a (firstn k l).
Proof.
  intros m a l k H. rewrite <- (firstn_skipn k l) in H. apply bytes_at_app in H. exact (proj1 H).
Qed.

Lemma ce_lr_tr : forall m m' W V (recs : list (word * list byte)), munch W m m' ->
  (forall j r, nth_error recs j = Some r -> list_rec m V j r) ->
  (forall j r, nth_error recs j = Some r ->
     disjoint_from W (V + 16 * Z.of_nat j) 16 /\
     disjoint_from W (bv_unsigned (fst r)) (Z.of_nat (length (snd r)) + 1)) ->
  forall j r, nth_error recs j = Some r -> list_rec m' V j r.
Proof.
  intros m m' W V recs MU LR D j r H. destruct (LR j r H) as [B1 B2]. destruct (D j r H) as [D1 D2].
  split.
  - eapply bytes_at_transport; [exact B1 | exact MU |]. rewrite length_app, !length_le8. exact D1.
  - eapply bytes_at_transport; [exact B2 | exact MU |]. rewrite length_app. cbn [length].
    replace (Z.of_nat (length (snd r) + 1)) with (Z.of_nat (length (snd r)) + 1) by lia. exact D2.
Qed.

Lemma ce_e1 : next_line_contract -> list_find_contract -> has_prefix_contract ->
  forall ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo SP AT V N CAP : Z) (at0 nout out : word)
    (j ob ln rest P slack : list byte) (recs : list (word * list byte)) (i : nat) (r : word * list byte),
  stk rsegs m lo SP -> lo + 80 <= SP -> 0x100000 <= lo -> SP mod 16 = 0 -> SP + 112 < 2 ^ 63 ->
  mem_inv rsegs m ->
  rw_cells rsegs m SP [CB 24 j] ->
  rw_cells rsegs m AT [C8 at0] -> AT mod 8 = 0 -> SP + 24 <= AT -> AT + 8 <= 2 ^ 63 ->
  bytes_at rsegs m G_NOUT (le8 nout) -> bytes_at rsegs m G_OUT (le8 out) ->
  bytes_at rsegs m (bv_unsigned out) ob -> Z.of_nat (length ob) = bv_unsigned nout ->
  bv_unsigned out + bv_unsigned nout <= lo -> 0 < bv_unsigned out ->
  skipn (Z.to_nat (bv_unsigned at0)) ob = ln ++ Z_to_bv 8 0 :: rest -> ~ In (Z_to_bv 8 0) ln ->
  (4 <= length ln)%nat -> skipn (length ln - 4) ln = END4 ->
  rw_cells rsegs m (bv_unsigned s1) [C8 (Z_to_bv 64 V); C4 (Z_to_bv 64 N); C4 (Z_to_bv 64 CAP)] ->
  bv_unsigned s1 + 16 <= lo -> bv_unsigned s1 mod 8 = 0 ->
  0 <= N < 2 ^ 26 -> Z.of_nat (length recs) = N -> (0 < N -> 0 < V /\ V mod 8 = 0) -> 0 <= V ->
  V + 16 * N <= lo ->
  (forall k r', nth_error recs k = Some r' -> list_rec m V k r') ->
  (forall k r', nth_error recs k = Some r' -> bv_unsigned (fst r') + Z.of_nat (length (snd r')) + 1 <= lo) ->
  nth_error recs i = Some r -> snd r = firstn (length ln - 4) ln ->
  (forall k r', (k < i)%nat -> nth_error recs k = Some r' -> snd r' <> firstn (length ln - 4) ln) ->
  bytes_at rsegs m (bv_unsigned s0) (P ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) P ->
  (- (bv_unsigned s0 + Z.of_nat (length P) + 1)) mod 8 <= Z.of_nat (length slack) ->
  (bv_unsigned s0 + Z.of_nat (length P + 1 + length slack) <= lo \/ SP + 24 <= bv_unsigned s0) ->
  (AT + 8 <= bv_unsigned s0 \/ bv_unsigned s0 + Z.of_nat (length P + 1 + length slack) <= AT) ->
  prefix_of P ln ->
  s4 = Z_to_bv 64 4 -> s6 = Z_to_bv 64 5 -> s7 = Z_to_bv 64 0x646e6520 ->
  evt rsegs (fun ms' => exists t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      munch [(SP - 80, SP + 24); (AT, AT + 8)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
      stk rsegs m' lo SP /\
      rw_cells rsegs m' AT [C8 (Z_to_bv 64 (bv_unsigned at0 + Z.of_nat (length ln) + 1))] /\
      (exists j', rw_cells rsegs m' SP [CB 24 j']) /\
      ms' = MS (mkR (Z_to_bv 64 0x14c88) (Z_to_bv 64 SP) gp tp t0' t1' t2' s0 s1 s1 (Z_to_bv 64 (Z.of_nat i))
                    a2' a3' a4' a5' a6' a7' (Z_to_bv 64 AT) (Z_to_bv 64 (Z.of_nat i)) s4 s5 s6 s7 s8 s9 s10 s11
                    t3' t4' t5' t6')
               F (Z_to_bv 64 0x14d58) fc None m' (seg_rom rsegs))
    (MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 AT) s3 s4 s5 s6 s7 s8 s9
             s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14bf4) fc None m (seg_rom rsegs)).
Proof.
  intros NL LF HP ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo SP AT V N CAP at0 nout out j ob ln rest P slack recs i r
    ST LO HLO SPA SPH MI FR AC ATA ATB ATC GN GO OB OL OUTL OUT0 SK NZ N4 E4 HC S1L S1A HN HRL HNV HV0 HVL
    LR LRB Hi Hsr Hmin HPB NZP SL PD PA PFX ES4 ES6 ES7.
  subst s4 s6 s7.
  pose proof (zr_word s0) as R0. pose proof (zr_word s1) as R1. pose proof (zr_word out) as Ro.
  pose proof (zr_word nout) as Rn. pose proof (zr_word at0) as Ra. unfold inr64 in *.
  assert (USP : bv_unsigned (Z_to_bv 64 SP) = SP) by (apply unsigned_lit; destruct ST as (? & ? & _); lia).
  assert (L0 : 0 <= lo) by (destruct ST as (? & _); lia).
  assert (HNLF : NEXT_LINE_FRAME = 48) by reflexivity.
  assert (HLFF : LIST_FIND_FRAME = 80) by reflexivity.
  assert (HHPK : HAS_PREFIX_K = 32) by reflexivity.
  assert (GNv : G_NOUT = 202976) by reflexivity.
  assert (GOv : G_OUT = 202992) by reflexivity.
  assert (LNL : bv_unsigned at0 + Z.of_nat (length ln) + 1 <= bv_unsigned nout).
  { pose proof (f_equal (@length byte) SK) as L. rewrite length_skipn, length_app in L. cbn [length] in L. lia. }
  assert (OBA : bytes_at rsegs m (bv_unsigned out + bv_unsigned at0) (ln ++ Z_to_bv 8 0 :: rest)).
  { rewrite <- SK. replace (bv_unsigned out + bv_unsigned at0) with (bv_unsigned out + Z.of_nat (Z.to_nat (bv_unsigned at0)))
      by lia. apply ce_skip; [exact OB | lia]. }
  assert (LNB : bytes_at rsegs m (bv_unsigned out + bv_unsigned at0) ln) by (apply bytes_at_app in OBA; exact (proj1 OBA)).
  assert (NB : forall t, (t < 4)%nat -> nth (length ln - 4 + t) ln (Z_to_bv 8 0) = nth t END4 (Z_to_bv 8 0)).
  { intros t Ht. rewrite <- E4, ce_nth_skipn. reflexivity. }
  assert (HV8 : bytes_at rsegs m (bv_unsigned s1) (le8 (Z_to_bv 64 V))).
  { destruct HC as [[_ B] _]. cbn [cells_bytes cbytes] in B. apply bytes_at_app in B. exact (proj1 B). }
  assert (HN4 : bytes_at rsegs m (bv_unsigned s1 + 8) (le4 (Z_to_bv 64 N))).
  { destruct HC as [[_ B] _]. cbn [cells_bytes cbytes] in B. apply bytes_at_app in B. destruct B as [_ B].
    rewrite length_le8 in B. apply bytes_at_app in B. exact (proj1 B). }
  destruct (ce_frame24 m SP j FR) as (j0 & j1 & F0 & F1). clear FR.
  destruct (ce_frame16 m (SP + 8) j1 F1) as (jn & jl & FN & FL). clear F1.
  replace (SP + 8 + 8) with (SP + 16) in FL by lia.
  pose proof (munch_refl [(SP - 80, SP + 24); (AT, AT + 8)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  ce_hide LR. ce_hide LRB. ce_hide HPB. ce_hide LNB. ce_hide OBA. ce_hide HV8. ce_hide HN4. ce_hide HC.
  ce_hide GN. ce_hide GO. ce_hide OB. ce_hide F0.
  do 4 step.
  eapply evt_cut.
  { eapply NL with (lo := lo) (PA := AT) (PL := SP + 16) (PN := SP + 8) (at0 := at0) (nout := nout) (out := out)
      (jl := jl) (jn := jn) (ob := ob).
    all: rewrite ?USP, ?HNLF.
    all: first [ exact ST | lia | exact MI | exact AC | exact FL | exact FN
               | (Z.div_mod_to_equations; lia) | ce_dj | exact GN | exact GO | exact OB | exact OL
               | (intros _; split; [lia | rewrite SK; apply in_or_app; right; left; reflexivity]) ]. }
  intros ms1 (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & u14 & m1 &
    -> & MU1 & WM1 & MI1 & ST1 & GN1 & GO1 & OB1 & ARM).
  rewrite USP, HNLF in MU1. rewrite USP in ST1.
  replace (ret_pc (Z_to_bv 64 0x14c04)) with (Z_to_bv 64 0x14c04) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  assert (F01 : rw_cells rsegs m1 SP [CB 8 j0]).
  { unfold ce_keep in F0. apply (rw_cells_transport rsegs _ m m1 _ _ F0 MU1 WM1). cbn [cells_size csize]. ce_dj. }
  ce_hide F01.
  assert (MUa : munch [(SP - 80, SP + 24); (AT, AT + 8)] m m1).
  { eapply munch_weaken; [| exact MU1]. unfold sub_fp. cbn [outside]. intros; lia. }
  clear MU MU1. rename MUa into MU. clear WM. rename WM1 into WM.
  destruct ARM as [(AE & _)|(ln0 & _ & (rest0 & SK0 & NZ0) & A1 & PAc & PLc & PNc)]; [exfalso; lia|].
  rewrite SK in SK0. destruct (ce_nul_eq ln rest ln0 rest0 SK0 NZ NZ0) as [E1 E2]. subst ln0 rest0 u3.
  step. if_cases Q; [vm_compute in Q; discriminate|].
  step. step. if_cases Q2.
  { exfalso. zify_cond Q2. try rewrite (unsigned_lit (Z.of_nat (length ln))) in Q2 by lia.
    try rewrite unsigned_lit_wrap in Q2. Z.div_mod_to_equations. lia. }
  step. step.
  step. ce_trap.
  step. ce_trap.
  step. ce_trap.
  step. ce_trap.
  assert (LNB1 : bytes_at rsegs m1 (bv_unsigned out + bv_unsigned at0) ln).
  { unfold ce_keep in LNB. eapply bytes_at_transport; [exact LNB | exact MU | ce_dj]. }
  assert (RDt : forall t, (t < 4)%nat ->
    ov_read_bytes rsegs m1 (Z_to_bv 64 (bv_unsigned out + bv_unsigned at0 + Z.of_nat (length ln) + (Z.of_nat t - 4))) 1
    = Some [nth t END4 (Z_to_bv 8 0)]).
  { intros t Ht. rewrite <- (NB t Ht).
    replace (bv_unsigned out + bv_unsigned at0 + Z.of_nat (length ln) + (Z.of_nat t - 4))
      with (bv_unsigned out + bv_unsigned at0 + Z.of_nat (length ln - 4 + t)) by lia.
    apply ce_byte; [exact LNB1 | lia]. }
  pose proof (RDt 0%nat ltac:(lia)) as RD4. pose proof (RDt 1%nat ltac:(lia)) as RD3.
  pose proof (RDt 2%nat ltac:(lia)) as RD2. pose proof (RDt 3%nat ltac:(lia)) as RD1. clear RDt.
  cbn [nth END4] in RD4, RD3, RD2, RD1.
  change (Z.of_nat 0 - 4) with (-4) in RD4. change (Z.of_nat 1 - 4) with (-3) in RD3.
  change (Z.of_nat 2 - 4) with (-2) in RD2. change (Z.of_nat 3 - 4) with (-1) in RD1.
  do 4 step.
  do 7 step.
  if_cases Q3; [vm_compute in Q3; discriminate|].
  assert (UV : bv_unsigned (Z_to_bv 64 V) = V) by (apply unsigned_lit; lia).
  assert (UOA : bv_unsigned (Z_to_bv 64 (bv_unsigned out + bv_unsigned at0)) = bv_unsigned out + bv_unsigned at0)
    by (apply unsigned_lit; lia).
  assert (ULN : bv_unsigned (Z_to_bv 64 (Z.of_nat (length ln))) = Z.of_nat (length ln)) by (apply unsigned_lit; lia).
  pose proof LRB as LRB'. unfold ce_keep in LRB'.
  assert (LR1 : forall k r', nth_error recs k = Some r' -> list_rec m1 V k r').
  { unfold ce_keep in LR. apply (ce_lr_tr m m1 _ V recs MU LR). intros k r' Hk.
    assert (Hkl : (k < length recs)%nat) by (apply nth_error_Some; rewrite Hk; discriminate).
    pose proof (LRB' k r' Hk). split; ce_dj. }
  assert (HV81 : bytes_at rsegs m1 (bv_unsigned s1) (le8 (Z_to_bv 64 V))).
  { unfold ce_keep in HV8. eapply bytes_at_transport; [exact HV8 | exact MU | rewrite length_le8; ce_dj]. }
  assert (HN41 : bytes_at rsegs m1 (bv_unsigned s1 + 8) (le4 (Z_to_bv 64 N))).
  { unfold ce_keep in HN4. eapply bytes_at_transport; [exact HN4 | exact MU | rewrite length_le4; ce_dj]. }
  assert (SRC1 : bytes_at rsegs m1 (bv_unsigned out + bv_unsigned at0) (firstn (length ln - 4) ln))
    by (apply ce_first; exact LNB1).
  do 3 step.
  eapply evt_cut.
  { eapply LF with (lo := lo) (N := N) (v := Z_to_bv 64 V) (recs := recs) (src := firstn (length ln - 4) ln).
    all: unfold LIST_FIND_FRAME; rewrite ?USP, ?UV, ?UOA.
    all: first [ exact ST1 | lia | exact MI1 | exact HV81 | exact HN41 | exact LR1 | exact SRC1 | exact HNV | assumption
               | (rewrite unsigned_lit by lia; rewrite length_firstn; lia)
               | (left; lia) | (intros _; left; lia) | (left; rewrite length_firstn; lia)
               | (intros k r' Hk; left; pose proof (LRB' k r' Hk); lia) ]. }
  intros ms2 (v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & m2 &
    -> & MU2 & WM2 & MI2 & ST2 & FRES).
  unfold LIST_FIND_FRAME in MU2. rewrite USP in MU2, ST2.
  replace (ret_pc (Z_to_bv 64 0x14c60)) with (Z_to_bv 64 0x14c60) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  destruct FRES as [(jj & rr & Hjj & Hsr' & Hmin' & ->)|(Hnone & ->)]; [|exfalso; exact (Hnone i r Hi Hsr)].
  assert (Eji : jj = i).
  { destruct (Nat.lt_trichotomy jj i) as [Hlt|[Heq|Hgt]];
      [exfalso; exact (Hmin jj rr Hlt Hjj Hsr') | exact Heq | exfalso; exact (Hmin' i r Hgt Hi Hsr)]. }
  subst jj. rewrite Hi in Hjj. injection Hjj as <-.
  assert (Hil : (i < length recs)%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
  step. if_cases Q4.
  { exfalso. zify_cond Q4. try (rewrite unsigned_lit in Q4 by lia). try (rewrite unsigned_lit_wrap in Q4).
    Z.div_mod_to_equations. lia. }
  assert (LNB2 : bytes_at rsegs m2 (bv_unsigned out + bv_unsigned at0) ln).
  { eapply bytes_at_transport; [exact LNB1 | exact MU2 | ce_dj]. }
  assert (HPB2 : bytes_at rsegs m2 (bv_unsigned s0) (P ++ Z_to_bv 8 0 :: slack)).
  { unfold ce_keep in HPB. eapply bytes_at_transport; [eapply bytes_at_transport; [exact HPB | exact MU |] | exact MU2 |].
    - rewrite length_app. cbn [length]. ce_dj.
    - rewrite length_app. cbn [length]. ce_dj. }
  assert (PL2 : rw_cells rsegs m2 (SP + 16) [C8 (Z_to_bv 64 (bv_unsigned out + bv_unsigned at0))]).
  { apply (rw_cells_transport rsegs _ m1 m2 _ _ PLc MU2 WM2). cbn [cells_size csize]. ce_dj. }
  assert (PN2 : rw_cells rsegs m2 (SP + 8) [C8 (Z_to_bv 64 (Z.of_nat (length ln)))]).
  { apply (rw_cells_transport rsegs _ m1 m2 _ _ PNc MU2 WM2). cbn [cells_size csize]. ce_dj. }
  do 5 step.
  eapply evt_cut.
  { eapply HP with (lo := lo) (S := ln) (P := P) (slack := slack).
    all: unfold HAS_PREFIX_K; rewrite ?USP, ?UOA, ?ULN.
    all: first [ exact LNB2 | reflexivity | exact HPB2 | exact NZP | exact SL | exact MI2 | exact ST2 | lia
               | (left; lia) | (destruct PD; [left; lia | right; lia]) ]. }
  intros ms3 (w0 & w1 & w2 & b0 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & m3 &
    -> & MU3 & WM3 & MI3 & ST3 & PR).
  unfold HAS_PREFIX_K in MU3. rewrite USP in MU3, ST3.
  replace (ret_pc (Z_to_bv 64 0x14c78)) with (Z_to_bv 64 0x14c78) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  destruct PR as [(_ & ->)|(NP & _)]; [|exfalso; exact (NP PFX)].
  assert (MUs : munch [(SP - 80, SP)] m1 m3).
  { apply (munch_trans _ m1 m2 m3 MU2). eapply munch_weaken; [| exact MU3]. unfold sub_fp. cbn [outside]. intros; lia. }
  pose proof (wmono_trans rsegs _ _ _ WM2 WM3) as WMs.
  step. if_cases Q5; [vm_compute in Q5; discriminate|].
  step. step. step.
  assert (PA3 : rw_cells rsegs m3 AT [C8 (Z_to_bv 64 (bv_unsigned at0 + Z.of_nat (length ln) + 1))]).
  { apply (rw_cells_transport rsegs _ m1 m3 _ _ PAc MUs WMs). cbn [cells_size csize]. ce_dj. }
  assert (PL3 : rw_cells rsegs m3 (SP + 8 + 8) [C8 (Z_to_bv 64 (bv_unsigned out + bv_unsigned at0))]).
  { replace (SP + 8 + 8) with (SP + 16) by lia.
    apply (rw_cells_transport rsegs _ m1 m3 _ _ PLc MUs WMs). cbn [cells_size csize]. ce_dj. }
  assert (PN3 : rw_cells rsegs m3 (SP + 8) [C8 (Z_to_bv 64 (Z.of_nat (length ln)))]).
  { apply (rw_cells_transport rsegs _ m1 m3 _ _ PNc MUs WMs). cbn [cells_size csize]. ce_dj. }
  assert (F03 : rw_cells rsegs m3 SP [CB 8 j0]).
  { unfold ce_keep in F01. apply (rw_cells_transport rsegs _ m1 m3 _ _ F01 MUs WMs). cbn [cells_size csize]. ce_dj. }
  destruct (ce_frame16j m3 (SP + 8) _ _ PN3 PL3) as (j16 & F16).
  assert (MUf : munch [(SP - 80, SP + 24); (AT, AT + 8)] m m3).
  { apply (munch_trans _ m m1 m3 MU). eapply munch_weaken; [| exact MUs]. unfold sub_fp. cbn [outside]. intros; lia. }
  pose proof (wmono_trans rsegs _ _ _ WM WMs) as WMf.
  apply evt_done. do 14 eexists.
  split; [exact MUf|]. split; [exact WMf|]. split; [exact MI3|]. split; [exact ST3|]. split; [exact PA3|].
  split; [exact (ce_frame24j m3 SP _ _ F03 F16)|].
  reflexivity.
Qed.

Lemma ce_head : has_prefix_contract ->
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo V PF : Z) (rs : list (Z * list byte)) (P slack : list byte)
    (gone : Z),
  stk rsegs m lo (bv_unsigned sp) -> lo + 144 <= bv_unsigned sp -> 0x100000 <= lo -> bv_unsigned sp < 2 ^ 63 ->
  mem_inv rsegs m -> 0 < bv_unsigned a0 -> bv_unsigned a0 mod 8 = 0 -> bv_unsigned a0 + 96 <= lo ->
  rw_cells rsegs m (bv_unsigned a0 + 80) [C8 (Z_to_bv 64 V)] ->
  rw_cells rsegs m (bv_unsigned a0 + 88) [C4 (Z_to_bv 64 (Z.of_nat (length rs)))] ->
  Z.of_nat (length rs) < 2 ^ 26 -> 0 <= V -> ((0 < length rs)%nat -> 0 < V /\ V mod 8 = 0) ->
  V + 16 * Z.of_nat (length rs) <= lo ->
  (forall k r, nth_error rs k = Some r ->
     rw_cells rsegs m (V + 16 * Z.of_nat k) [C8 (Z_to_bv 64 (fst r)); C8 (Z_to_bv 64 (Z.of_nat (length (snd r))))] /\
     bytes_at rsegs m (fst r) (snd r) /\ 0 <= fst r /\ fst r + Z.of_nat (length (snd r)) <= lo) ->
  0 <= PF < 2 ^ 64 -> bytes_at rsegs m PF (P ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) P ->
  (- (PF + Z.of_nat (length P) + 1)) mod 8 <= Z.of_nat (length slack) ->
  (PF + Z.of_nat (length P + 1 + length slack) <= lo \/ bv_unsigned sp <= PF) ->
  rw_cells rsegs m 0x318a8 [C1 (Z_to_bv 8 gone)] -> 0 <= gone < 256 ->
  evt rsegs (fun ms' => exists m', munch [(bv_unsigned sp - 144, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\
      mem_inv rsegs m' /\
      (((length rs = 0%nat \/ ((0 < length rs)%nat /\ gone = 0 /\ want_of P rs = 0%nat)) /\
        (exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
           ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                         t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom rsegs))) \/
       ((0 < length rs)%nat /\
        (exists jj, rw_cells rsegs m' (bv_unsigned sp + -112) (ce_frame ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 jj)) /\
        ((gone <> 0 /\
          (exists ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' s4' s6' s7' s8' s9',
           ms' = MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0' t1' t2' (Z_to_bv 64 PF)
                         (Z_to_bv 64 (bv_unsigned a0 + 80)) (Z_to_bv 64 (Z.of_nat (length rs) - 1)) a1' a2' a3' a4'
                         a5' a6' a7' a2 (Z_to_bv 64 (Z.of_nat (length rs))) s4' (Z_to_bv 64 (Z.of_nat (want_of P rs)))
                         s6' s7' s8' s9' s10 s11 t3' t4' t5' t6')
                    F (Z_to_bv 64 0x14b4c) fc None m' (seg_rom rsegs))) \/
         (gone = 0 /\ (0 < want_of P rs)%nat /\
          (exists ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' s9',
           ms' = MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0' t1' t2' (Z_to_bv 64 PF)
                         (Z_to_bv 64 (bv_unsigned a0 + 80)) a0' a1' a2' a3' a4' a5' a6' a7' a2
                         (Z_to_bv 64 (Z.of_nat (length rs))) (Z_to_bv 64 4) (Z_to_bv 64 (Z.of_nat (want_of P rs)))
                         (Z_to_bv 64 5) (Z_to_bv 64 0x646e6520) (Z_to_bv 64 (Z.of_nat (want_of P rs) - 1)) s9' s10 s11
                         t3' t4' t5' t6')
                    F (Z_to_bv 64 0x14bf4) fc None m' (seg_rom rsegs)))))))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 PF) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14a78) fc None m (seg_rom rsegs)).
Proof.
  intros HP ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo V PF rs P slack gone ST LO HLO SPH MI HA0 HA8 HA1 CV CN HN HV0 HVP HVL RS HPF HPB NZ SL PDj GC Hg.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. cbn in Rsp.
  assert (UV : bv_unsigned (Z_to_bv 64 V) = V) by (apply unsigned_lit; lia).
  eapply evt_cut.
  { exact (ce_pro ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 PF) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6 F fc m lo (Z_to_bv 64 V) (Z.of_nat (length rs)) gone ST ltac:(lia) HLO MI HA0 HA8 HA1 CV CN
             ltac:(lia) ltac:(intros X; rewrite UV; destruct (HVP ltac:(lia)); lia) GC Hg). }
  intros ms1 (m1 & MU1 & WM1 & MI1 & [(Hn0 & u0 & u1 & ->)|(Hn0 & jj & u0 & u1 & ST1 & FR1 & ->)]).
  - apply evt_done. exists m1.
    split; [eapply munch_weaken; [|exact MU1]; unfold sub_fp; cbn [outside]; intros; lia|].
    split; [exact WM1|]. split; [exact MI1|].
    left. split; [left; lia|].
    exists t0, t1, t2, u0, u1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6. reflexivity.
  - assert (USP1 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -112)) = bv_unsigned sp + -112)
      by (apply unsigned_lit; lia).
    destruct (HVP ltac:(lia)) as (HV0' & HV8').
    rewrite UV.
    assert (RS1 : forall k r, nth_error rs k = Some r ->
      rw_cells rsegs m1 (V + 16 * Z.of_nat k) [C8 (Z_to_bv 64 (fst r)); C8 (Z_to_bv 64 (Z.of_nat (length (snd r))))] /\
      bytes_at rsegs m1 (fst r) (snd r) /\ 0 <= fst r /\ fst r + Z.of_nat (length (snd r)) <= bv_unsigned sp + -112 - 32).
    { intros k r Hk. destruct (RS k r Hk) as (X1 & X2 & X3 & X4).
      assert (Hkl : (k < length rs)%nat) by (apply nth_error_Some; rewrite Hk; discriminate).
      split; [|split; [|split; [exact X3 | lia]]].
      - apply (rw_cells_transport rsegs _ m m1 _ _ X1 MU1 WM1). cbn [disjoint_from cells_size csize]. split; [lia | exact I].
      - apply (bytes_at_transport rsegs _ m m1 _ _ X2 MU1). cbn [disjoint_from]. split; [lia | exact I]. }
    assert (HPB1 : bytes_at rsegs m1 PF (P ++ Z_to_bv 8 0 :: slack)).
    { apply (bytes_at_transport rsegs _ m m1 _ _ HPB MU1). cbn [disjoint_from]. rewrite length_app. cbn [length].
      split; [lia | exact I]. }
    assert (GC1 : rw_cells rsegs m1 0x318a8 [C1 (Z_to_bv 8 gone)]).
    { apply (rw_cells_transport rsegs _ m m1 _ _ GC MU1 WM1). cbn [disjoint_from cells_size csize]. split; [lia | exact I]. }
    eapply evt_cut.
    { eapply (ce_count HP rs P slack (length rs) 0%nat V PF) with (lo := lo).
      - lia.
      - lia.
      - exact UV.
      - rewrite unsigned_lit by lia. lia.
      - rewrite unsigned_lit by lia. lia.
      - rewrite USP1. exact ST1.
      - rewrite USP1. lia.
      - exact MI1.
      - exact HV0'.
      - exact HV8'.
      - lia.
      - exact HN.
      - rewrite USP1. lia.
      - rewrite USP1. exact RS1.
      - exact HPB1.
      - exact NZ.
      - exact SL.
      - lia.
      - lia.
      - rewrite USP1. lia. }
    intros ms2 (v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & v15 & v16 & v17 & m2 &
      -> & MU2 & WM2 & MI2 & ST2).
    rewrite USP1 in MU2.
    assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp + -112) (ce_frame ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 jj)).
    { apply (rw_cells_transport rsegs _ m1 m2 _ _ FR1 MU2 WM2). cbn [disjoint_from]. split; [lia | exact I]. }
    assert (GC2 : rw_cells rsegs m2 0x318a8 [C1 (Z_to_bv 8 gone)]).
    { apply (rw_cells_transport rsegs _ m1 m2 _ _ GC1 MU2 WM2). cbn [disjoint_from cells_size csize]. split; [lia | exact I]. }
    assert (MUt : munch [(bv_unsigned sp - 144, bv_unsigned sp)] m m2).
    { apply (munch_trans _ m m1 m2).
      - eapply munch_weaken; [|exact MU1]. unfold sub_fp. cbn [outside]. intros; lia.
      - eapply munch_weaken; [|exact MU2]. unfold sub_fp. cbn [outside]. intros; lia. }
    pose proof (wmono_trans rsegs _ _ _ WM1 WM2) as WMt.
    pose proof (ce_want_le P rs) as WLE.
    eapply evt_cut.
    { eapply ce_mid with (B := bv_unsigned sp + -112) (n := Z.of_nat (length rs)) (W := Z.of_nat (want_of P rs))
        (gone := gone) (rav := ra) (s0v := s0) (s1v := s1) (s2v := s2) (s3v := s3) (s4v := s4) (s5v := s5)
        (s6v := s6) (s7v := s7) (s8v := s8) (s9v := s9) (j := jj).
      - reflexivity.
      - lia.
      - lia.
      - exact MI2.
      - exact FR2.
      - exact GC2.
      - exact Hg.
      - lia.
      - lia. }
    intros ms3 [(Hg0 & ->)|[(Hg0 & HW0 & a0x & a1x & ->)|(Hg0 & HW0 & a0x & a1x & ->)]].
    + apply evt_done. exists m2. split; [exact MUt|]. split; [exact WMt|]. split; [exact MI2|].
      right. split; [lia|]. split; [exists jj; exact FR2|]. left. split; [exact Hg0|].
      do 20 eexists. reflexivity.
    + apply evt_done. exists m2. split; [exact MUt|]. split; [exact WMt|]. split; [exact MI2|].
      left. split; [right; split; [lia|]; split; [exact Hg0 | lia]|].
      replace (bv_unsigned sp + -112 + 112) with (bv_unsigned sp) by lia. rewrite (Z_to_bv_bv_unsigned sp).
      do 15 eexists. reflexivity.
    + apply evt_done. exists m2. split; [exact MUt|]. split; [exact WMt|]. split; [exact MI2|].
      right. split; [lia|]. split; [exists jj; exact FR2|]. right. split; [exact Hg0|]. split; [lia|].
      do 17 eexists. reflexivity.
Qed.

From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YK11 YK0o YK0s YK14 YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YL0i YL01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Contract ContractT.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import RelayFrame RelayRunT RelayRunF TrNames ListRep
  ListTr HarnessTr TrModel check_shape_ends_c list_drop_c KindB HarnessGlue HarnessFrame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YM05.

Definition ce_ftl (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 : word) : list cell :=
  [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma ce_out_dec : forall W x, outside W x \/ ~ outside W x.
Proof.
  induction W as [|[lo hi] W IH]; intros x; cbn [outside]; [left; exact I|].
  destruct (IH x) as [H|H]; [|right; tauto].
  destruct (Z_le_gt_dec lo x); destruct (Z_lt_ge_dec x hi); [right; lia | left; split; [lia | exact H] ..].
Qed.

Lemma ce_getr : forall {fx : YK11.FPState} R (r : bv 5), bv_eqb r 0 = false -> YK11.getr R r = reg_get R r.
Proof. intros fx R r E. unfold YK11.getr. rewrite E. reflexivity. Qed.

Ltac rgx GR := lazymatch goal with |- reg_get ?R ?r = _ =>
  change (reg_get R r) with (YK11.getr R r); rewrite GR, (ce_getr _ r eq_refl); simp_regs end.

Lemma ce_in_rev : forall {X} (l : list X) x, In x (List.rev l) <-> In x l.
Proof.
  intros X l x. induction l as [|y l IH]; cbn [List.rev]; [tauto|].
  rewrite in_app_iff, IH. cbn [In]. tauto.
Qed.

Lemma ce_skipn_S : forall {X} (l : list X) i x, nth_error l i = Some x -> skipn i l = x :: skipn (S i) l.
Proof.
  intros X l. induction l as [|y l IH]; intros [|i] x H; cbn in H |- *; try discriminate.
  - injection H as <-. reflexivity.
  - apply IH. exact H.
Qed.

Lemma ce_skip_line : forall (ob0 l d' : list byte) a, 0 <= a ->
  skipn (Z.to_nat a) ob0 = l ++ Z_to_bv 8 0 :: d' -> skipn (Z.to_nat (a + Z.of_nat (length l) + 1)) ob0 = d'.
Proof.
  intros ob0 l d' a Ha E.
  replace (Z.to_nat (a + Z.of_nat (length l) + 1)) with (S (length l) + Z.to_nat a)%nat by lia.
  rewrite <- skipn_skipn, E. rewrite skipn_app, skipn_all2 by lia. cbn [app].
  replace (S (length l) - length l)%nat with 1%nat by lia. reflexivity.
Qed.

Lemma ce_drop_pre : forall (l Y : list (Z * list byte)) i, (i < length l)%nat ->
  drop_nth i (firstn (S i) l ++ Y) = firstn i l ++ Y.
Proof.
  intros l Y i Hi. unfold drop_nth.
  assert (Lf : length (firstn (S i) l) = S i) by (rewrite length_firstn; lia).
  rewrite firstn_app, Lf. replace (i - S i)%nat with 0%nat by lia. rewrite firstn_O, app_nil_r, firstn_firstn.
  rewrite Nat.min_l by lia. f_equal.
  rewrite skipn_app, skipn_all2 by lia. rewrite Lf, Nat.sub_diag. reflexivity.
Qed.

Lemma ce_fcons : forall (P0 : list byte) (r : Z * list byte) l,
  filter (fun r => prefixb P0 (snd r)) (r :: l) =
    (if prefixb P0 (snd r) then r :: filter (fun r => prefixb P0 (snd r)) l
     else filter (fun r => prefixb P0 (snd r)) l) /\
  filter (fun r => negb (prefixb P0 (snd r))) (r :: l) =
    (if prefixb P0 (snd r) then filter (fun r => negb (prefixb P0 (snd r))) l
     else r :: filter (fun r => negb (prefixb P0 (snd r))) l).
Proof.
  intros P0 r l. change (r :: l) with ([r] ++ l).
  rewrite !list_basics.list.filter_app, !list_basics.list.filter_singleton.
  destruct (prefixb P0 (snd r)) eqn:E; split;
    match goal with |- context [decide ?X] => destruct (decide X) as [D|D] end; cbn in *;
    first [reflexivity | contradiction | (exfalso; apply D; exact I) | (rewrite E in D; cbn in D; contradiction)
          | (exfalso; apply D; rewrite E; exact I)].
  Unshelve. all: exact [].
Qed.

Lemma ce_ends_len : forall P0 w rs d, ends_run P0 rs d w <> None -> (w <= length rs)%nat.
Proof.
  intros P0 w. induction w as [|w IH]; intros rs d H; [lia|].
  cbn [ends_run] in H.
  destruct (split_nul d) as [[l d']|]; [|congruence].
  destruct (Nat.leb 4 (length l) && list_eqb (bzs (skipn (length l - 4) l)) (bzs END4) && prefixb P0 l);
    [|congruence].
  destruct (find_text (firstn (length l - 4) l) rs) as [i|] eqn:FT; [|congruence].
  destruct (ends_run P0 (drop_nth i rs) d' w) as [[[a b] c]|] eqn:R; [|congruence].
  destruct (ce_find_text _ _ _ FT) as (Hi & _ & _).
  assert (X : ends_run P0 (drop_nth i rs) d' w <> None) by (rewrite R; discriminate).
  pose proof (IH _ _ X) as Y. unfold drop_nth in Y. rewrite length_app, length_firstn, length_skipn in Y. lia.
Qed.

Lemma ce_drop_ne : forall (l : list (Z * list byte)) i r, List.NoDup (map fst l) -> (i < length l)%nat ->
  In r (firstn i l ++ skipn (S i) l) -> fst r <> fst (nth i l (0, [])).
Proof.
  intros l i r ND Hi Hr E.
  destruct (nth_error l i) as [x|] eqn:Hx; [|apply nth_error_None in Hx; lia].
  destruct (nth_error_split l i x Hx) as (l1 & l2 & -> & L1). subst i.
  assert (F : firstn (length l1) (l1 ++ x :: l2) = l1)
    by (rewrite firstn_app, firstn_all, Nat.sub_diag, firstn_O, app_nil_r; reflexivity).
  assert (S1 : skipn (S (length l1)) (l1 ++ x :: l2) = l2).
  { rewrite skipn_app, skipn_all2 by lia. replace (S (length l1) - length l1)%nat with 1%nat by lia. reflexivity. }
  assert (N : nth (length l1) (l1 ++ x :: l2) (0, []) = x) by (rewrite app_nth2, Nat.sub_diag by lia; reflexivity).
  rewrite F, S1 in Hr. rewrite N in E.
  rewrite map_app in ND. cbn [map] in ND. apply NoDup_remove_2 in ND. apply ND. rewrite <- map_app.
  rewrite <- E. apply in_map. exact Hr.
Qed.

Lemma nret_cse : forall nm g P0 rs d, nretF (check_shape_ends_tr nm g P0 rs d) = 0%nat.
Proof.
  intros nm g P0 rs d. unfold check_shape_ends_tr. destruct (g =? 0); [|apply nret_recs_drop].
  destruct (ends_run P0 rs d (want_of P0 rs)) as [[[x y] z]|]; [apply nret_recs_drop | reflexivity].
Qed.

Section CEB.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable Bm : malloc_syms.
Variable API : AllocAPI Bm.
Variable RF : ResFormT.
Hypothesis AX : AllocExtra Bm (aa_MR API).
Hypothesis BW : blocks_writable Bm API.
Hypothesis BND : blocks_nodup Bm API.
Hypothesis HERRB : errno_addr Bm + 4 <= alloc_ceiling.

Section Run.
Hypothesis SEG : ms_segs Bm = rsegs.
Hypothesis NLC : next_line_contract.
Hypothesis LFC : list_find_contract.
Hypothesis HPC : has_prefix_contract.
Hypothesis LDC : list_drop_contract Bm API RF.

Variables (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
  (bnd : rt_R RF) (h : hsrc) (j : nat) (gone A0 : Z) (nout out : word) (ob P slack : list byte).

Local Notation zSP0 := (bv_unsigned (reg_get regs 2)).
Local Notation zSP1 := (bv_unsigned (reg_get regs 2) + -112).
Local Notation zHA := (G_S + SRC_SIZE * Z.of_nat j).
Local Notation zPF := (bv_unsigned (reg_get regs 11)).
Local Notation zAT := (bv_unsigned (reg_get regs 12)).
Local Notation zPL := (Z.of_nat (length P + 1 + length slack)).
Local Notation zNO := (bv_unsigned nout).
Local Notation zOUT := (bv_unsigned out).
Local Notation zV := (hl_v (hs_held h)).
Local Notation zCAP := (hl_cap (hs_held h)).
Local Notation RS0 := (hl_recs (hs_held h)).
Local Notation zW := (want_of P (hl_recs (hs_held h))).
Local Notation D0 := (skipn (Z.to_nat A0) ob).
Local Notation EE := (fun a : Z => G_S + SRC_SIZE * Z.of_nat j + 88 <= a < G_S + SRC_SIZE * Z.of_nat j + 92 \/
  bv_unsigned (reg_get regs 12) <= a < bv_unsigned (reg_get regs 12) + 8 \/
  (0 < hl_cap (hs_held h) /\ hl_v (hs_held h) <= a < hl_v (hs_held h) + 16 * hl_cap (hs_held h))).
Local Notation FF := (fun q : Z => In q (map fst (hl_recs (hs_held h)))).
Local Notation FT := (ce_ftl (reg_get regs 1) (reg_get regs 8) (reg_get regs 9) (reg_get regs 18) (reg_get regs 19)
  (reg_get regs 20) (reg_get regs 21) (reg_get regs 22) (reg_get regs 23) (reg_get regs 24) (reg_get regs 25)).

Hypothesis hPRE : call_pre_k Bm (aa_MR API) 8352 L A regs mem md.
Hypothesis hINIT : st_init_done A = true.
Hypothesis hRO : ro_agree rsegs mem.
Hypothesis hPLR : forall a, G_GONE <= a < G_S + SRC_SIZE * SOURCES_MAX -> img_plain Bm a.
Hypothesis hJ4 : (j < 4)%nat.
Hypothesis hR10 : reg_get regs 10 = Z_to_bv 64 zHA.
Hypothesis hSRC : src_at Bm L A mem zHA h.
Hypothesis hNDT : NoDup (texts (hs_held h)).
Hypothesis hN26 : hl_n (hs_held h) < 2 ^ 26.
Hypothesis hPB : bytes_at rsegs mem zPF (P ++ Z_to_bv 8 0 :: slack).
Hypothesis hNZP : ~ In (Z_to_bv 8 0) P.
Hypothesis hSL : (- (zPF + Z.of_nat (length P) + 1)) mod 8 <= Z.of_nat (length slack).
Hypothesis hPD : (zSP0 <= zPF /\ zPF + zPL <= 2 ^ 63) \/
  (0 <= zPF /\ zPF + zPL <= 2 ^ 64 /\ forall i, 0 <= i < zPL -> ro_addr rsegs (Z_to_bv 64 (zPF + i)) = true).
Hypothesis hATM : zAT mod 8 = 0.
Hypothesis hATS : zSP0 <= zAT.
Hypothesis hATH : zAT + 8 <= 2 ^ 63.
Hypothesis hATP : zAT + 8 <= zPF \/ zPF + zPL <= zAT.
Hypothesis hATC : rw_cells rsegs mem zAT [C8 (Z_to_bv 64 A0)].
Hypothesis hGG : 0 <= gone < 256.
Hypothesis hGB : bytes_at rsegs mem G_GONE [Z_to_bv 8 gone].
Hypothesis hGN : bytes_at rsegs mem G_NOUT (le8 nout).
Hypothesis hGO : bytes_at rsegs mem G_OUT (le8 out).
Hypothesis hOB : bytes_at rsegs mem zOUT ob.
Hypothesis hOL : Z.of_nat (length ob) = zNO.
Hypothesis hOK : ob = [] \/
  exists CO, zNO <= CO /\ In (zOUT, CO) (blocks L A) /\ fresh_block Bm zOUT CO /\ ~ In zOUT (hs_blocks h).
Hypothesis hA0 : 0 <= A0 <= zNO.
Hypothesis hER : gone = 0 -> ends_run P RS0 D0 zW <> None.
Hypothesis hRES : rt_ok RF A bnd.

Definition cePOST (c' : config) : Prop :=
  exists L' A' regs' mem' md' (H' : hlist) (ds : list (Z * list byte)) (c : Z),
    c' = mkCfg (YK11.mkst regs' (reg_get regs 1) mem' (PropExec.seg_rom rsegs)) md' /\
    relay_post Bm API 8352 EE FF L A regs mem md L' A' regs' mem' md' /\
    st_init_done A' = true /\
    (exists qs, length qs = nretF (check_shape_ends_tr (known_at L A) gone P RS0 D0) /\
       rt_ok RF A' (runF RF qs bnd (check_shape_ends_tr (known_at L A) gone P RS0 D0))) /\
    ro_agree rsegs mem' /\
    src_at Bm L' A' mem' zHA (set_held h H') /\
    hl_v H' = zV /\ hl_cap H' = zCAP /\ NoDup (texts H') /\
    ((gone <> 0 /\ hl_recs H' = filter (fun r => negb (prefixb P (snd r))) RS0 /\
      ds = filter (fun r => prefixb P (snd r)) RS0 /\ c = 0) \/
     (gone = 0 /\ ends_run P RS0 D0 zW = Some (hl_recs H', ds, c))) /\
    rw_cells rsegs mem' zAT [C8 (Z_to_bv 64 (A0 + c))] /\
    bytes_at rsegs mem' zPF (P ++ Z_to_bv 8 0 :: slack) /\
    bytes_at rsegs mem' G_GONE [Z_to_bv 8 gone] /\
    bytes_at rsegs mem' G_NOUT (le8 nout) /\
    bytes_at rsegs mem' G_OUT (le8 out) /\
    bytes_at rsegs mem' zOUT ob /\
    (forall q m, In (q, m) (blocks L A) -> ~ In q (map fst ds) -> In (q, m) (blocks L' A')) /\
    (forall q m, In (q, m) (blocks L' A') -> In (q, m) (blocks L A) /\ ~ In q (map fst ds)).

Definition ce_frm (m : word -> option byte) : Prop :=
  exists jj, rw_cells rsegs m zSP1 ([CB 24 jj] ++ FT).

Definition ce_mf (m : word -> option byte) : Prop :=
  bytes_at rsegs m zPF (P ++ Z_to_bv 8 0 :: slack) /\ bytes_at rsegs m G_GONE [Z_to_bv 8 gone] /\
  bytes_at rsegs m G_NOUT (le8 nout) /\ bytes_at rsegs m G_OUT (le8 out) /\ bytes_at rsegs m zOUT ob.

Definition ce_br (L1 : layout) (A1 : astate) (ds : list (Z * list byte)) : Prop :=
  (forall q k, In (q, k) (blocks L A) -> ~ In q (map fst ds) -> In (q, k) (blocks L1 A1)) /\
  (forall q k, In (q, k) (blocks L1 A1) -> In (q, k) (blocks L A) /\ ~ In q (map fst ds)).

Definition ce_bu (L1 : layout) (A1 : astate) (rs : list (Z * list byte)) : Prop :=
  forall r, In r rs -> In (sptr_of L A (fst r), Z.of_nat (length (snd r)) + 1) (user_blocks A1) /\
    ptr_addr L1 (sptr_of L A (fst r)) = fst r.

Definition ce_rs (L1 : layout) (A1 : astate) (Hc : hlist) (ds : list (Z * list byte)) : Prop :=
  rt_ok RF A1 (runF RF [] bnd (recs_drop_tr (map (shr (known_at L A)) ds))) /\ ce_bu L1 A1 (hl_recs Hc).

Definition ceJ (L1 : layout) (A1 : astate) (m1 : word -> option byte) (md1 : Model) (Hc : hlist)
    (ds : list (Z * list byte)) (c : Z) : Prop :=
  rmid Bm API 8352 zSP0 EE FF L A mem md L1 A1 m1 md1 /\
  st_init_done A1 = true /\ ro_agree rsegs m1 /\
  ce_rs L1 A1 Hc ds /\
  list_at Bm L1 A1 m1 (zHA + 80) Hc true /\ hl_v Hc = zV /\ hl_cap Hc = zCAP /\
  NoDup (texts Hc) /\ (forall r, In r (hl_recs Hc) -> In r RS0) /\ (forall r, In r ds -> In r RS0) /\
  (length (hl_recs Hc) <= length RS0)%nat /\
  rw_cells rsegs m1 zAT [C8 (Z_to_bv 64 (A0 + c))] /\ ce_mf m1 /\ ce_br L1 A1 ds.

Definition ceRES (Hc : hlist) (ds : list (Z * list byte)) (c : Z) : Prop :=
  (gone <> 0 /\ hl_recs Hc = filter (fun r => negb (prefixb P (snd r))) RS0 /\
   ds = List.rev (filter (fun r => prefixb P (snd r)) RS0) /\ c = 0) \/
  (gone = 0 /\ ends_run P RS0 D0 zW = Some (hl_recs Hc, ds, c)).

Lemma cf0 : aa_MR API L A mem md /\ WF A /\ bounded A /\ YK0s.ret_ok (YK11.getr regs 1) /\ zSP0 mod 16 = 0 /\
  alloc_ceiling + 8352 <= zSP0 /\ zSP0 < 2 ^ 63 /\
  (forall a, zSP0 - 8352 <= a < zSP0 -> writable_at rsegs mem a) /\ YK11.getr regs 4 = Z_to_bv 64 (ms_tp Bm) /\
  (forall a, errno_addr Bm <= a < errno_addr Bm + 4 -> writable_at rsegs mem a).
Proof.
  pose proof hPRE as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & _). rewrite SEG in H8, H10.
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
  split; [exact H6|]. split; [exact H7|]. split; [exact H8|]. split; [exact H9 | exact H10].
Qed.

Lemma cfV : list_at Bm L A mem (zHA + 80) (hs_held h) true /\ NoDup (hs_blocks h) /\
  0 <= zV /\ hl_n (hs_held h) <= zCAP < 2 ^ 30 /\ ~ In zV (map fst RS0) /\ List.NoDup (map fst RS0) /\
  (0 < zCAP -> In (zV, 16 * zCAP) (blocks L A) /\ fresh_block Bm zV (16 * zCAP) /\ 4096 <= zV /\
     zV + 16 * zCAP <= alloc_ceiling /\ zV mod 16 = 0 /\ In zV (hs_blocks h)) /\
  (forall r, In r RS0 -> In (fst r) (hs_blocks h)).
Proof.
  pose proof hSRC as S. apply src_at_iff in S. destruct S as (_ & _ & LH & ND).
  pose proof LH as (_ & HNC & HAR & HND1 & HND2 & _).
  pose proof (hf_list_head Bm L A mem (zHA + 80) (hs_held h) true LH) as (_ & _ & V0 & VB).
  pose proof cf0 as (HM0 & _).
  split; [exact LH|]. split; [exact ND|]. split; [lia|]. split; [exact HNC|]. split; [exact HND2|].
  split; [apply hf_nodup; exact HND1|].
  split.
  - intros HC. destruct HAR as [(X & _)|(_ & Hin & Hfr & _)]; [lia|].
    destruct (VB HC) as (V1 & V2).
    split; [exact Hin|]. split; [exact Hfr|]. split; [exact V1|]. split; [exact V2|].
    split; [exact (hf_blk_align Bm API L A mem md _ _ HM0 Hin)|].
    unfold hs_blocks. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right.
    exact (proj2 (hf_list_v Bm L A mem _ _ true LH HC)).
  - intros r Hr. unfold hs_blocks. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right.
    unfold list_blocks. apply in_or_app. right. apply in_map. exact Hr.
Qed.

Lemma bu0 : ce_bu L A RS0.
Proof.
  pose proof cf0 as (HM0 & _). pose proof cfV as (LH0 & _).
  pose proof LH0 as (_ & _ & _ & _ & _ & HFA0). rewrite Forall_forall in HFA0.
  intros r Hr. destruct (HFA0 r Hr) as (RIn & _).
  exact (sptr_of_spec L A (fst r) _ (BND L A mem md HM0) RIn).
Qed.

Lemma ce_stk : forall m hi, (forall a, zSP0 - 8352 <= a < zSP0 -> writable_at (ms_segs Bm) m a) ->
  zSP0 - 8352 <= hi <= zSP0 -> stk rsegs (normalize rsegs m) (zSP0 - 8352) hi.
Proof.
  intros m hi W Hhi. pose proof cf0 as (_ & _ & _ & _ & _ & HC & H63 & _).
  pose proof (@YM05.alloc_ceiling_value rc) as ACV.
  apply stk_normalize; [|lia].
  split; [lia|]. split; [lia|]. intros a Ha. assert (Wa : writable_at rsegs m a) by (rewrite <- SEG; apply W; lia).
  split; [exact Wa|]. destruct (writable_hi_present m a ltac:(lia) Wa) as [bb E]. exists bb.
  unfold mrd, wa. rewrite E. reflexivity.
Qed.

Lemma c_hi : forall K' sp' E' F' L1 A1 m1 md1 L2 A2 m2 md2 a cs,
  rmid Bm API K' sp' E' F' L1 A1 m1 md1 L2 A2 m2 md2 -> aa_MR API L1 A1 m1 md1 -> alloc_ceiling <= sp' ->
  rw_cells rsegs m1 a cs -> sp' <= a ->
  a + Z.of_nat (cells_size cs) <= 2 ^ 64 -> (forall i, 0 <= i < Z.of_nat (cells_size cs) -> ~ E' (a + i)) ->
  rw_cells rsegs m2 a cs.
Proof.
  intros K' sp' E' F' L1 A1 m1 md1 L2 A2 m2 md2 a cs R HM H1 X Ha Hb D.
  rewrite <- SEG in X |- *.
  exact (rmid_rw_hi Bm API K' sp' E' F' L1 A1 m1 md1 L2 A2 m2 md2 a cs H1 ltac:(lia) HM R X Ha Hb D).
Qed.

Lemma c_bhi : forall K' sp' E' F' L1 A1 m1 md1 L2 A2 m2 md2 a bs,
  alloc_ceiling <= sp' -> aa_MR API L1 A1 m1 md1 ->
  rmid Bm API K' sp' E' F' L1 A1 m1 md1 L2 A2 m2 md2 -> bytes_at rsegs m1 a bs -> sp' <= a ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> ~ E' (a + i)) -> bytes_at rsegs m2 a bs.
Proof.
  intros K' sp' E' F' L1 A1 m1 md1 L2 A2 m2 md2 a bs H1 HM R X Ha D.
  pose proof (bytes_at_bound rsegs m1 a bs X) as Bd.
  rewrite <- SEG in X |- *. apply (bytes_at_transfer (ms_segs Bm) m1); [exact X|]. intros i Hi.
  exact (proj1 (rmid_hi Bm API K' sp' E' F' L1 A1 m1 md1 L2 A2 m2 md2 (a + i) H1 ltac:(lia) HM R ltac:(lia) (D i Hi))).
Qed.

Lemma c_img : forall K' sp' E' F' L1 A1 m1 md1 L2 A2 m2 md2 a cs,
  alloc_ceiling <= sp' - K' -> aa_MR API L1 A1 m1 md1 ->
  rmid Bm API K' sp' E' F' L1 A1 m1 md1 L2 A2 m2 md2 -> rw_cells rsegs m1 a cs ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) -> img_plain Bm (a + i) /\ ~ E' (a + i)) ->
  rw_cells rsegs m2 a cs.
Proof.
  intros K' sp' E' F' L1 A1 m1 md1 L2 A2 m2 md2 a cs H1 HM R X D. rewrite <- SEG in X |- *.
  exact (rmid_rw_img Bm API AX K' sp' E' F' L1 A1 m1 md1 L2 A2 m2 md2 a cs (hg_img_low Bm SEG) H1 HM R X D).
Qed.

Lemma c_bimg : forall K' sp' E' F' L1 A1 m1 md1 L2 A2 m2 md2 a bs,
  alloc_ceiling <= sp' - K' -> aa_MR API L1 A1 m1 md1 ->
  rmid Bm API K' sp' E' F' L1 A1 m1 md1 L2 A2 m2 md2 -> bytes_at rsegs m1 a bs ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> img_plain Bm (a + i) /\ ~ E' (a + i)) ->
  bytes_at rsegs m2 a bs.
Proof.
  intros K' sp' E' F' L1 A1 m1 md1 L2 A2 m2 md2 a bs H1 HM R X D. rewrite <- SEG in X |- *.
  exact (rmid_bytes_img Bm API AX K' sp' E' F' L1 A1 m1 md1 L2 A2 m2 md2 a bs (hg_img_low Bm SEG) H1 HM R X D).
Qed.

Lemma c_blk : forall K' sp' E' F' L1 A1 m1 md1 L2 A2 m2 md2 q k a cs,
  rmid Bm API K' sp' E' F' L1 A1 m1 md1 L2 A2 m2 md2 -> In (q, k) (blocks L1 A1) -> 0 < k -> ~ F' q ->
  rw_cells rsegs m1 a cs -> q <= a -> a + Z.of_nat (cells_size cs) <= q + k ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) -> ~ E' (a + i)) -> rw_cells rsegs m2 a cs.
Proof.
  intros K' sp' E' F' L1 A1 m1 md1 L2 A2 m2 md2 q k a cs R Hin Hk NF X Ha Hb D. rewrite <- SEG in X |- *.
  exact (rmid_rw_block Bm API BW K' sp' E' F' L1 A1 m1 md1 L2 A2 m2 md2 q k a cs R Hin Hk NF X Ha Hb D).
Qed.

Lemma c_bblk : forall K' sp' E' F' L1 A1 m1 md1 L2 A2 m2 md2 q k a bs,
  rmid Bm API K' sp' E' F' L1 A1 m1 md1 L2 A2 m2 md2 -> In (q, k) (blocks L1 A1) -> 0 < k -> ~ F' q ->
  bytes_at rsegs m1 a bs -> q <= a -> a + Z.of_nat (length bs) <= q + k ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> ~ E' (a + i)) -> bytes_at rsegs m2 a bs.
Proof.
  intros K' sp' E' F' L1 A1 m1 md1 L2 A2 m2 md2 q k a bs R Hin Hk NF X Ha Hb D. rewrite <- SEG in X |- *.
  exact (rmid_bytes_block Bm API BW K' sp' E' F' L1 A1 m1 md1 L2 A2 m2 md2 q k a bs R Hin Hk NF X Ha Hb D).
Qed.

Lemma c_inblk : forall K' sp' E' F' L1 A1 m1 md1 L2 A2 m2 md2 q k,
  rmid Bm API K' sp' E' F' L1 A1 m1 md1 L2 A2 m2 md2 -> In (q, k) (blocks L1 A1) -> 0 < k -> ~ F' q ->
  ~ E' q -> In (q, k) (blocks L2 A2).
Proof.
  intros K' sp' E' F' L1 A1 m1 md1 L2 A2 m2 md2 q k R Hin Hk NF NE.
  exact (proj1 (rmid_block Bm API BW K' sp' E' F' L1 A1 m1 md1 L2 A2 m2 md2 q k 0 R Hin Hk NF ltac:(lia)
                  ltac:(rewrite Z.add_0_r; exact NE))).
Qed.

Lemma ce_rec_cells : forall L1 A1 m LA (l : hlist) lines k r, list_at Bm L1 A1 m LA l lines ->
  nth_error (hl_recs l) k = Some r ->
  rw_cells rsegs m (hl_v l + 16 * Z.of_nat k) [C8 (Z_to_bv 64 (fst r)); C8 (Z_to_bv 64 (Z.of_nat (length (snd r))))].
Proof.
  intros L1 A1 m LA l lines k r (C & B1 & AR & _) Hk.
  assert (Hkl : (k < length (hl_recs l))%nat) by (apply nth_error_Some; rewrite Hk; discriminate).
  unfold hl_n in B1.
  destruct AR as [(X & _)|(Hc & _ & _ & Hj & [[_ BV] (W0 & W1 & W)])]; [lia|].
  rewrite SEG in BV, W. cbn [cells_bytes cbytes] in BV. rewrite app_nil_r in BV.
  pose proof (hf_rec_bytes rsegs m (hl_v l) (hl_recs l) (hl_junk l) k r BV Hk) as RB.
  cbn [cells_size csize] in W1, W. rewrite Nat.add_0_r, Z2Nat.id in W1, W by lia.
  split; [split; [cbn; tauto | cbn [cells_bytes cbytes]; rewrite app_nil_r; exact RB]|].
  cbn [cells_size csize Nat.add]. split; [lia|]. split; [lia|]. intros i Hi.
  replace (hl_v l + 16 * Z.of_nat k + i) with (hl_v l + (16 * Z.of_nat k + i)) by lia. apply W. lia.
Qed.

Lemma kstep : forall (Ew : Z -> Prop) Wd L1 A1 m1 md1 regs1 pc (Q : machine_state -> Prop) (Pc : config -> Prop),
  rmid Bm API 8352 zSP0 EE FF L A mem md L1 A1 m1 md1 -> ro_agree rsegs m1 ->
  (forall a, Ew a -> EE a) -> (forall a, Ew a -> ~ owned Bm L1 A1 a) ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ outside Wd x -> (zSP0 - 8352 <= x < zSP0) \/ Ew x) ->
  evt rsegs Q (MS (Regs6ss.mkR_of regs1) fp_regs pc fp_csr None (normalize rsegs m1) (PropExec.seg_rom rsegs)) ->
  (forall s0, Q s0 -> exists R pc' m0, s0 = MS R fp_regs pc' fp_csr None m0 (PropExec.seg_rom rsegs) /\
     munch Wd (normalize rsegs m1) m0 /\ wmono rsegs (normalize rsegs m1) m0) ->
  (forall R pc' m0 regs2 m2, Q (MS R fp_regs pc' fp_csr None m0 (PropExec.seg_rom rsegs)) ->
     (forall r, YK11.getr regs2 r = YK11.getr R r) -> mem_rel rsegs m2 m0 ->
     rmid Bm API 8352 zSP0 EE FF L A mem md L1 A1 m2 md1 ->
     rmid Bm API 8352 zSP0 Ew (fun _ => False) L1 A1 m1 md1 L1 A1 m2 md1 ->
     ro_agree rsegs m2 -> munch Wd m1 m2 -> wmono rsegs m1 m2 ->
     SR rsegs (mkCfg (YK11.mkst regs2 pc' m2 (PropExec.seg_rom rsegs)) md1) Pc) ->
  SR rsegs (mkCfg (YK11.mkst regs1 pc m1 (PropExec.seg_rom rsegs)) md1) Pc.
Proof.
  intros Ew Wd L1 A1 m1 md1 regs1 pc Q Pc RM RO1 HE HO HW EV HS K.
  pose proof (aa_laws API) as LAWS.
  pose proof cf0 as (_ & HWF0 & _ & _ & _ & HC0 & H630 & _).
  pose proof (@YM05.alloc_ceiling_value rc) as ACV.
  pose proof RM as (HM1 & HWF1 & HBD1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & SC1).
  destruct (mr_model _ _ LAWS _ _ _ _ HM1) as (Hh & Hl & _).
  eapply (kseg regs1 pc m1 md1 Q Pc); [vm_compute; reflexivity | exact RO1 | exact Hh | exact Hl | exact EV | |].
  { intros s0 X. destruct (HS s0 X) as (R & pc' & m0 & E & _). exists R, pc', m0. exact E. }
  intros R pc' m0 regs2 m2 HQ GR MREL ROS.
  destruct (HS _ HQ) as (R' & pc'' & m0' & EQ & MU & WM). injection EQ as E1 E2 E3. subst R' pc'' m0'.
  destruct (rmid_norm Bm API 8352 zSP0 Ew (fun _ => False) L1 A1 m1 md1 m0 m2 Wd SEG RO1 MREL ROS MU WM HM1 HWF1
              HBD1 ltac:(lia) SC1 HW) as (RMs & MU2 & WM2).
  { intros a Ho. destruct (ce_out_dec Wd a) as [O|O]; [exact O|]. exfalso.
    pose proof (mr_owned_low _ _ LAWS _ _ _ _ a HM1 Ho) as Ra.
    destruct (HW a ltac:(lia) O) as [X|X]; [lia | exact (HO a X Ho)]. }
  { intros p n i Hp Hi O.
    assert (IB : In (ptr_addr L1 p, n) (blocks L1 A1))
      by (unfold blocks; exact (in_map (fun b => (ptr_addr L1 (fst b), snd b)) _ (p, n) Hp)).
    destruct (block_facts Bm (aa_MR API) LAWS L1 A1 m1 md1 _ n i HM1 IB Hi) as (_ & B1 & B2 & _).
    pose proof (hf_blk_img Bm API AX L1 A1 m1 md1 _ n i HM1 IB Hi) as NI.
    pose proof (BW L1 A1 m1 md1 _ n i HM1 IB Hi) as Wr. rewrite SEG in Wr.
    assert (NE : normalize rsegs m1 (Z_to_bv 64 (ptr_addr L1 p + i)) = m1 (Z_to_bv 64 (ptr_addr L1 p + i)))
      by (unfold normalize; rewrite (ro_addr_out Bm SEG (ptr_addr L1 p + i) ltac:(lia) NI); reflexivity).
    assert (Wn : writable_at rsegs (normalize rsegs m1) (ptr_addr L1 p + i))
      by (unfold writable_at, wview in *; rewrite NE; exact Wr).
    pose proof (WM _ Wn) as W0.
    apply (present_of_writable_out Bm SEG m2 (ptr_addr L1 p + i) ltac:(lia) NI).
    exact (writable_at_rel rsegs m2 m0 _ MREL W0). }
  apply (K R pc' m0 regs2 m2 HQ GR MREL); [| exact RMs | exact (ro_agree_same rsegs m1 m2 RO1 ROS) | exact MU2
                                            | exact WM2].
  apply (rmid_EF Bm API _ _ _ _ _ _ _ _ _ _ _ _ _ _ (rmid_seq Bm API _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HWF0 RM RMs)).
  - intros a [X|X]; [exact X | exact (HE a X)].
  - intros q [X|[]]; exact X.
Qed.

Lemma dstep : forall L1 A1 m1 md1 Hc ds c regs1 (i : nat) rr (Pc : config -> Prop),
  ceJ L1 A1 m1 md1 Hc ds c -> nth_error (hl_recs Hc) i = Some rr ->
  YK11.getr regs1 10 = Z_to_bv 64 (zHA + 80) -> YK11.getr regs1 11 = Z_to_bv 64 (Z.of_nat i) ->
  spZ regs1 = zSP1 -> YK0s.ret_ok (YK11.getr regs1 1) -> YK11.getr regs1 4 = Z_to_bv 64 (ms_tp Bm) ->
  (forall L2 A2 regs2 m2 md2 (l' : hlist),
     rmid Bm API 8352 zSP0 EE FF L A mem md L2 A2 m2 md2 ->
     rmid Bm API LIST_DROP_K zSP1
       (fun a => zHA + 80 + 8 <= a < zHA + 80 + 12 \/ zV + 16 * Z.of_nat i <= a < zV + 16 * (hl_n Hc - 1))
       (fun q => q = fst rr) L1 A1 m1 md1 L2 A2 m2 md2 ->
     regs_preserved regs1 regs2 -> st_init_done A2 = true -> ro_agree rsegs m2 ->
     rt_ok RF A2 (rt_free RF (runF RF [] bnd (recs_drop_tr (map (shr (known_at L A)) ds)))
       (Z.of_nat (length (snd rr)) + 1) (sptr_of L A (fst rr))) ->
     list_at Bm L2 A2 m2 (zHA + 80) l' true -> hl_v l' = zV -> hl_cap l' = zCAP ->
     hl_recs l' = firstn i (hl_recs Hc) ++ skipn (S i) (hl_recs Hc) ->
     (exists b1 b2, blocks L1 A1 = b1 ++ (fst rr, text_len rr) :: b2 /\ blocks L2 A2 = b1 ++ b2) ->
     SR rsegs (mkCfg (YK11.mkst regs2 (YK11.getr regs1 1) m2 (PropExec.seg_rom rsegs)) md2) Pc) ->
  SR rsegs (mkCfg (YK11.mkst regs1 (Z_to_bv 64 0x14d58) m1 (PropExec.seg_rom rsegs)) md1) Pc.
Proof.
  intros L1 A1 m1 md1 Hc ds c regs1 i rr Pc J Hrr R10' R11' SP' RA' TP' K.
  pose proof J as (RM & INI & RO1 & (RES1 & BU1) & LH1 & HV1 & HC1 & _ & SUB1 & _).
  pose proof cf0 as (_ & HWF0 & _ & _ & HAL0 & HC0 & H630 & _).
  pose proof (@YM05.alloc_ceiling_value rc) as ACV.
  pose proof cfV as (_ & _ & _ & _ & _ & _ & VB & _).
  pose proof RM as (HM1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SC1).
  pose proof (bv_unsigned_in_range 64 (reg_get regs 2)) as RSP. change (bv_modulus 64) with (2 ^ 64) in RSP.
  assert (HAr : 203040 <= zHA <= 203328) by (unfold G_S, SRC_SIZE; lia).
  assert (EKD : LIST_DROP_K = 8240) by reflexivity.
  assert (Hil : (i < length (hl_recs Hc))%nat) by (apply nth_error_Some; rewrite Hrr; discriminate).
  assert (HiN : Z.of_nat i < hl_n Hc) by (unfold hl_n; lia).
  pose proof LH1 as (_ & HNC1 & _). rewrite HC1 in HNC1.
  assert (Rin : In rr RS0) by exact (SUB1 rr (nth_error_In _ _ Hrr)).
  assert (Enth : nth i (hl_recs Hc) (0, []) = rr) by (apply nth_error_nth; exact Hrr).
  assert (R10p : PropExec.getr regs1 10 = Z_to_bv 64 (zHA + 80)) by exact R10'.
  assert (R11p : PropExec.getr regs1 11 = Z_to_bv 64 (Z.of_nat i)) by exact R11'.
  assert (ULA : bv_unsigned (Z_to_bv 64 (zHA + 80)) = zHA + 80) by (apply unsigned_lit; lia).
  assert (UI : bv_unsigned (Z_to_bv 64 (Z.of_nat i)) = Z.of_nat i) by (apply unsigned_lit; lia).
  assert (EV : forall a, zV + 16 * Z.of_nat i <= a < zV + 16 * (hl_n Hc - 1) ->
             0 < zCAP /\ zV <= a < zV + 16 * zCAP /\ a < alloc_ceiling).
  { intros a Ha. assert (CP : 0 < zCAP) by lia. destruct (VB CP) as (_ & _ & _ & VCe & _). lia. }
  pose proof LDC as LDc. unfold list_drop_contract in LDc. rewrite SEG in LDc.
  eapply SR_bind.
  { apply (LDc L1 A1 regs1 m1 md1 (runF RF [] bnd (recs_drop_tr (map (shr (known_at L A)) ds))) Hc true).
    - reflexivity.
    - change (call_pre_k Bm (aa_MR API) LIST_DROP_K L1 A1 regs1 m1 md1).
      eapply cpk_of_rmid; [exact RM | exact INI | exact RA' | exact TP' | rewrite SP'; Z.div_mod_to_equations; lia
                           | rewrite SP', EKD; lia | rewrite SP'; lia | rewrite EKD; lia
                           | rewrite SP', EKD; lia | rewrite SP'; lia].
    - exact INI.
    - exact RO1.
    - rewrite R10p, ULA. intros a Ha. split.
      + apply hPLR. unfold G_GONE, G_S, SRC_SIZE, SOURCES_MAX in *. lia.
      + apply hf_ro_glob. unfold G_S, SRC_SIZE in *. lia.
    - rewrite R10p, ULA. unfold G_S, SRC_SIZE. Z.div_mod_to_equations. lia.
    - rewrite R10p, ULA. exact LH1.
    - rewrite R11p, UI. exact HiN.
    - exact RES1. }
  intros c' (L2 & A2 & regs2 & m2 & md2 & l' & -> & RP & INI2 & (qs & QL & RES2 & _) & RO2 & LH2 & HV2 & HC2 & HR2 & _
    & BL).
  rewrite R10p, ULA in RP, LH2.
  rewrite R11p, UI, Nat2Z.id in RP, RES2, HR2, BL.
  rewrite Enth in RP, BL.
  rewrite nret_list_drop in QL. destruct qs as [|q0 qs]; [|discriminate QL].
  pose proof (BU1 rr (nth_error_In _ _ Hrr)) as (UB1 & PB1).
  assert (SPE : sptr_of L1 A1 (fst rr) = sptr_of L A (fst rr)).
  { rewrite <- PB1 at 1. exact (sptr_of_eq L1 A1 _ _ (BND L1 A1 m1 md1 HM1) UB1). }
  assert (EN : nth i (sh_recs (sh_of (known_at L1 A1) Hc)) (Known pdefT, @nil Z) = shr (known_at L1 A1) rr)
    by (apply nth_error_nth; cbn [sh_of sh_recs]; rewrite nth_error_map, Hrr; reflexivity).
  unfold list_drop_tr in RES2. rewrite EN in RES2. unfold shr, rec_drop_tr, rec_len, known_at in RES2.
  cbn [fst snd] in RES2. rewrite SPE in RES2. unfold bzs in RES2. rewrite length_map in RES2.
  destruct (rp_split Bm API _ _ _ _ _ _ _ _ _ _ _ _ _ RP) as (RMi & PR).
  rewrite SP', HV1 in RMi. rewrite HV1 in HV2. rewrite HC1 in HC2.
  assert (WR1 : forall a, zSP0 - 8352 <= a < zSP0 -> writable_at (ms_segs Bm) m1 a)
    by (intros a Ha; apply SC1; unfold sk; left; exact Ha).
  assert (NE1 : forall a, zSP0 - 8352 <= a < zSP0 ->
            ~ (zHA + 80 + 8 <= a < zHA + 80 + 12 \/ zV + 16 * Z.of_nat i <= a < zV + 16 * (hl_n Hc - 1))).
  { intros a Ha [X|X]; [lia | pose proof (EV a X); lia]. }
  pose proof (rmid_widen Bm API LIST_DROP_K zSP1 8352 zSP0 _ _ _ _ _ _ _ _ _ _ HM1 ltac:(rewrite EKD; lia)
                ltac:(lia) ltac:(lia) ltac:(lia) WR1 NE1 RMi) as RMw.
  assert (RMo : rmid Bm API 8352 zSP0 EE FF L A mem md L2 A2 m2 md2).
  { apply (rmid_EF Bm API _ _ _ _ _ _ _ _ _ _ _ _ _ _ (rmid_seq Bm API _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HWF0 RM RMw)).
    - intros a [X|[X|X]]; [exact X | cbv beta; left; lia |].
      cbv beta. right. right. destruct (EV a X) as (E1 & E2 & _). split; [exact E1 | exact E2].
    - intros x [X|X]; [exact X|]. cbv beta. rewrite X. apply in_map. exact Rin. }
  exact (K L2 A2 regs2 m2 md2 l' RMo RMi PR INI2 RO2 RES2 LH2 HV2 HC2 HR2 BL).
Qed.

Lemma v_blk : forall L1 A1 ds, ce_br L1 A1 ds -> (forall r, In r ds -> In r RS0) -> 0 < zCAP ->
  In (zV, 16 * zCAP) (blocks L1 A1).
Proof.
  intros L1 A1 ds (BRa & _) SUBD HC. pose proof cfV as (_ & _ & _ & _ & VNR & _ & VB & _).
  apply (BRa _ _ (proj1 (VB HC))). intros X. apply in_map_iff in X as (r & Er & Hr).
  apply VNR. rewrite <- Er. apply in_map. exact (SUBD r Hr).
Qed.

Lemma out_blk : forall L1 A1 ds, ce_br L1 A1 ds -> (forall r, In r ds -> In r RS0) -> ob <> [] ->
  exists CO, zNO <= CO /\ In (zOUT, CO) (blocks L1 A1) /\ fresh_block Bm zOUT CO /\ ~ In zOUT (hs_blocks h).
Proof.
  intros L1 A1 ds (BRa & _) SUBD OBN. pose proof cfV as (_ & _ & _ & _ & _ & _ & _ & RB).
  destruct hOK as [X|(CO & H1 & H2 & H3 & H4)]; [contradiction|].
  exists CO. split; [exact H1|]. split; [|split; [exact H3 | exact H4]].
  apply (BRa _ _ H2). intros X. apply in_map_iff in X as (r & Er & Hr). apply H4. rewrite <- Er.
  exact (RB r (SUBD r Hr)).
Qed.

Lemma br_free : forall L1 A1 L2 A2 m1 md1 ds q k r b1 b2,
  aa_MR API L1 A1 m1 md1 -> ce_br L1 A1 ds -> fst r = q ->
  blocks L1 A1 = b1 ++ (q, k) :: b2 -> blocks L2 A2 = b1 ++ b2 -> ce_br L2 A2 (ds ++ [r]).
Proof.
  intros L1 A1 L2 A2 m1 md1 ds q k r b1 b2 HM (BRa & BRb) Er BL1 BL2.
  pose proof (BND L1 A1 m1 md1 HM) as ND. apply hf_nodup in ND. rewrite BL1, map_app in ND. cbn [map fst] in ND.
  apply NoDup_remove_2 in ND. rewrite <- map_app in ND.
  split.
  - intros q' k' Hq Hn. rewrite map_app, in_app_iff in Hn. cbn [map In] in Hn.
    pose proof (BRa q' k' Hq (fun X => Hn (or_introl X))) as X. rewrite BL1 in X. rewrite BL2.
    apply in_app_iff in X as [X|[X|X]]; [apply in_or_app; left; exact X | | apply in_or_app; right; exact X].
    injection X as E1 E2. exfalso. apply Hn. right. left. rewrite Er. exact E1.
  - intros q' k' Hq. rewrite BL2 in Hq.
    assert (Hq1 : In (q', k') (blocks L1 A1)).
    { rewrite BL1. apply in_app_iff in Hq as [X|X]; apply in_or_app; [left; exact X | right; right; exact X]. }
    destruct (BRb q' k' Hq1) as (Y1 & Y2). split; [exact Y1|].
    rewrite map_app, in_app_iff. cbn [map In]. intros [Z|[Z|[]]]; [exact (Y2 Z)|].
    apply ND. rewrite <- Er, Z. exact (in_map fst _ (q', k') Hq).
Qed.

Lemma mf_rmid : forall K' sp' E' F' L1 A1 m1 md1 L2 A2 m2 md2 ds,
  rmid Bm API K' sp' E' F' L1 A1 m1 md1 L2 A2 m2 md2 -> aa_MR API L1 A1 m1 md1 ->
  alloc_ceiling <= sp' - K' -> sp' <= zSP0 -> 0 <= K' ->
  ro_agree rsegs m1 -> ro_agree rsegs m2 ->
  (forall a, E' a -> EE a) -> (ob <> [] -> ~ F' zOUT) ->
  ce_br L1 A1 ds -> (forall r, In r ds -> In r RS0) ->
  ce_mf m1 -> ce_mf m2.
Proof.
  intros K' sp' E' F' L1 A1 m1 md1 L2 A2 m2 md2 ds R HM1 HK Hsp HK0 RO1 RO2 HE HF BR SUBD (P1 & G1 & N1 & O1 & B1).
  pose proof cf0 as (_ & _ & _ & _ & _ & HC0 & H630 & _).
  pose proof (@YM05.alloc_ceiling_value rc) as ACV.
  pose proof cfV as (_ & NDB & V0 & HNC & VNR & NDR & VB & RB).
  assert (HAr : 203040 <= zHA <= 203328) by (unfold G_S, SRC_SIZE; lia).
  assert (PLG : forall a, G_GONE <= a < G_S -> img_plain Bm a /\ ~ E' a).
  { intros a Ha. assert (IP : img_plain Bm a) by (apply hPLR; unfold G_GONE, G_S, SRC_SIZE, SOURCES_MAX in *; lia).
    split; [exact IP|]. intros X. apply HE in X. cbv beta in X. destruct X as [X|[X|(HC & X)]].
    - unfold G_S, SRC_SIZE, G_GONE in *. lia.
    - unfold G_S, G_GONE in *. lia.
    - destruct (VB HC) as (_ & (_ & _ & Hf) & _). apply (Hf (a - zV) ltac:(lia)).
      replace (zV + (a - zV)) with a by lia. exact (proj1 IP). }
  split; [|split; [|split; [|split]]].
  - destruct hPD as [(PS1 & PS2)|(PR0 & PR1 & PR2)].
    + apply (c_bhi K' sp' E' F' L1 A1 m1 md1 L2 A2 m2 md2 _ _ ltac:(lia) HM1 R P1 ltac:(lia)).
      intros i Hi X. rewrite length_app in Hi. cbn [length] in Hi. apply HE in X. cbv beta in X.
      destruct X as [X|[X|(HC & X)]]; [unfold G_S, SRC_SIZE in *; lia | lia |].
      destruct (VB HC) as (_ & _ & _ & V2 & _). lia.
    + apply (bytes_at_transfer rsegs m1); [exact P1|]. intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
      assert (E1 : ro_addr rsegs (Z_to_bv 64 (zPF + i)) = true) by (apply PR2; lia).
      rewrite (mbyte_ro_agree rsegs m2 _ RO2 E1), (mbyte_ro_agree rsegs m1 _ RO1 E1). reflexivity.
  - apply (c_bimg K' sp' E' F' L1 A1 m1 md1 L2 A2 m2 md2 _ _ HK HM1 R G1).
    intros i Hi. cbn [length] in Hi. apply PLG. unfold G_GONE, G_S. lia.
  - apply (c_bimg K' sp' E' F' L1 A1 m1 md1 L2 A2 m2 md2 _ _ HK HM1 R N1).
    intros i Hi. rewrite length_le8 in Hi. apply PLG. unfold G_GONE, G_NOUT, G_S. lia.
  - apply (c_bimg K' sp' E' F' L1 A1 m1 md1 L2 A2 m2 md2 _ _ HK HM1 R O1).
    intros i Hi. rewrite length_le8 in Hi. apply PLG. unfold G_GONE, G_OUT, G_S. lia.
  - destruct (list_eq_dec (bv_eq_dec 8) ob []) as [OE|ON].
    + rewrite OE in B1 |- *. destruct B1 as (B10 & B11 & _). split; [lia|]. split; [cbn [length] in *; lia|].
      intros i Hi. cbn [length] in Hi. lia.
    + destruct (out_blk L1 A1 ds BR SUBD ON) as (CO & HCO & OIn & OFr & OHB).
      pose proof OFr as (Fq1 & Fq2 & Fq3).
      assert (LP : (0 < length ob)%nat)
        by (destruct (length ob) eqn:EL; [apply length_zero_iff_nil in EL; contradiction | lia]).
      assert (CO0 : 0 < CO) by lia.
      apply (c_bblk K' sp' E' F' L1 A1 m1 md1 L2 A2 m2 md2 zOUT CO zOUT ob R OIn CO0 (HF ON) B1 ltac:(lia) ltac:(lia)).
      intros i Hi X. apply HE in X. cbv beta in X. destruct X as [X|[X|(HC & X)]].
      * apply (Fq3 i ltac:(lia)).
        exact (proj1 (hPLR (zOUT + i) ltac:(unfold G_GONE, G_S, SRC_SIZE, SOURCES_MAX in *; lia))).
      * lia.
      * destruct (VB HC) as (_ & _ & _ & _ & _ & VHB).
        assert (NE : zV <> zOUT) by (intros Eq; apply OHB; rewrite <- Eq; exact VHB).
        pose proof (v_blk L1 A1 ds BR SUBD HC) as VIn1.
        destruct (blocks_disjoint Bm API L1 A1 m1 md1 zV (16 * zCAP) zOUT CO HM1 VIn1 OIn NE); lia.
Qed.

Lemma ce_src_rest : forall L1 A1 m1 md1, rmid Bm API 8352 zSP0 EE FF L A mem md L1 A1 m1 md1 ->
  src_base Bm L1 A1 m1 zHA h /\ list_at Bm L1 A1 m1 (zHA + 64) (hs_expected h) true.
Proof.
  intros L1 A1 m1 md1 R.
  pose proof cf0 as (HM & _ & _ & _ & _ & HC0 & H630 & _).
  pose proof (@YM05.alloc_ceiling_value rc) as ACV.
  pose proof cfV as (LH & _ & V0 & HNC & VNR & NDR & VB & RB).
  pose proof hSRC as S. apply src_at_iff in S. destruct S as (SB & LE & _ & ND).
  apply hf_nodup in ND. unfold hs_blocks in ND.
  assert (HAr : 203040 <= zHA <= 203328) by (unfold G_S, SRC_SIZE; lia).
  assert (OUTB : forall q, In q (list_blocks (hs_pending h) ++ [hs_partial h] ++ list_blocks (hs_expected h)) ->
                ~ In q (list_blocks (hs_held h))).
  { intros q Hq Hh.
    apply (hf_nodup_disj (list_blocks (hs_pending h) ++ [hs_partial h] ++ list_blocks (hs_expected h))
             (list_blocks (hs_held h)) q); [rewrite <- !app_assoc; exact ND | exact Hq | exact Hh]. }
  assert (KQ : forall q, In q (list_blocks (hs_pending h) ++ [hs_partial h] ++ list_blocks (hs_expected h)) ->
               kept_block EE FF L A q).
  { intros q Hq. split.
    - intros X. apply (OUTB q Hq). unfold list_blocks. apply in_or_app. right. exact X.
    - intros k i Hin Hi X. cbv beta in X.
      pose proof (hf_blk_img Bm API AX L A mem md q k i HM Hin Hi) as NI.
      destruct (block_facts Bm (aa_MR API) (aa_laws API) L A mem md q k i HM Hin Hi) as (_ & B1 & B2 & _).
      destruct X as [X|[X|(HC & X)]].
      + apply NI. exact (proj1 (hPLR (q + i) ltac:(unfold G_GONE, G_S, SRC_SIZE, SOURCES_MAX in *; lia))).
      + lia.
      + destruct (VB HC) as (HVb & _ & _ & _ & _ & HVh). destruct (Z.eq_dec q zV) as [E|E].
        * subst q. apply (OUTB _ Hq). exact (proj2 (hf_list_v Bm L A mem _ _ true LH HC)).
        * destruct (blocks_disjoint Bm API L A mem md zV (16 * zCAP) q k HM HVb Hin (fun e => E (eq_sym e))); lia. }
  assert (NE : forall i, 0 <= i < 80 -> img_plain Bm (zHA + i) /\ ~ EE (zHA + i)).
  { intros i Hi. assert (IP : img_plain Bm (zHA + i))
      by (apply hPLR; unfold G_GONE, G_S, SRC_SIZE, SOURCES_MAX in *; lia).
    split; [exact IP|]. intros [X|[X|(HC & X)]]; [lia | lia |].
    destruct (VB HC) as (HVb & _).
    apply (hf_blk_img Bm API AX L A mem md zV (16 * zCAP) (zHA + i - zV) HM HVb ltac:(lia)).
    replace (zV + (zHA + i - zV)) with (zHA + i) by lia. exact (proj1 IP). }
  split.
  - eapply (src_base_rmid Bm API AX BW 8352 zSP0); [exact SEG | lia | exact HM | exact R | exact SB | |].
    + intros i Hi. apply NE. lia.
    + intros q [Hq|Hq]; apply KQ; [apply in_or_app; left; exact Hq|].
      subst q. apply in_app_iff. right. apply in_app_iff. left. left. reflexivity.
  - eapply (list_at_rmid Bm API AX BW 8352 zSP0); [exact SEG | lia | exact HM | exact R | exact LE | |].
    + intros i Hi. replace (zHA + 64 + i) with (zHA + (64 + i)) by lia. apply NE. lia.
    + intros q Hq. apply KQ. apply in_app_iff. right. apply in_app_iff. right. exact Hq.
Qed.

Lemma ce_src_fin : forall L1 A1 m1 md1 Hc, rmid Bm API 8352 zSP0 EE FF L A mem md L1 A1 m1 md1 ->
  list_at Bm L1 A1 m1 (zHA + 80) Hc true -> hl_v Hc = zV -> hl_cap Hc = zCAP ->
  (forall r, In r (hl_recs Hc) -> In r RS0) -> src_at Bm L1 A1 m1 zHA (set_held h Hc).
Proof.
  intros L1 A1 m1 md1 Hc R LH1 HV1 HC1 SUB1.
  destruct (ce_src_rest L1 A1 m1 md1 R) as (SB1 & LE1).
  pose proof hSRC as S. apply src_at_iff in S. destruct S as (_ & _ & _ & ND).
  apply (src_at_set_held Bm L1 A1 m1 zHA h Hc SB1 LE1 LH1); [|exact ND].
  intros q Hq X. apply (src_out h ND q Hq). unfold list_blocks in X |- *. rewrite HV1, HC1 in X.
  apply in_app_iff in X as [X|X]; apply in_or_app; [left; exact X | right].
  apply in_map_iff in X as (r & <- & Hr). apply in_map. exact (SUB1 r Hr).
Qed.

Lemma fin_ret : forall L1 A1 regs1 m1 md1 Hc ds c,
  ceJ L1 A1 m1 md1 Hc ds c -> regs_preserved regs regs1 -> ceRES Hc ds c ->
  cePOST (mkCfg (YK11.mkst regs1 (reg_get regs 1) m1 (PropExec.seg_rom rsegs)) md1).
Proof.
  intros L1 A1 regs1 m1 md1 Hc ds c JJ PR REL.
  destruct JJ as (RM & INI & RO1 & RES1 & LH1 & HV1 & HC1 & ND1 & SUB1 & SUBD & LEN1 & ATC1 & MF1 & BR1).
  destruct MF1 as (P1 & G1 & N1 & O1 & B1).
  pose proof (ce_src_fin L1 A1 m1 md1 Hc RM LH1 HV1 HC1 SUB1) as SRC1.
  destruct BR1 as (BRa & BRb).
  destruct REL as [(G & ER1 & ED & Ec)|(G & ER1)].
  - subst c. exists L1, A1, regs1, m1, md1, Hc, (filter (fun r => prefixb P (snd r)) RS0), 0.
    split; [reflexivity|].
    split; [apply rp_join; [exact RM | exact PR]|].
    split; [exact INI|].
    split; [exists []; split; [rewrite nret_cse; reflexivity|];
            unfold check_shape_ends_tr; rewrite (proj2 (Z.eqb_neq gone 0) G), <- ED; exact (proj1 RES1)|].
    split; [exact RO1|]. split; [exact SRC1|]. split; [exact HV1|]. split; [exact HC1|]. split; [exact ND1|].
    split; [left; split; [exact G|]; split; [exact ER1|]; split; reflexivity|].
    split; [exact ATC1|]. split; [exact P1|]. split; [exact G1|]. split; [exact N1|]. split; [exact O1|].
    split; [exact B1|].
    split.
    + intros q k Hq Hn. apply (BRa q k Hq). rewrite ED, map_rev, ce_in_rev. exact Hn.
    + intros q k Hq. destruct (BRb q k Hq) as (X & Y). split; [exact X|]. rewrite ED, map_rev, ce_in_rev in Y. exact Y.
  - exists L1, A1, regs1, m1, md1, Hc, ds, c.
    split; [reflexivity|].
    split; [apply rp_join; [exact RM | exact PR]|].
    split; [exact INI|].
    split; [exists []; split; [rewrite nret_cse; reflexivity|];
            unfold check_shape_ends_tr; rewrite G, Z.eqb_refl, ER1; exact (proj1 RES1)|].
    split; [exact RO1|]. split; [exact SRC1|]. split; [exact HV1|]. split; [exact HC1|]. split; [exact ND1|].
    split; [right; split; [exact G | exact ER1]|].
    split; [exact ATC1|]. split; [exact P1|]. split; [exact G1|]. split; [exact N1|]. split; [exact O1|].
    split; [exact B1|].
    split; [exact BRa | exact BRb].
Qed.

Lemma ceJ_step : forall L1 A1 m1 md1 m2 Hc ds c,
  ceJ L1 A1 m1 md1 Hc ds c -> rmid Bm API 8352 zSP0 EE FF L A mem md L1 A1 m2 md1 ->
  rmid Bm API 8352 zSP0 (fun _ => False) (fun _ => False) L1 A1 m1 md1 L1 A1 m2 md1 -> ro_agree rsegs m2 ->
  ceJ L1 A1 m2 md1 Hc ds c.
Proof.
  intros L1 A1 m1 md1 m2 Hc ds c (RM & INI & RO1 & RES1 & LH1 & HV1 & HC1 & ND1 & SUB1 & SUBD & LEN1 & ATC1 & MF1 & BR1)
    RMa RMs RO2.
  pose proof cf0 as (_ & _ & _ & _ & _ & HC0 & H630 & _).
  pose proof (@YM05.alloc_ceiling_value rc) as ACV.
  pose proof RM as (HM1 & _).
  pose proof (bv_unsigned_in_range 64 (reg_get regs 12)) as RAT. change (bv_modulus 64) with (2 ^ 64) in RAT.
  assert (HAr : 203040 <= zHA <= 203328) by (unfold G_S, SRC_SIZE; lia).
  split; [exact RMa|]. split; [exact INI|]. split; [exact RO2|]. split; [exact RES1|].
  split.
  { eapply (list_at_rmid Bm API AX BW 8352 zSP0); [exact SEG | lia | exact HM1 | exact RMs | exact LH1 | |].
    - intros k Hk. split; [apply hPLR; unfold G_GONE, G_S, SRC_SIZE, SOURCES_MAX in *; lia | intros []].
    - intros q _. split; [intros [] | intros k0 i0 _ _ []]. }
  split; [exact HV1|]. split; [exact HC1|]. split; [exact ND1|]. split; [exact SUB1|]. split; [exact SUBD|].
  split; [exact LEN1|].
  split.
  { apply (c_hi _ _ _ _ L1 A1 m1 md1 L1 A1 m2 md1 _ _ RMs HM1 ltac:(lia) ATC1 ltac:(lia)
             ltac:(cbn [cells_size csize Nat.add]; lia)). intros i _ []. }
  split; [|exact BR1].
  exact (mf_rmid _ _ _ _ L1 A1 m1 md1 L1 A1 m2 md1 ds RMs HM1 ltac:(lia) ltac:(lia) ltac:(lia) RO1 RO2
           (fun a X => False_ind _ X) (fun _ X => X) BR1 SUBD MF1).
Qed.

Lemma epi : forall L1 A1 R1 m1 md1 Hc ds c,
  ceJ L1 A1 m1 md1 Hc ds c -> ce_frm m1 ->
  reg_get R1 2 = Z_to_bv 64 zSP1 -> reg_get R1 3 = reg_get regs 3 -> reg_get R1 4 = reg_get regs 4 ->
  reg_get R1 26 = reg_get regs 26 -> reg_get R1 27 = reg_get regs 27 -> ceRES Hc ds c ->
  SR rsegs (mkCfg (YK11.mkst R1 (Z_to_bv 64 0x14ba0) m1 (PropExec.seg_rom rsegs)) md1) cePOST.
Proof.
  intros L1 A1 R1 m1 md1 Hc ds c J (jj & FR) E2 E3 E4 E26 E27 REL.
  pose proof J as (RM & INI & RO1 & _).
  pose proof cf0 as (HM0 & HWF0 & HBD0 & HRA0 & HAL0 & HC0 & H630 & _).
  pose proof (@YM05.alloc_ceiling_value rc) as ACV.
  pose proof (bv_unsigned_in_range 64 (reg_get regs 2)) as RSP. change (bv_modulus 64) with (2 ^ 64) in RSP.
  assert (FR' : rw_cells rsegs m1 zSP1 (ce_frame (reg_get regs 1) (reg_get regs 8) (reg_get regs 9) (reg_get regs 18)
      (reg_get regs 19) (reg_get regs 20) (reg_get regs 21) (reg_get regs 22) (reg_get regs 23) (reg_get regs 24)
      (reg_get regs 25) jj)) by exact FR.
  eapply (kstep (fun _ => False) [] L1 A1 m1 md1 R1 (Z_to_bv 64 0x14ba0)).
  - exact RM.
  - exact RO1.
  - intros a [].
  - intros a [].
  - intros x _ O. exfalso. exact (O I).
  - unfold Regs6ss.mkR_of. rewrite E2, E3, E4, E26, E27.
    eapply ce_epi with (B := zSP1); [reflexivity | lia | lia |].
    apply (rw_cells_normalize rsegs m1 _ _ RO1 FR'). intros i Hi.
    unfold ce_frame in Hi. cbn [cells_size csize Nat.add] in Hi. apply ro_addr_hi. lia.
  - intros s0 ->. do 3 eexists. split; [reflexivity|]. split; [apply munch_refl | apply wmono_refl].
  - intros R pc' m0 regs2 m2 HQ GR MREL RMa RMs RO2 MU2 WM2.
    injection HQ as ER EP EM. subst R pc' m0.
    apply SR_ret.
    replace (ret_pc (reg_get regs 1)) with (reg_get regs 1) by (symmetry; exact (ret_pc_of_ok _ HRA0)).
    apply (fin_ret L1 A1 regs2 m2 md1 Hc ds c); [exact (ceJ_step L1 A1 m1 md1 m2 Hc ds c J RMa RMs RO2) | | exact REL].
    intros r Hr. rewrite GR. unfold callee_saved in Hr.
    assert (Rc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                 r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    destruct Rc as [->|Rc].
    + transitivity (Z_to_bv 64 (zSP1 + 112)); [reflexivity|].
      replace (zSP1 + 112) with zSP0 by lia. rewrite Z_to_bv_bv_unsigned. reflexivity.
    + repeat (destruct Rc as [Rc|Rc]; [subst r; reflexivity|]); subst r; reflexivity.
Qed.

Lemma ce_run_snoc : forall (b : rt_R RF) (ds : list (Z * list byte)) (rr : Z * list byte),
  runF RF [] b (recs_drop_tr (map (shr (known_at L A)) (ds ++ [rr]))) =
  rt_free RF (runF RF [] b (recs_drop_tr (map (shr (known_at L A)) ds))) (Z.of_nat (length (snd rr)) + 1)
    (sptr_of L A (fst rr)).
Proof.
  intros b ds rr.
  transitivity (rt_free RF (runF RF [] b (recs_drop_tr (map (shr (known_at L A)) ds)))
    (Z.of_nat (length (bzs (snd rr))) + 1) (sptr_of L A (fst rr))).
  - unfold runF, run_tr, recs_drop_tr. rewrite !map_app, concat_app, run_from_app. reflexivity.
  - unfold bzs. rewrite length_map. reflexivity.
Qed.

Lemma bu_drop : forall K' sp' E' L1 A1 m1 md1 L2 A2 m2 md2 Hc i rr,
  ce_bu L1 A1 (hl_recs Hc) ->
  rmid Bm API K' sp' E' (fun x => x = fst rr) L1 A1 m1 md1 L2 A2 m2 md2 ->
  list_at Bm L1 A1 m1 (zHA + 80) Hc true -> nth_error (hl_recs Hc) i = Some rr ->
  ce_bu L2 A2 (firstn i (hl_recs Hc) ++ skipn (S i) (hl_recs Hc)).
Proof.
  intros K' sp' E' L1 A1 m1 md1 L2 A2 m2 md2 Hc i rr BU RMi LH Hrr r Hr.
  pose proof LH as (_ & _ & _ & HND & _).
  assert (Hil : (i < length (hl_recs Hc))%nat) by (apply nth_error_Some; rewrite Hrr; discriminate).
  pose proof (ce_drop_ne (hl_recs Hc) i r (proj1 (hf_nodup _) HND) Hil Hr) as NE.
  assert (E1 : nth i (hl_recs Hc) (0, []) = rr) by (apply nth_error_nth; exact Hrr). rewrite E1 in NE.
  destruct (BU r (hf_in_drop _ i r Hr)) as (U1 & P1).
  pose proof RMi as (_ & _ & _ & _ & _ & R6 & R7 & _).
  assert (NF : ptr_addr L1 (sptr_of L A (fst r)) <> fst rr) by (rewrite P1; exact NE).
  assert (U3 : In (sptr_of L A (fst r), Z.of_nat (length (snd r)) + 1) (user_blocks A2))
    by (apply (R7 _ _ U1); [lia | exact NF]).
  split; [exact U3|]. rewrite (R6 _ _ U1 U3 NF). exact P1.
Qed.

Lemma post_drop : forall L1 A1 m1 md1 L2 A2 m2 md2 (Hc l' : hlist) ds c (i : nat) rr,
  ceJ L1 A1 m1 md1 Hc ds c -> ce_frm m1 -> nth_error (hl_recs Hc) i = Some rr ->
  rmid Bm API 8352 zSP0 EE FF L A mem md L2 A2 m2 md2 ->
  rmid Bm API LIST_DROP_K zSP1
    (fun a => zHA + 80 + 8 <= a < zHA + 80 + 12 \/ zV + 16 * Z.of_nat i <= a < zV + 16 * (hl_n Hc - 1))
    (fun q => q = fst rr) L1 A1 m1 md1 L2 A2 m2 md2 ->
  st_init_done A2 = true -> ro_agree rsegs m2 ->
  rt_ok RF A2 (rt_free RF (runF RF [] bnd (recs_drop_tr (map (shr (known_at L A)) ds)))
    (Z.of_nat (length (snd rr)) + 1) (sptr_of L A (fst rr))) ->
  list_at Bm L2 A2 m2 (zHA + 80) l' true -> hl_v l' = zV -> hl_cap l' = zCAP ->
  hl_recs l' = firstn i (hl_recs Hc) ++ skipn (S i) (hl_recs Hc) ->
  (exists b1 b2, blocks L1 A1 = b1 ++ (fst rr, text_len rr) :: b2 /\ blocks L2 A2 = b1 ++ b2) ->
  ceJ L2 A2 m2 md2 l' (ds ++ [rr]) c /\ ce_frm m2.
Proof.
  intros L1 A1 m1 md1 L2 A2 m2 md2 Hc l' ds c i rr J (jj & FR1) Hrr RMo RMi INI2 RO2 RES2 LH2 HV2 HC2 HR2
    (b1 & b2 & BL1 & BL2).
  destruct J as (RM & INI & RO1 & (RES1 & BU1) & LH1 & HV1 & HC1 & ND1 & SUB1 & SUBD & LEN1 & ATC1 & MF1 & BR1).
  pose proof cf0 as (_ & _ & _ & _ & _ & HC0 & H630 & _).
  pose proof (@YM05.alloc_ceiling_value rc) as ACV.
  pose proof cfV as (_ & _ & _ & _ & _ & _ & VB & RB).
  pose proof RM as (HM1 & _).
  pose proof (bv_unsigned_in_range 64 (reg_get regs 12)) as RAT. change (bv_modulus 64) with (2 ^ 64) in RAT.
  pose proof (bv_unsigned_in_range 64 (reg_get regs 2)) as RSP. change (bv_modulus 64) with (2 ^ 64) in RSP.
  assert (HAr : 203040 <= zHA <= 203328) by (unfold G_S, SRC_SIZE; lia).
  assert (EKD : LIST_DROP_K = 8240) by reflexivity.
  assert (KK : alloc_ceiling <= zSP1 - LIST_DROP_K) by (rewrite EKD; lia).
  pose proof LH1 as (_ & HNC1 & _). rewrite HC1 in HNC1.
  assert (Rin : In rr RS0) by exact (SUB1 rr (nth_error_In _ _ Hrr)).
  assert (EV : forall a, zV + 16 * Z.of_nat i <= a < zV + 16 * (hl_n Hc - 1) ->
             0 < zCAP /\ zV <= a < zV + 16 * zCAP /\ a < alloc_ceiling).
  { intros a Ha. assert (CP : 0 < zCAP) by lia. destruct (VB CP) as (_ & _ & _ & VCe & _). lia. }
  assert (EEi : forall a, (zHA + 80 + 8 <= a < zHA + 80 + 12 \/ zV + 16 * Z.of_nat i <= a < zV + 16 * (hl_n Hc - 1)) ->
             EE a).
  { intros a [X|X]; cbv beta; [left; lia|]. right. right. destruct (EV a X) as (E1 & E2 & _).
    split; [exact E1 | exact E2]. }
  assert (OQ : ob <> [] -> fst rr <> zOUT).
  { intros ON E. destruct (out_blk L1 A1 ds BR1 SUBD ON) as (_ & _ & _ & _ & OHB). apply OHB. rewrite <- E.
    exact (RB rr Rin). }
  assert (SUBD' : forall r, In r (ds ++ [rr]) -> In r RS0).
  { intros r Hr. apply in_app_iff in Hr as [Hr|[<-|[]]]; [exact (SUBD r Hr) | exact Rin]. }
  split.
  - split; [exact RMo|]. split; [exact INI2|]. split; [exact RO2|].
    split; [split; [rewrite ce_run_snoc; exact RES2 | rewrite HR2; exact (bu_drop _ _ _ L1 A1 m1 md1 L2 A2 m2 md2 Hc i rr
                                                                        BU1 RMi LH1 Hrr)]|].
    split; [exact LH2|]. split; [exact HV2|]. split; [exact HC2|].
    split.
    { unfold texts in *. rewrite HR2, hf_texts_drop. apply hf_nodup. apply hf_nodup_drop. apply hf_nodup. exact ND1. }
    split; [intros r Hr; rewrite HR2 in Hr; exact (SUB1 r (hf_in_drop _ i r Hr))|].
    split; [exact SUBD'|].
    split; [rewrite HR2, length_app, length_firstn, length_skipn; lia|].
    split.
    { apply (c_hi _ _ _ _ L1 A1 m1 md1 L2 A2 m2 md2 _ _ RMi HM1 ltac:(lia) ATC1 ltac:(lia)
               ltac:(cbn [cells_size csize Nat.add]; lia)).
      intros k Hk X. cbv beta in X. destruct X as [X|X]; [lia | pose proof (EV _ X); lia]. }
    split.
    { exact (mf_rmid _ _ _ _ L1 A1 m1 md1 L2 A2 m2 md2 ds RMi HM1 KK ltac:(lia) ltac:(rewrite EKD; lia) RO1 RO2
               EEi (fun ON E => OQ ON (eq_sym E)) BR1 SUBD MF1). }
    exact (br_free L1 A1 L2 A2 m1 md1 ds (fst rr) _ rr b1 b2 HM1 BR1 eq_refl BL1 BL2).
  - exists jj. apply (c_hi _ _ _ _ L1 A1 m1 md1 L2 A2 m2 md2 _ _ RMi HM1 ltac:(lia) FR1 ltac:(lia)).
    + unfold ce_ftl. cbn [cells_size csize app Nat.add]. lia.
    + intros k Hk X. cbv beta in X. destruct X as [X|X]; [lia | pose proof (EV _ X); lia].
Qed.

Lemma gl_np : forall i rr, nth_error RS0 i = Some rr -> prefixb P (snd rr) = false ->
  firstn (S i) RS0 ++ filter (fun r => negb (prefixb P (snd r))) (skipn (S i) RS0) =
    firstn i RS0 ++ filter (fun r => negb (prefixb P (snd r))) (skipn i RS0) /\
  filter (fun r => prefixb P (snd r)) (skipn (S i) RS0) = filter (fun r => prefixb P (snd r)) (skipn i RS0).
Proof.
  intros i rr Hrr E. rewrite (ce_skipn_S RS0 i rr Hrr), (ce_firstn_S RS0 i rr Hrr).
  destruct (ce_fcons P rr (skipn (S i) RS0)) as (F1 & F2). rewrite E in F1, F2. rewrite F1, F2, <- app_assoc.
  split; reflexivity.
Qed.

Lemma gl_p : forall i rr, nth_error RS0 i = Some rr -> prefixb P (snd rr) = true ->
  filter (fun r => negb (prefixb P (snd r))) (skipn (S i) RS0) =
    filter (fun r => negb (prefixb P (snd r))) (skipn i RS0) /\
  List.rev (filter (fun r => prefixb P (snd r)) (skipn (S i) RS0)) ++ [rr] =
    List.rev (filter (fun r => prefixb P (snd r)) (skipn i RS0)).
Proof.
  intros i rr Hrr E. rewrite (ce_skipn_S RS0 i rr Hrr).
  destruct (ce_fcons P rr (skipn (S i) RS0)) as (F1 & F2). rewrite E in F1, F2. rewrite F1, F2.
  split; reflexivity.
Qed.

Definition RGe (R : bvmap 5 word) (w : Z) : Prop :=
  reg_get R 2 = Z_to_bv 64 zSP1 /\ reg_get R 3 = reg_get regs 3 /\ reg_get R 4 = reg_get regs 4 /\
  reg_get R 8 = Z_to_bv 64 zPF /\ reg_get R 9 = Z_to_bv 64 (zHA + 80) /\ reg_get R 18 = Z_to_bv 64 zAT /\
  reg_get R 20 = Z_to_bv 64 4 /\ reg_get R 22 = Z_to_bv 64 5 /\ reg_get R 23 = Z_to_bv 64 0x646e6520 /\
  reg_get R 24 = Z_to_bv 64 (w - 1) /\ reg_get R 26 = reg_get regs 26 /\ reg_get R 27 = reg_get regs 27.

Definition JE (L1 : layout) (A1 : astate) (R1 : bvmap 5 word) (m1 : word -> option byte) (md1 : Model)
    (Hc : hlist) (ds : list (Z * list byte)) (c : Z) (w : nat) : Prop :=
  ceJ L1 A1 m1 md1 Hc ds c /\ RGe R1 (Z.of_nat w) /\ gone = 0 /\ (1 <= w)%nat /\ 0 <= A0 + c <= zNO /\
  ends_run P (hl_recs Hc) (skipn (Z.to_nat (A0 + c)) ob) w <> None /\
  (forall rsF dsF cF, ends_run P (hl_recs Hc) (skipn (Z.to_nat (A0 + c)) ob) w = Some (rsF, dsF, cF) ->
     ends_run P RS0 D0 zW = Some (rsF, ds ++ dsF, c + cF)).

Lemma eloop : forall w L1 A1 R1 m1 md1 Hc ds c, JE L1 A1 R1 m1 md1 Hc ds c w -> ce_frm m1 ->
  SR rsegs (mkCfg (YK11.mkst R1 (Z_to_bv 64 0x14bf4) m1 (PropExec.seg_rom rsegs)) md1) cePOST.
Proof.
  induction w as [|w IH]; intros L1 A1 R1 m1 md1 Hc ds c JJ (jj & FR).
  { destruct JJ as (_ & _ & _ & X & _). lia. }
  destruct JJ as (J & RG & G0 & _ & HAc & NN & REL).
  pose proof J as (RM & INI & RO1 & RES1 & LH1 & HV1 & HC1 & ND1 & SUB1 & SUBD & LEN1 & ATC1 & MF1 & BR1).
  pose proof cf0 as (HM0 & HWF0 & HBD0 & HRA0 & HAL0 & HC0 & H630 & HWS0 & HTP0 & HERR0).
  pose proof (@YM05.alloc_ceiling_value rc) as ACV.
  pose proof cfV as (_ & NDB & V0 & HNC & VNR & NDR & VB & RB).
  pose proof RM as (HM1 & HWF1 & HBD1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & SC1).
  pose proof (bv_unsigned_in_range 64 (reg_get regs 2)) as RSP. change (bv_modulus 64) with (2 ^ 64) in RSP.
  pose proof (bv_unsigned_in_range 64 (reg_get regs 11)) as RPF. change (bv_modulus 64) with (2 ^ 64) in RPF.
  pose proof (bv_unsigned_in_range 64 (reg_get regs 12)) as RAT. change (bv_modulus 64) with (2 ^ 64) in RAT.
  pose proof (bv_unsigned_in_range 64 nout) as RNO. change (bv_modulus 64) with (2 ^ 64) in RNO.
  pose proof (bv_unsigned_in_range 64 out) as ROU. change (bv_modulus 64) with (2 ^ 64) in ROU.
  assert (HAr : 203040 <= zHA <= 203328) by (unfold G_S, SRC_SIZE; lia).
  pose proof (ce_ends_len P (S w) (hl_recs Hc) _ NN) as WL.
  pose proof NN as NN0. cbn [ends_run] in NN0.
  destruct (split_nul (skipn (Z.to_nat (A0 + c)) ob)) as [[l d']|] eqn:SN; [|congruence].
  destruct (Nat.leb 4 (length l) && list_eqb (bzs (skipn (length l - 4) l)) (bzs END4) && prefixb P l) eqn:CND;
    [|congruence].
  destruct (find_text (firstn (length l - 4) l) (hl_recs Hc)) as [i|] eqn:FTE; [|congruence].
  destruct (ends_run P (drop_nth i (hl_recs Hc)) d' w) as [[[rs' ds'] c']|] eqn:ER'; [|congruence].
  clear NN0.
  assert (STEP : forall rsF dsF cF, ends_run P (drop_nth i (hl_recs Hc)) d' w = Some (rsF, dsF, cF) ->
     ends_run P (hl_recs Hc) (skipn (Z.to_nat (A0 + c)) ob) (S w) =
       Some (rsF, nth i (hl_recs Hc) (0, []) :: dsF, Z.of_nat (length l) + 1 + cF)).
  { intros rsF dsF cF X. cbn [ends_run]. rewrite SN, CND, FTE, X. reflexivity. }
  destruct (ce_split_inv _ l d' SN) as [Edl NZl].
  pose proof CND as C3. apply andb_true_iff in C3 as [C1 C3]. apply andb_true_iff in C1 as [C1 C2].
  apply Nat.leb_le in C1. apply ce_eqb_true, ce_bzs_inj in C2. apply ce_prefixb in C3.
  destruct (ce_find_text _ _ _ FTE) as (Hil & Hsn & Hmin).
  set (rr := nth i (hl_recs Hc) (0, [])) in *.
  assert (Hrr : nth_error (hl_recs Hc) i = Some rr) by (unfold rr; apply nth_error_nth'; exact Hil).
  pose proof LH1 as (HC0' & HNC1 & HAR1 & HND11 & HND21 & HFA1).
  rewrite SEG, HV1, HC1 in HC0'. unfold hl_n in HNC1. rewrite HC1 in HNC1.
  assert (CAPp : 0 < zCAP) by lia.
  destruct (VB CAPp) as (VIn & VFr & V4 & VCe & VAl & VHB).
  assert (OBN : ob <> []) by (intros E; rewrite E, skipn_nil in SN; discriminate).
  destruct (out_blk L1 A1 ds BR1 SUBD OBN) as (CO & HCO & OIn1 & OFr & OHB).
  pose proof OFr as (OF1 & OF2 & OF3).
  assert (UA : bv_unsigned (Z_to_bv 64 (A0 + c)) = A0 + c) by (apply unsigned_lit; lia).
  assert (Hlen : A0 + c + Z.of_nat (length l) + 1 <= zNO).
  { pose proof (f_equal (@length byte) Edl) as X. rewrite length_skipn, length_app in X. cbn [length] in X. lia. }
  assert (HN26' : Z.of_nat (length (hl_recs Hc)) < 2 ^ 26) by (unfold hl_n in hN26; lia).
  destruct (ce_cut m1 zSP1 [CB 24 jj] FT FR) as (F24 & FRt).
  replace (zSP1 + Z.of_nat (cells_size [CB 24 jj])) with (zSP1 + 24) in FRt by (cbn [cells_size csize Nat.add]; lia).
  destruct MF1 as (P1 & G1 & N1 & O1 & B1).
  assert (NHC : rw_cells rsegs (normalize rsegs m1) (zHA + 80)
                  [C8 (Z_to_bv 64 zV); C4 (Z_to_bv 64 (hl_n Hc)); C4 (Z_to_bv 64 zCAP)]).
  { apply (rw_cells_normalize rsegs m1 _ _ RO1 HC0'). intros k Hk. apply hf_ro_glob.
    cbn [cells_size csize Nat.add] in Hk. unfold G_S, SRC_SIZE in *. lia. }
  assert (NF24 : rw_cells rsegs (normalize rsegs m1) zSP1 [CB 24 jj]).
  { apply (rw_cells_normalize rsegs m1 _ _ RO1 F24). intros k Hk. apply ro_addr_hi.
    cbn [cells_size csize Nat.add] in Hk. lia. }
  assert (NAT : rw_cells rsegs (normalize rsegs m1) zAT [C8 (Z_to_bv 64 (A0 + c))]).
  { apply (rw_cells_normalize rsegs m1 _ _ RO1 ATC1). intros k Hk. apply ro_addr_hi.
    cbn [cells_size csize Nat.add] in Hk. lia. }
  assert (NLR : forall k r', nth_error (wrecs Hc) k = Some r' -> list_rec (normalize rsegs m1) zV k r').
  { intros k r' Hk. destruct (hf_lrec Bm L1 A1 m1 _ Hc true LH1 k r' Hk) as (X1 & X2 & _).
    rewrite SEG, HV1 in X1. rewrite SEG in X2.
    split; [exact (bytes_at_normalize rsegs m1 _ _ RO1 X1) | exact (bytes_at_normalize rsegs m1 _ _ RO1 X2)]. }
  assert (NLRB : forall k r', nth_error (wrecs Hc) k = Some r' ->
            bv_unsigned (fst r') + Z.of_nat (length (snd r')) + 1 <= zSP0 - 8352).
  { intros k r' Hk. destruct (hf_lrec Bm L1 A1 m1 _ Hc true LH1 k r' Hk) as (_ & _ & _ & X4 & _). lia. }
  eapply (kstep (fun a => zAT <= a < zAT + 8) [(zSP1 - 80, zSP1 + 24); (zAT, zAT + 8)] L1 A1 m1 md1 R1
            (Z_to_bv 64 0x14bf4)).
  { exact RM. }
  { exact RO1. }
  { intros a X. cbv beta. right. left. exact X. }
  { intros a X Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ a HM1 Ho). lia. }
  { intros x Hx O. destruct (hg_not_out _ _ O) as (lo & hi & [E|[E|[]]] & Hlh); injection E as <- <-;
      [left; lia | right; exact Hlh]. }
  { destruct RG as (E2 & E3 & E4 & E8 & E9 & E18 & E20 & E22 & E23 & E24 & E26 & E27).
    unfold Regs6ss.mkR_of. rewrite E2, E3, E4, E8, E9, E18, E20, E22, E23, E24, E26, E27.
    eapply (ce_e1 NLC LFC HPC) with (lo := zSP0 - 8352) (SP := zSP1) (AT := zAT) (V := zV) (N := hl_n Hc)
      (CAP := zCAP) (at0 := Z_to_bv 64 (A0 + c)) (nout := nout) (out := out) (j := jj) (ob := ob) (ln := l)
      (rest := d') (P := P) (slack := slack) (recs := wrecs Hc) (i := i) (r := (Z_to_bv 64 (fst rr), snd rr)).
    - apply ce_stk; [exact (fun a Ha => SC1 a (or_introl Ha)) | lia].
    - lia.
    - lia.
    - Z.div_mod_to_equations. lia.
    - lia.
    - apply mem_inv_normalize.
    - exact NF24.
    - exact NAT.
    - exact hATM.
    - lia.
    - exact hATH.
    - exact (bytes_at_normalize rsegs m1 _ _ RO1 N1).
    - exact (bytes_at_normalize rsegs m1 _ _ RO1 O1).
    - exact (bytes_at_normalize rsegs m1 _ _ RO1 B1).
    - exact hOL.
    - lia.
    - lia.
    - rewrite UA. exact Edl.
    - exact NZl.
    - exact C1.
    - exact C2.
    - rewrite unsigned_lit by lia. exact NHC.
    - rewrite unsigned_lit by lia. lia.
    - rewrite unsigned_lit by lia. unfold G_S, SRC_SIZE. Z.div_mod_to_equations. lia.
    - unfold hl_n. lia.
    - unfold wrecs. rewrite length_map. reflexivity.
    - intros _. split; [lia | Z.div_mod_to_equations; lia].
    - lia.
    - unfold hl_n. lia.
    - exact NLR.
    - exact NLRB.
    - unfold wrecs. rewrite nth_error_map, Hrr. reflexivity.
    - exact Hsn.
    - intros k r' Hk Hr'. unfold wrecs in Hr'. rewrite nth_error_map in Hr'.
      destruct (nth_error (hl_recs Hc) k) as [r0|] eqn:E0; [|discriminate]. cbn [option_map] in Hr'.
      injection Hr' as <-. cbn [snd].
      assert (E1 : nth k (hl_recs Hc) (0, []) = r0) by (apply nth_error_nth; exact E0).
      rewrite <- E1. exact (Hmin k Hk).
    - rewrite unsigned_lit by lia. exact (bytes_at_normalize rsegs m1 _ _ RO1 P1).
    - exact hNZP.
    - rewrite unsigned_lit by lia. exact hSL.
    - rewrite unsigned_lit by lia. destruct hPD as [(PS1 & PS2)|(PR0 & PR1 & PR2)]; [right; lia | left].
      assert (R1' : ro_addr rsegs (Z_to_bv 64 (zPF + (zPL - 1))) = true) by (apply PR2; lia).
      pose proof (in_img_low Bm SEG _ (ro_in_img Bm SEG (zPF + (zPL - 1)) ltac:(lia) R1')). lia.
    - rewrite unsigned_lit by lia. exact hATP.
    - exact C3.
    - reflexivity.
    - reflexivity.
    - reflexivity. }
  { intros s0 (t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
      MU & WM & _ & _ & _ & _ & ->).
    do 3 eexists. split; [reflexivity|]. split; [exact MU | exact WM]. }
  intros R pc' m0 regs2 m2 HQ GR MREL RMa RMs RO2 MU2 WM2.
  destruct HQ as (t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0' &
    MU & WM & MI & ST & ATn & (j' & F24') & EQ).
  injection EQ as ER EP EM. subst R pc' m0'.
  rewrite UA in ATn.
  pose proof (rw_cells_of_rel rsegs m2 m0 _ _ MREL ATn) as AT2.
  replace (A0 + c + Z.of_nat (length l) + 1) with (A0 + (c + Z.of_nat (length l) + 1)) in AT2 by lia.
  pose proof (rw_cells_of_rel rsegs m2 m0 _ _ MREL F24') as F242.
  assert (FRt2 : rw_cells rsegs m2 (zSP1 + 24) FT).
  { apply (rw_cells_transport rsegs _ m1 m2 _ _ FRt MU2 WM2). unfold ce_ftl.
    cbn [disjoint_from cells_size csize Nat.add]. split; [lia|]. split; [lia | exact I]. }
  assert (FR2 : ce_frm m2).
  { exists j'. exact (ce_join m2 zSP1 (zSP1 + 24) [CB 24 j'] FT F242 FRt2 ltac:(cbn [cells_size csize Nat.add]; lia)). }
  assert (LH2 : list_at Bm L1 A1 m2 (zHA + 80) Hc true).
  { eapply (list_at_rmid Bm API AX BW 8352 zSP0); [exact SEG | lia | exact HM1 | exact RMs | exact LH1 | |].
    - intros k Hk. split; [apply hPLR; unfold G_GONE, G_S, SRC_SIZE, SOURCES_MAX in *; lia | cbv beta; lia].
    - intros q Hq. split; [intros [] |]. intros k0 i0 Hin Hi0 X. cbv beta in X.
      destruct (block_facts Bm (aa_MR API) (aa_laws API) L1 A1 m1 md1 q k0 i0 HM1 Hin Hi0) as (_ & B1' & B2' & _).
      lia. }
  assert (MF2 : ce_mf m2).
  { apply (mf_rmid _ _ _ _ L1 A1 m1 md1 L1 A1 m2 md1 ds RMs HM1 ltac:(lia) ltac:(lia) ltac:(lia) RO1 RO2).
    - intros a X. cbv beta. right. left. exact X.
    - intros _ [].
    - exact BR1.
    - exact SUBD.
    - split; [exact P1|]. split; [exact G1|]. split; [exact N1|]. split; [exact O1 | exact B1]. }
  assert (J2 : ceJ L1 A1 m2 md1 Hc ds (c + Z.of_nat (length l) + 1)).
  { split; [exact RMa|]. split; [exact INI|]. split; [exact RO2|]. split; [exact RES1|].
    split; [exact LH2|]. split; [exact HV1|]. split; [exact HC1|]. split; [exact ND1|]. split; [exact SUB1|].
    split; [exact SUBD|]. split; [exact LEN1|]. split; [exact AT2|]. split; [exact MF2 | exact BR1]. }
  assert (E2_1 : YK11.getr regs2 1 = Z_to_bv 64 0x14c88) by (rewrite GR; reflexivity).
  eapply (dstep L1 A1 m2 md1 Hc ds (c + Z.of_nat (length l) + 1) regs2 i rr).
  { exact J2. }
  { exact Hrr. }
  { rewrite GR. reflexivity. }
  { rewrite GR. reflexivity. }
  { change (spZ regs2) with (bv_unsigned (YK11.getr regs2 2)). rewrite GR.
    transitivity (bv_unsigned (Z_to_bv 64 zSP1)); [reflexivity | apply unsigned_lit; lia]. }
  { rewrite E2_1. apply ret_ok_even. vm_compute. reflexivity. }
  { rewrite GR. exact HTP0. }
  intros L2 A2 regs3 m3 md3 l' RMo RMi PR INI3 RO3 RES3 LH3 HV3 HC3 HR3 BL.
  rewrite E2_1.
  destruct (post_drop L1 A1 m2 md1 L2 A2 m3 md3 Hc l' ds (c + Z.of_nat (length l) + 1) i rr J2 FR2 Hrr RMo RMi
              INI3 RO3 RES3 LH3 HV3 HC3 HR3 BL) as (J3 & FR3).
  assert (E3_2 : reg_get regs3 2 = Z_to_bv 64 zSP1)
    by exact (eq_trans (PR 2 ltac:(unfold callee_saved; lia)) (GR _)).
  assert (E3_3 : reg_get regs3 3 = reg_get regs 3)
    by exact (eq_trans (PR 3 ltac:(unfold callee_saved; lia)) (GR _)).
  assert (E3_4 : reg_get regs3 4 = reg_get regs 4)
    by exact (eq_trans (PR 4 ltac:(unfold callee_saved; lia)) (GR _)).
  assert (E3_8 : reg_get regs3 8 = Z_to_bv 64 zPF)
    by exact (eq_trans (PR 8 ltac:(unfold callee_saved; lia)) (GR _)).
  assert (E3_9 : reg_get regs3 9 = Z_to_bv 64 (zHA + 80))
    by exact (eq_trans (PR 9 ltac:(unfold callee_saved; lia)) (GR _)).
  assert (E3_18 : reg_get regs3 18 = Z_to_bv 64 zAT)
    by exact (eq_trans (PR 18 ltac:(unfold callee_saved; lia)) (GR _)).
  assert (E3_20 : reg_get regs3 20 = Z_to_bv 64 4)
    by exact (eq_trans (PR 20 ltac:(unfold callee_saved; lia)) (GR _)).
  assert (E3_22 : reg_get regs3 22 = Z_to_bv 64 5)
    by exact (eq_trans (PR 22 ltac:(unfold callee_saved; lia)) (GR _)).
  assert (E3_23 : reg_get regs3 23 = Z_to_bv 64 0x646e6520)
    by exact (eq_trans (PR 23 ltac:(unfold callee_saved; lia)) (GR _)).
  assert (E3_24 : reg_get regs3 24 = Z_to_bv 64 (Z.of_nat (S w) - 1))
    by exact (eq_trans (PR 24 ltac:(unfold callee_saved; lia)) (GR _)).
  assert (E3_26 : reg_get regs3 26 = reg_get regs 26)
    by exact (eq_trans (PR 26 ltac:(unfold callee_saved; lia)) (GR _)).
  assert (E3_27 : reg_get regs3 27 = reg_get regs 27)
    by exact (eq_trans (PR 27 ltac:(unfold callee_saved; lia)) (GR _)).
  eapply (kstep (fun _ => False) [] L2 A2 m3 md3 regs3 (Z_to_bv 64 0x14c88)).
  { exact RMo. }
  { exact RO3. }
  { intros a []. }
  { intros a []. }
  { intros x _ O. exfalso. exact (O I). }
  { unfold Regs6ss.mkR_of.
    rewrite E3_2, E3_3, E3_4, E3_8, E3_9, E3_18, E3_20, E3_22, E3_23, E3_24, E3_26, E3_27.
    eapply ce_e2 with (w := Z.of_nat (S w)); [reflexivity | lia]. }
  { intros s0 [(_ & ->)|(_ & ->)]; do 3 eexists; (split; [reflexivity|]);
      (split; [apply munch_refl | apply wmono_refl]). }
  intros R pc' m0q regs4 m4 HQ GR4 MREL4 RMa4 RMs4 RO4 MU4 WM4.
  pose proof (ceJ_step L2 A2 m3 md3 m4 l' (ds ++ [rr]) _ J3 RMa4 RMs4 RO4) as J4.
  assert (FR4 : ce_frm m4).
  { destruct FR3 as (j3 & F3). exists j3. apply (rw_cells_transport rsegs _ m3 m4 _ _ F3 MU4 WM4).
    cbn [disjoint_from]. exact I. }
  assert (SK' : skipn (Z.to_nat (A0 + (c + Z.of_nat (length l) + 1))) ob = d').
  { replace (A0 + (c + Z.of_nat (length l) + 1)) with (A0 + c + Z.of_nat (length l) + 1) by lia.
    exact (ce_skip_line ob l d' (A0 + c) ltac:(lia) Edl). }
  destruct HQ as [(Hw & EQ)|(Hw & EQ)]; injection EQ; intros; subst R pc'.
  - eapply (IH L2 A2 regs4 m4 md3 l' (ds ++ [rr]) (c + Z.of_nat (length l) + 1)); [|exact FR4].
    split; [exact J4|].
    split.
    { unfold RGe. repeat split; rgx GR4; first [reflexivity | (f_equal; lia)]. }
    split; [exact G0|]. split; [lia|]. split; [lia|].
    rewrite SK', HR3.
    change (firstn i (hl_recs Hc) ++ skipn (S i) (hl_recs Hc)) with (drop_nth i (hl_recs Hc)).
    split; [rewrite ER'; discriminate|].
    intros rsF dsF cF X. rewrite (REL _ _ _ (STEP _ _ _ X)). rewrite <- app_assoc. f_equal. f_equal. lia.
  - assert (w = 0)%nat by lia. subst w.
    apply (epi L2 A2 regs4 m4 md3 l' (ds ++ [rr]) (c + Z.of_nat (length l) + 1) J4 FR4).
    + rgx GR4. reflexivity.
    + rgx GR4. reflexivity.
    + rgx GR4. reflexivity.
    + rgx GR4. reflexivity.
    + rgx GR4. reflexivity.
    + right. split; [exact G0|].
      pose proof (REL _ _ _ (STEP (drop_nth i (hl_recs Hc)) [] 0 eq_refl)) as X.
      rewrite X, HR3. f_equal. f_equal. all: first [reflexivity | lia].
Qed.

Definition RGg (R : bvmap 5 word) (i : Z) : Prop :=
  reg_get R 2 = Z_to_bv 64 zSP1 /\ reg_get R 3 = reg_get regs 3 /\ reg_get R 4 = reg_get regs 4 /\
  reg_get R 8 = Z_to_bv 64 zPF /\ reg_get R 9 = Z_to_bv 64 (zHA + 80) /\ reg_get R 19 = Z_to_bv 64 (i + 1) /\
  reg_get R 26 = reg_get regs 26 /\ reg_get R 27 = reg_get regs 27.

Definition JG (L1 : layout) (A1 : astate) (R1 : bvmap 5 word) (m1 : word -> option byte) (md1 : Model)
    (Hc : hlist) (i : nat) : Prop :=
  ceJ L1 A1 m1 md1 Hc (List.rev (filter (fun r => prefixb P (snd r)) (skipn (S i) RS0))) 0 /\
  RGg R1 (Z.of_nat i) /\ gone <> 0 /\ (i < length RS0)%nat /\
  hl_recs Hc = firstn (S i) RS0 ++ filter (fun r => negb (prefixb P (snd r))) (skipn (S i) RS0).

Lemma gstep : forall i,
  (forall L2 A2 R2 m2 md2 Hc2, (0 < i)%nat -> JG L2 A2 R2 m2 md2 Hc2 (i - 1) -> ce_frm m2 ->
     SR rsegs (mkCfg (YK11.mkst R2 (Z_to_bv 64 0x14b4c) m2 (PropExec.seg_rom rsegs)) md2) cePOST) ->
  forall L1 A1 R1 m1 md1 Hc, JG L1 A1 R1 m1 md1 Hc i -> ce_frm m1 ->
  SR rsegs (mkCfg (YK11.mkst R1 (Z_to_bv 64 0x14b4c) m1 (PropExec.seg_rom rsegs)) md1) cePOST.
Proof.
  intros i IH L1 A1 R1 m1 md1 Hc JJ (jj & FR).
  destruct JJ as (J & RG & G0 & Hi & ERc).
  pose proof J as (RM & INI & RO1 & RES1 & LH1 & HV1 & HC1 & ND1 & SUB1 & SUBD & LEN1 & ATC1 & MF1 & BR1).
  pose proof cf0 as (HM0 & HWF0 & HBD0 & HRA0 & HAL0 & HC0 & H630 & HWS0 & HTP0 & HERR0).
  pose proof (@YM05.alloc_ceiling_value rc) as ACV.
  pose proof cfV as (_ & NDB & V0 & HNC & VNR & NDR & VB & RB).
  pose proof RM as (HM1 & HWF1 & HBD1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & SC1).
  pose proof (bv_unsigned_in_range 64 (reg_get regs 2)) as RSP. change (bv_modulus 64) with (2 ^ 64) in RSP.
  pose proof (bv_unsigned_in_range 64 (reg_get regs 11)) as RPF. change (bv_modulus 64) with (2 ^ 64) in RPF.
  pose proof (bv_unsigned_in_range 64 (reg_get regs 12)) as RAT. change (bv_modulus 64) with (2 ^ 64) in RAT.
  assert (HAr : 203040 <= zHA <= 203328) by (unfold G_S, SRC_SIZE; lia).
  assert (HN26' : Z.of_nat (length RS0) < 2 ^ 26) by (unfold hl_n in hN26; lia).
  set (ds := List.rev (filter (fun r => prefixb P (snd r)) (skipn (S i) RS0))) in *.
  destruct (nth_error RS0 i) as [rr|] eqn:Hrr0; [|apply nth_error_None in Hrr0; lia].
  assert (FS : firstn (S i) RS0 = firstn i RS0 ++ [rr]) by exact (ce_firstn_S RS0 i rr Hrr0).
  assert (Lfi : length (firstn i RS0) = i) by (rewrite length_firstn; lia).
  assert (Hrr : nth_error (hl_recs Hc) i = Some rr).
  { rewrite ERc, FS, <- app_assoc, nth_error_app2 by lia. rewrite Lfi, Nat.sub_diag. reflexivity. }
  assert (Hil : (i < length (hl_recs Hc))%nat) by (apply nth_error_Some; rewrite Hrr; discriminate).
  pose proof LH1 as (HC0' & HNC1 & HAR1 & HND11 & HND21 & HFA1).
  rewrite SEG, HV1, HC1 in HC0'. unfold hl_n in HNC1. rewrite HC1 in HNC1.
  assert (CAPp : 0 < zCAP) by lia.
  destruct (VB CAPp) as (VIn & VFr & V4 & VCe & VAl & VHB).
  destruct HAR1 as [(X & _)|(_ & VIn1 & VFr1 & VJ1 & AV1)]; [rewrite HC1 in X; lia|].
  unfold hl_n in VJ1. rewrite HC1 in VJ1.
  pose proof HFA1 as HFA1'. rewrite Forall_forall in HFA1'.
  destruct (HFA1' rr (nth_error_In _ _ Hrr)) as (RIn & (RF1 & RF2 & RF3) & _).
  destruct (hf_lrec Bm L1 A1 m1 _ Hc true LH1 i (Z_to_bv 64 (fst rr), snd rr)) as (X1 & X2 & _).
  { unfold wrecs. rewrite nth_error_map, Hrr. reflexivity. }
  cbn [fst snd] in X1, X2. rewrite SEG, HV1 in X1. rewrite SEG in X2. rewrite unsigned_lit in X2 by lia.
  destruct MF1 as (P1 & G1 & N1 & O1 & B1).
  assert (NHC : rw_cells rsegs (normalize rsegs m1) (zHA + 80)
                  [C8 (Z_to_bv 64 zV); C4 (Z_to_bv 64 (hl_n Hc)); C4 (Z_to_bv 64 zCAP)]).
  { apply (rw_cells_normalize rsegs m1 _ _ RO1 HC0'). intros k Hk. apply hf_ro_glob.
    cbn [cells_size csize Nat.add] in Hk. unfold G_S, SRC_SIZE in *. lia. }
  eapply (kstep (fun _ => False) [(zSP1 - 32, zSP1)] L1 A1 m1 md1 R1 (Z_to_bv 64 0x14b4c)).
  { exact RM. }
  { exact RO1. }
  { intros a []. }
  { intros a []. }
  { intros x Hx O. left. destruct (hg_not_out _ _ O) as (lo & hi & [E|[]] & Hlh). injection E as <- <-. lia. }
  { destruct RG as (E2 & E3 & E4 & E8 & E9 & E19 & E26 & E27).
    unfold Regs6ss.mkR_of. rewrite E2, E3, E4, E8, E9, E19, E26, E27.
    eapply (ce_g1 HPC) with (lo := zSP0 - 8352) (V := zV) (N := hl_n Hc) (CAP := zCAP) (i := Z.of_nat i)
      (q := fst rr) (S := snd rr) (P := P) (slack := slack).
    - rewrite unsigned_lit by lia. exact NHC.
    - unfold ro_cells, cells_at. split; [cbn; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
      exact (bytes_at_normalize rsegs m1 _ _ RO1 X1).
    - apply bytes_at_app in X2. exact (bytes_at_normalize rsegs m1 _ _ RO1 (proj1 X2)).
    - lia.
    - lia.
    - lia.
    - lia.
    - Z.div_mod_to_equations. lia.
    - lia.
    - rewrite unsigned_lit by lia. exact (bytes_at_normalize rsegs m1 _ _ RO1 P1).
    - exact hNZP.
    - rewrite unsigned_lit by lia. exact hSL.
    - apply mem_inv_normalize.
    - rewrite unsigned_lit by lia. apply ce_stk; [exact (fun a Ha => SC1 a (or_introl Ha)) | lia].
    - rewrite unsigned_lit by lia. lia.
    - rewrite unsigned_lit by lia. left. lia.
    - rewrite !unsigned_lit by lia. destruct hPD as [(PS1 & PS2)|(PR0 & PR1 & PR2)]; [right; lia | left].
      assert (R1' : ro_addr rsegs (Z_to_bv 64 (zPF + (zPL - 1))) = true) by (apply PR2; lia).
      pose proof (in_img_low Bm SEG _ (ro_in_img Bm SEG (zPF + (zPL - 1)) ltac:(lia) R1')). lia.
    - reflexivity. }
  { intros s0 (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & MU & WM & _ & _ &
      CASE).
    rewrite unsigned_lit in MU by lia.
    destruct CASE as [(_ & ->)|[(_ & _ & ->)|(_ & _ & ->)]]; do 3 eexists; (split; [reflexivity|]);
      (split; [exact MU | exact WM]). }
  intros R pc' m0 regs2 m2 HQ GR MREL RMa RMs RO2 MU2 WM2.
  destruct HQ as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0' & MU & WM & MI &
    ST & CASE).
  assert (EM : m0 = m0') by (destruct CASE as [(_ & EQ)|[(_ & _ & EQ)|(_ & _ & EQ)]]; injection EQ; intros; subst;
                               reflexivity).
  subst m0'.
  pose proof (ceJ_step L1 A1 m1 md1 m2 Hc ds 0 J RMa RMs RO2) as J2.
  assert (FR2 : ce_frm m2).
  { exists jj. apply (rw_cells_transport rsegs _ m1 m2 _ _ FR MU2 WM2). cbn [disjoint_from]. split; [lia | exact I]. }
  destruct CASE as [(PO & EQ)|[(PO & Hi0 & EQ)|(PO & Hi0 & EQ)]]; injection EQ; intros; subst R pc'.
  - assert (PB : prefixb P (snd rr) = true) by (apply ce_prefixb; exact PO).
    assert (E2_1 : YK11.getr regs2 1 = Z_to_bv 64 0x14b9c) by (rewrite GR; reflexivity).
    eapply (dstep L1 A1 m2 md1 Hc ds 0 regs2 i rr).
    { exact J2. }
    { exact Hrr. }
    { rewrite GR. reflexivity. }
    { rewrite GR. reflexivity. }
    { change (spZ regs2) with (bv_unsigned (YK11.getr regs2 2)). rewrite GR.
      transitivity (bv_unsigned (Z_to_bv 64 zSP1)); [reflexivity | apply unsigned_lit; lia]. }
    { rewrite E2_1. apply ret_ok_even. vm_compute. reflexivity. }
    { rewrite GR. exact HTP0. }
    intros L2 A2 regs3 m3 md3 l' RMo RMi PR INI3 RO3 RES3 LH3 HV3 HC3 HR3 BL.
    rewrite E2_1.
    destruct (post_drop L1 A1 m2 md1 L2 A2 m3 md3 Hc l' ds 0 i rr J2 FR2 Hrr RMo RMi INI3 RO3 RES3 LH3 HV3 HC3 HR3
                BL) as (J3 & FR3).
    assert (E3_2 : reg_get regs3 2 = Z_to_bv 64 zSP1)
      by exact (eq_trans (PR 2 ltac:(unfold callee_saved; lia)) (GR _)).
    assert (E3_3 : reg_get regs3 3 = reg_get regs 3)
      by exact (eq_trans (PR 3 ltac:(unfold callee_saved; lia)) (GR _)).
    assert (E3_4 : reg_get regs3 4 = reg_get regs 4)
      by exact (eq_trans (PR 4 ltac:(unfold callee_saved; lia)) (GR _)).
    assert (E3_8 : reg_get regs3 8 = Z_to_bv 64 zPF)
      by exact (eq_trans (PR 8 ltac:(unfold callee_saved; lia)) (GR _)).
    assert (E3_9 : reg_get regs3 9 = Z_to_bv 64 (zHA + 80))
      by exact (eq_trans (PR 9 ltac:(unfold callee_saved; lia)) (GR _)).
    assert (E3_19 : reg_get regs3 19 = Z_to_bv 64 (Z.of_nat i))
      by exact (eq_trans (PR 19 ltac:(unfold callee_saved; lia)) (GR _)).
    assert (E3_26 : reg_get regs3 26 = reg_get regs 26)
      by exact (eq_trans (PR 26 ltac:(unfold callee_saved; lia)) (GR _)).
    assert (E3_27 : reg_get regs3 27 = reg_get regs 27)
      by exact (eq_trans (PR 27 ltac:(unfold callee_saved; lia)) (GR _)).
    eapply (kstep (fun _ => False) [] L2 A2 m3 md3 regs3 (Z_to_bv 64 0x14b9c)).
    { exact RMo. }
    { exact RO3. }
    { intros a []. }
    { intros a []. }
    { intros x _ O. exfalso. exact (O I). }
    { unfold Regs6ss.mkR_of. rewrite E3_2, E3_3, E3_4, E3_8, E3_9, E3_19, E3_26, E3_27.
      eapply ce_g2 with (i := Z.of_nat i); [reflexivity | lia]. }
    { intros s0 [(_ & ->)|(_ & ->)]; do 3 eexists; (split; [reflexivity|]);
        (split; [apply munch_refl | apply wmono_refl]). }
    intros R pc' m0q regs4 m4 HQ GR4 MREL4 RMa4 RMs4 RO4 MU4 WM4.
    pose proof (ceJ_step L2 A2 m3 md3 m4 l' (ds ++ [rr]) 0 J3 RMa4 RMs4 RO4) as J4.
    assert (FR4 : ce_frm m4).
    { destruct FR3 as (j3 & F3). exists j3. apply (rw_cells_transport rsegs _ m3 m4 _ _ F3 MU4 WM4).
      cbn [disjoint_from]. exact I. }
    assert (DS : ds ++ [rr] = List.rev (filter (fun r => prefixb P (snd r)) (skipn i RS0)))
      by exact (proj2 (gl_p i rr Hrr0 PB)).
    assert (RC : hl_recs l' = firstn i RS0 ++ filter (fun r => negb (prefixb P (snd r))) (skipn i RS0)).
    { rewrite HR3. change (firstn i (hl_recs Hc) ++ skipn (S i) (hl_recs Hc)) with (drop_nth i (hl_recs Hc)).
      rewrite ERc, ce_drop_pre by lia. rewrite (proj1 (gl_p i rr Hrr0 PB)). reflexivity. }
    rewrite DS in J4.
    destruct HQ as [(Hi0 & EQ2)|(Hi0 & EQ2)]; injection EQ2; intros; subst R pc'.
    + eapply (IH L2 A2 regs4 m4 md3 l' ltac:(lia)); [|exact FR4].
      unfold JG. replace (S (i - 1)) with i by lia.
      split; [exact J4|].
      split.
      { unfold RGg. repeat split; rgx GR4; first [reflexivity | (f_equal; lia)]. }
      split; [exact G0|]. split; [lia|]. exact RC.
    + assert (i = 0)%nat by lia. subst i.
      apply (epi L2 A2 regs4 m4 md3 l' (List.rev (filter (fun r => prefixb P (snd r)) (skipn 0 RS0))) 0 J4 FR4).
      * rgx GR4. reflexivity.
      * rgx GR4. reflexivity.
      * rgx GR4. reflexivity.
      * rgx GR4. reflexivity.
      * rgx GR4. reflexivity.
      * left. split; [exact G0|]. split; [rewrite RC; reflexivity|]. split; reflexivity.
  - destruct (prefixb P (snd rr)) eqn:PB; [exfalso; apply PO; apply ce_prefixb; exact PB|].
    destruct (gl_np i rr Hrr0 PB) as (RC1 & RC2).
    apply (IH L1 A1 regs2 m2 md1 Hc ltac:(lia)); [|exact FR2].
    unfold JG. replace (S (i - 1)) with i by lia.
    split; [unfold ds in J2; rewrite RC2 in J2; exact J2|].
    split; [unfold RGg; repeat split; rgx GR; first [reflexivity | (f_equal; lia)]|].
    split; [exact G0|]. split; [lia|]. rewrite ERc. exact RC1.
  - destruct (prefixb P (snd rr)) eqn:PB; [exfalso; apply PO; apply ce_prefixb; exact PB|].
    assert (i = 0)%nat by lia. subst i.
    destruct (gl_np 0 rr Hrr0 PB) as (RC1 & RC2).
    apply (epi L1 A1 regs2 m2 md1 Hc ds 0 J2 FR2).
    + rgx GR. reflexivity.
    + rgx GR. reflexivity.
    + rgx GR. reflexivity.
    + rgx GR. reflexivity.
    + rgx GR. reflexivity.
    + left. split; [exact G0|]. split; [rewrite ERc; exact RC1|].
      split; [unfold ds; rewrite RC2; reflexivity | reflexivity].
Qed.

Lemma gloop : forall i L1 A1 R1 m1 md1 Hc, JG L1 A1 R1 m1 md1 Hc i -> ce_frm m1 ->
  SR rsegs (mkCfg (YK11.mkst R1 (Z_to_bv 64 0x14b4c) m1 (PropExec.seg_rom rsegs)) md1) cePOST.
Proof.
  induction i as [|i IH]; intros L1 A1 R1 m1 md1 Hc JJ FR.
  - refine (gstep 0 _ L1 A1 R1 m1 md1 Hc JJ FR). intros; lia.
  - refine (gstep (S i) _ L1 A1 R1 m1 md1 Hc JJ FR). intros L2 A2 R2 m2 md2 Hc2 _ J2 F2.
    replace (S i - 1)%nat with i in J2 by lia. exact (IH _ _ _ _ _ _ J2 F2).
Qed.

Lemma run_main : SR rsegs (mkCfg (YK11.mkst regs (Z_to_bv 64 0x14a78) mem (PropExec.seg_rom rsegs)) md) cePOST.
Proof.
  pose proof cf0 as (HM0 & HWF0 & HBD0 & HRA0 & HAL0 & HC0 & H630 & HWS0 & HTP0 & HERR0).
  pose proof (@YM05.alloc_ceiling_value rc) as ACV.
  pose proof cfV as (LH & NDB & V0 & HNC & VNR & NDR & VB & RB).
  pose proof LH as (HC0' & _ & HAR & HND1 & HND2 & HFA).
  rewrite SEG in HC0'. unfold hl_n in HNC.
  pose proof (bv_unsigned_in_range 64 (reg_get regs 2)) as RSP. change (bv_modulus 64) with (2 ^ 64) in RSP.
  pose proof (bv_unsigned_in_range 64 (reg_get regs 11)) as RPF. change (bv_modulus 64) with (2 ^ 64) in RPF.
  pose proof (bv_unsigned_in_range 64 (reg_get regs 12)) as RAT. change (bv_modulus 64) with (2 ^ 64) in RAT.
  assert (HAr : 203040 <= zHA <= 203328) by (unfold G_S, SRC_SIZE; lia).
  assert (A0' : bv_unsigned (reg_get regs 10) = zHA) by (rewrite hR10; apply unsigned_lit; lia).
  assert (HN26' : Z.of_nat (length RS0) < 2 ^ 26) by (unfold hl_n in hN26; lia).
  assert (VL : zV + 16 * Z.of_nat (length RS0) <= alloc_ceiling).
  { destruct (Z.eq_dec zCAP 0) as [Z0|Z0].
    - destruct HAR as [(_ & V00)|(X & _)]; [lia | lia].
    - destruct (VB ltac:(lia)) as (_ & _ & _ & X & _). lia. }
  assert (RM0 : rmid Bm API 8352 zSP0 EE FF L A mem md L A mem md).
  { apply (rmid_A Bm API 8352 zSP0 EE FF L A mem md mem [] HM0 HWF0 HBD0 (hg_img_low Bm SEG) ltac:(lia)).
    - intros a X. rewrite SEG. destruct X as [X|X]; [apply HWS0; lia | apply HERR0; exact X].
    - apply munch_refl.
    - apply wmono_refl.
    - intros x _ O. exfalso. exact (O I).
    - intros a _. exact I.
    - intros p n i _ _ O. exfalso. exact (O I). }
  destruct (ce_cut mem (zHA + 80) [C8 (Z_to_bv 64 zV)] [C4 (Z_to_bv 64 (hl_n (hs_held h))); C4 (Z_to_bv 64 zCAP)] HC0')
    as (HV8 & HRest).
  destruct (ce_cut mem _ [C4 (Z_to_bv 64 (hl_n (hs_held h)))] [C4 (Z_to_bv 64 zCAP)] HRest) as (HN4 & _).
  replace (zHA + 80 + Z.of_nat (cells_size [C8 (Z_to_bv 64 zV)])) with (zHA + 88) in HN4
    by (cbn [cells_size csize Nat.add]; lia).
  assert (GCw : rw_cells rsegs (normalize rsegs mem) 0x318a8 [C1 (Z_to_bv 8 gone)]).
  { pose proof (bytes_at_normalize rsegs mem _ _ hRO hGB) as GBn.
    split; [split; [cbn; tauto | cbn [cells_bytes cbytes app]; exact GBn]|].
    split; [lia|]. split; [cbn [cells_size csize Nat.add]; lia|]. intros k Hk. cbn [cells_size csize Nat.add] in Hk.
    replace k with 0 by lia. rewrite Z.add_0_r. unfold wview, normalize, wa.
    rewrite (hf_ro_glob 0x318a8 ltac:(lia)).
    destruct (mem (Z_to_bv 64 0x318a8)); [discriminate|]. vm_compute. discriminate. }
  eapply (kstep (fun _ => False) [(zSP0 - 144, zSP0)] L A mem md regs (Z_to_bv 64 0x14a78)).
  { exact RM0. }
  { exact hRO. }
  { intros a []. }
  { intros a []. }
  { intros x _ O. left. destruct (hg_not_out _ _ O) as (lo & hi & [E|[]] & Hlh). injection E as <- <-. lia. }
  { unfold Regs6ss.mkR_of. rewrite <- (Z_to_bv_bv_unsigned (reg_get regs 11)).
    eapply (ce_head HPC) with (lo := zSP0 - 8352) (V := zV) (PF := zPF) (rs := RS0) (P := P) (slack := slack)
      (gone := gone).
    - apply ce_stk; [intros a Ha; rewrite SEG; apply HWS0; lia | lia].
    - lia.
    - lia.
    - lia.
    - apply mem_inv_normalize.
    - rewrite A0'. lia.
    - rewrite A0'. unfold G_S, SRC_SIZE. Z.div_mod_to_equations. lia.
    - rewrite A0'. lia.
    - rewrite A0'. apply (rw_cells_normalize rsegs mem _ _ hRO HV8). intros k Hk. apply hf_ro_glob.
      cbn [cells_size csize Nat.add] in Hk. unfold G_S, SRC_SIZE in *. lia.
    - rewrite A0'. apply (rw_cells_normalize rsegs mem _ _ hRO HN4). intros k Hk. apply hf_ro_glob.
      cbn [cells_size csize Nat.add] in Hk. unfold G_S, SRC_SIZE in *. lia.
    - exact HN26'.
    - lia.
    - intros Hn. assert (CAPp : 0 < zCAP) by lia.
      destruct (VB CAPp) as (_ & _ & V4 & _ & VAl & _). split; [lia | Z.div_mod_to_equations; lia].
    - lia.
    - intros k r Hk.
      assert (Hkl : (k < length RS0)%nat) by (apply nth_error_Some; rewrite Hk; discriminate).
      pose proof (ce_rec_cells L A mem _ _ true k r LH Hk) as RCk.
      pose proof HFA as HFA'. rewrite Forall_forall in HFA'.
      destruct (HFA' r (nth_error_In _ _ Hk)) as (RI & (RF1 & RF2 & RF3) & RC & _).
      rewrite SEG in RC.
      assert (CAPp : 0 < zCAP) by lia.
      destruct (VB CAPp) as (_ & VFr & _).
      split; [|split; [|split; lia]].
      + apply (rw_cells_normalize rsegs mem _ _ hRO RCk). intros k0 Hk0. cbn [cells_size csize Nat.add] in Hk0.
        apply (ro_addr_out Bm SEG); [lia|]. intros X. apply (proj2 (proj2 VFr) (16 * Z.of_nat k + k0)); [lia|].
        replace (zV + (16 * Z.of_nat k + k0)) with (zV + 16 * Z.of_nat k + k0) by lia. exact X.
      + destruct RC as [[_ RB'] _]. cbn [cells_bytes cbytes] in RB'. rewrite app_nil_r in RB'.
        apply bytes_at_app in RB'. exact (bytes_at_normalize rsegs mem _ _ hRO (proj1 RB')).
    - lia.
    - exact (bytes_at_normalize rsegs mem _ _ hRO hPB).
    - exact hNZP.
    - exact hSL.
    - destruct hPD as [(PS1 & PS2)|(PR0 & PR1 & PR2)]; [right; lia | left].
      assert (R1' : ro_addr rsegs (Z_to_bv 64 (zPF + (zPL - 1))) = true) by (apply PR2; lia).
      pose proof (in_img_low Bm SEG _ (ro_in_img Bm SEG (zPF + (zPL - 1)) ltac:(lia) R1')). lia.
    - exact GCw.
    - exact hGG. }
  { intros s0 (m' & MU & WM & MI & CASES).
    destruct CASES as [(_ & (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & ->))|
      (_ & _ & [(_ & (ra' & t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & s4' &
                      s6' & s7' & s8' & s9' & ->))|
                (_ & _ & (ra' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' &
                          s9' & ->))])];
      do 3 eexists; (split; [reflexivity|]); (split; [exact MU | exact WM]). }
  intros R pc' m0 regs1 m1 HQ GR MREL RMa RMs RO1 MU1 WM1.
  destruct HQ as (m0' & MU & WM & MI & CASES).
  assert (EM : m0 = m0').
  { destruct CASES as [(_ & (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & EQ))|
      (_ & _ & [(_ & (ra' & t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & s4' &
                      s6' & s7' & s8' & s9' & EQ))|
                (_ & _ & (ra' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' &
                          s9' & EQ))])];
      injection EQ; intros; subst; reflexivity. }
  subst m0'.
  assert (J1 : ceJ L A m1 md (hs_held h) [] 0).
  { split; [exact RMa|]. split; [exact hINIT|]. split; [exact RO1|]. split; [split; [exact hRES | exact bu0]|].
    split.
    { eapply (list_at_rmid Bm API AX BW 8352 zSP0); [exact SEG | lia | exact HM0 | exact RMs | exact LH | |].
      - intros k Hk. split; [apply hPLR; unfold G_GONE, G_S, SRC_SIZE, SOURCES_MAX in *; lia | intros []].
      - intros q _. split; [intros [] | intros k0 i0 _ _ []]. }
    split; [reflexivity|]. split; [reflexivity|]. split; [exact hNDT|]. split; [intros r Hr; exact Hr|].
    split; [intros r []|]. split; [lia|].
    split.
    { rewrite Z.add_0_r. apply (c_hi _ _ _ _ L A mem md L A m1 md _ _ RMs HM0 ltac:(lia) hATC ltac:(lia)
                                 ltac:(cbn [cells_size csize Nat.add]; lia)). intros k _ []. }
    split; [|split; [intros q k Hq _; exact Hq | intros q k Hq; split; [exact Hq | intros []]]].
    apply (mf_rmid _ _ _ _ L A mem md L A m1 md [] RMs HM0 ltac:(lia) ltac:(lia) ltac:(lia) hRO RO1
             (fun a X => False_ind _ X) (fun _ X => X)).
    - split; [intros q k Hq _; exact Hq | intros q k Hq; split; [exact Hq | intros []]].
    - intros r [].
    - split; [exact hPB|]. split; [exact hGB|]. split; [exact hGN|]. split; [exact hGO | exact hOB]. }
  destruct CASES as [(HR & (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & EQ))|
    (Hn & (jj & FR1) & [(G1 & (ra' & t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' &
                               s4' & s6' & s7' & s8' & s9' & EQ))|
                        (G1 & HW & (ra' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' &
                                    t5' & t6' & s9' & EQ))])];
    injection EQ; intros; subst R pc'.
  - apply SR_ret.
    replace (ret_pc (reg_get regs 1)) with (reg_get regs 1) by (symmetry; exact (ret_pc_of_ok _ HRA0)).
    apply (fin_ret L A regs1 m1 md (hs_held h) [] 0 J1).
    + intros r Hr. rewrite GR. unfold callee_saved in Hr.
      assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                   r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
      repeat (destruct Hc as [Hc|Hc]; [subst r; reflexivity|]); subst r; reflexivity.
    + destruct HR as [N0|(Np & G0 & W0)].
      * apply length_zero_iff_nil in N0.
        destruct (Z.eq_dec gone 0) as [G0|G0].
        -- right. split; [exact G0|]. rewrite N0. reflexivity.
        -- left. split; [exact G0|]. rewrite N0. split; [reflexivity|]. split; reflexivity.
      * right. split; [exact G0|]. rewrite W0. reflexivity.
  - apply (gloop (length RS0 - 1) L A regs1 m1 md (hs_held h)).
    + split.
      { replace (List.rev (filter (fun r => prefixb P (snd r)) (skipn (S (length RS0 - 1)) RS0)))
          with (@nil (Z * list byte)); [exact J1|].
        rewrite skipn_all2 by lia. reflexivity. }
      split.
      { unfold RGg. repeat split; rgx GR;
          first [reflexivity | (f_equal; lia) | exact hR10 | (rewrite A0'; reflexivity)]. }
      split; [exact G1|]. split; [lia|].
      rewrite firstn_all2, skipn_all2 by lia.
      change (filter (fun r => negb (prefixb P (snd r))) []) with (@nil (Z * list byte)).
      rewrite app_nil_r. reflexivity.
    + exists jj. exact (rw_cells_of_rel rsegs m1 m0 _ _ MREL FR1).
  - apply (eloop zW L A regs1 m1 md (hs_held h) [] 0).
    + split; [exact J1|].
      split.
      { unfold RGe. repeat split; rgx GR;
          first [reflexivity | exact hR10 | (rewrite A0'; reflexivity) | (symmetry; apply Z_to_bv_bv_unsigned)]. }
      split; [exact G1|]. split; [lia|]. split; [lia|].
      rewrite Z.add_0_r. split; [exact (hER G1)|].
      intros rsF dsF cF X. rewrite X. reflexivity.
    + exists jj. exact (rw_cells_of_rel rsegs m1 m0 _ _ MREL FR1).
Qed.

End Run.

Theorem check_shape_ends_holds : next_line_contract -> list_find_contract -> has_prefix_contract ->
  list_drop_contract Bm API RF -> check_shape_ends_contract Bm API RF.
Proof.
  intros NL LF HP LD. unfold check_shape_ends_contract. cbv zeta.
  intros L A regs mem md bnd h j gone A0 nout out ob P slack SEG PRE INIT RO PLR Hj4 R10 SRC NDT HN HPB NZ SL PD
    ATM ATS ATH ATP ATC GG GB GN GO OBB OBL OBK HA0 ERN RES.
  rewrite SEG in RO, HPB, PD, ATC, GB, GN, GO, OBB |- *.
  eapply SR_mono; [eapply run_main; eassumption|].
  intros c' X. exact X.
Qed.

End CEB.
