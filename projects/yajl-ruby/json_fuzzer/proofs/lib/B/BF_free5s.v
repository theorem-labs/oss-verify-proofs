(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA AImages.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import BF_place BF_kit BF_kit2 BF_gbb BF_qkit.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanConsts AsanSizeClass.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import StrFun.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import SecRanges.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= force_section_ranges.   (* [comment removed for export] *)
Ltac pg := match goal with |- ?g => idtac "GOAL:"; idtac g end.
Ltac phyps := match goal with |- _ => repeat match goal with H : ?t |- _ => idtac H ":" t; fail end end.
Ltac djs := cbn [disjoint_from length cells_size csize Nat.add Nat.mul Z.of_nat Pos.of_succ_nat Pos.succ Pos.mul Pos.add]; rewrite ?length_le8, ?length_le4; repeat split; try exact I; lia.

(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac lia ::=
  first [ LiaTuning.zify_prune; LiaTuning.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | LiaTuning.zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ].
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac aceil :=
  lazymatch goal with
  | H : _ <= alloc_ceiling <= _ |- _ => idtac
  | |- context [alloc_ceiling] => repeat match goal with H : True |- _ => clear H end; pose proof alloc_ceiling_range as CEILB
  | H : context [alloc_ceiling] |- _ => repeat match goal with H' : True |- _ => clear H' end; pose proof alloc_ceiling_range as CEILB
  | _ => first [ pose proof I as CEILB | idtac ]
  end.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac slia ::= first [ exact I | dlia | split; [dlia | exact I] ].
Local Ltac flia ::= first [ assumption | lia ].
Local Definition carry_skip (P : Prop) := P.
Local Ltac skipH H := lazymatch type of H with ?TS => change TS with (carry_skip TS) in H end.

Local Ltac dlia1 := dlia.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac incl_leaves xq Hq :=
  repeat match type of Hq with _ /\ _ => let Q := fresh "Q" in destruct Hq as [Q Hq] end;
  repeat match goal with |- _ /\ _ => split end; try exact I;
  let C := fresh "C" in intros C;
  first [ match goal with Q : ~ (_ <= xq < _) |- _ => apply Q; LiaA.lia_probe end
        | match goal with D : _ \/ _ |- _ => destruct D as [XD|XD]; match goal with Q : ~ (_ <= xq < _) |- _ => apply Q; LiaA.lia_probe end end ].
(* [comment removed for export] *)
Local Ltac solve_covers ::=
  let lo := fresh "lo" in let hi := fresh "hi" in let Hin := fresh "Hin" in
  intros lo hi Hin; cbn [In app] in Hin;
  repeat match type of Hin with
  | _ \/ _ => destruct Hin as [Hin|Hin]; [injection Hin as <- <-; do 2 eexists; split; [cover_member| cbn [fst snd b_addr]; LiaA.lia_probe] |]
  | _ = _ => injection Hin as <- <-; do 2 eexists; split; [cover_member| cbn [fst snd b_addr]; LiaA.lia_probe]
  | False => contradiction
  end.
Local Ltac carry_rw H MU WM ::= eapply rw_cells_transport in H; [| exact MU| exact WM| cbn; repeat match goal with |- _ /\ _ => split end; first [exact I | dlia1]].
Local Ltac carry_all mc m' MUc WMc ::=
  repeat match goal with
  | H : rw_cells bsegs mc _ _ |- _ => first [ carry_rw H MUc WMc | skipH H ]
  | H : bytes_at bsegs mc _ _ |- _ => first [ eapply bytes_at_transport in H; [| exact MUc| cbn [disjoint_from length]; rewrite ?repeat_length, ?length_le8, ?length_le4; lia] | skipH H ]
  | H : stk bsegs mc _ _ |- _ => first [ eapply stk_transport in H; [| exact MUc| exact WMc| intros; left; cbn; lia] | skipH H ]
  | H : wr_at bsegs mc _ _ |- _ => first [ eapply wr_at_transport in H; [| exact WMc] | skipH H ]
  | H : u8arr bsegs mc _ _ |- _ => first [ eapply u8arr_transport in H; [| exact MUc| exact WMc| cbn [disjoint_from length]; rewrite ?repeat_length; lia] | skipH H ]
  | H : u64arr bsegs mc _ _ |- _ => first [ eapply u64arr_transport in H; [| exact MUc| exact WMc| cbn [disjoint_from length]; lia] | skipH H ]
  | H : u32arr bsegs mc _ _ |- _ => first [ eapply u32arr_transport in H; [| exact MUc| exact WMc| cbn [disjoint_from length]; lia] | skipH H ]
  | H : munch ?W ?ma mc |- _ =>
      let H2 := fresh in
      first [ assert (H2 : munch W ma m')
          by (eapply munch_trans; [exact H| eapply munch_weaken; [| exact MUc];
              first [ sub_fp_fast | let xq := fresh "xq" in let Hq := fresh "Hq" in intros xq Hq; cbn in Hq |- *; decompose [and] Hq; clear Hq; repeat match goal with |- _ /\ _ => split end; try exact I; match goal with O : ~ (_ <= xq < _)%Z |- _ => clear -O; let R := fresh in intros R; apply O; lia end ]]);
        clear H; rename H2 into H | skipH H ]
  | H : wmono bsegs ?ma mc |- _ =>
      let H2 := fresh in
      assert (H2 : wmono bsegs ma m') by (eapply wmono_trans; [exact H| exact WMc]);
      clear H; rename H2 into H
  end;
  repeat match goal with H : carry_skip _ |- _ => unfold carry_skip in H end.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma nearest_ge_acc : forall p cs acc, acc <= nearest p acc cs.
Proof.
  intros p cs. induction cs as [|c cs IH]; intros acc; cbn; [lia|].
  eapply Z.le_trans; [| apply IH].
  unfold near_step. destruct (fst c <=? p) eqn:E1; destruct (acc <? fst c) eqn:E2; cbn; try lia.
Qed.

Lemma nearest_ge_in : forall p cs acc c, In c cs -> fst c <= p -> fst c <= nearest p acc cs.
Proof.
  intros p cs. induction cs as [|c0 cs IH]; intros acc c Hin Hp; [destruct Hin|].
  destruct Hin as [<-|Hin].
  - cbn. eapply Z.le_trans; [| apply nearest_ge_acc].
    unfold near_step. replace (fst c0 <=? p) with true by (symmetry; apply Z.leb_le; lia).
    destruct (acc <? fst c0) eqn:E2; cbn; [lia|]. apply Z.ltb_ge in E2. lia.
  - cbn. apply IH; assumption.
Qed.

Lemma gbb_result_hit : forall cs (i : nat) A L p,
  nth_error cs i = Some (A, L) -> A <= p < A + L ->
  Forall (fun c => 0 < fst c /\ 0 < snd c) cs ->
  (forall j k cj ck, nth_error cs j = Some cj -> nth_error cs k = Some ck -> j <> k -> fst cj + snd cj <= fst ck \/ fst ck + snd ck <= fst cj) ->
  gbb_result cs p = A + 4096.
Proof.
  intros cs i A L p NTH HP RNG DISJ.
  pose proof (nth_error_In _ _ NTH) as INA.
  pose proof (proj1 (Forall_forall _ _) RNG _ INA) as [A0 L0]. cbn [fst snd] in A0, L0.
  pose proof (nearest_bounds p cs 0 ltac:(lia)) as NB.
  pose proof (nearest_ge_in p cs 0 (A, L) INA ltac:(cbn; lia)) as NA. cbn [fst] in NA.
  unfold gbb_result.
  set (M := nearest p 0 cs) in *.
  replace (M =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  destruct (nearest_in p cs 0) as [E0|IN]; [exfalso; subst M; lia|]. fold M in IN.
  destruct (in_map_fst_find cs _ IN) as (c & FD & Ec). rewrite FD.
  destruct (find_some_nth _ _ cs c FD) as (k & NTHk & _).
  destruct (Nat.eq_dec k i) as [->|NE].
  - rewrite NTH in NTHk. injection NTHk as <-. cbn [fst snd].
    replace (p <? A + L) with true by (symmetry; apply Z.ltb_lt; lia). cbn [fst] in Ec. lia.
  - exfalso. pose proof (proj1 (Forall_forall _ _) RNG _ (nth_error_In _ _ NTHk)) as [C0 CL0].
    destruct (DISJ _ _ _ _ NTHk NTH NE) as [D|D]; cbn [fst snd] in D; lia.
Qed.

(* [comment removed for export] *)
Lemma rw_cells_app_split5 : forall segs m A cs1 cs2,
  rw_cells segs m A (cs1 ++ cs2) -> rw_cells segs m A cs1 /\ rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof. aceil.
  intros segs m A cs1 cs2 [[WF B] W]. apply cells_wf_app in WF. destruct WF as [W1 W2].
  rewrite cells_bytes_app in B. apply bytes_at_app in B. destruct B as [B1 B2]. rewrite (cells_bytes_length _ W1) in B2.
  rewrite cells_size_app in W. destruct W as (Wa & Wb & Wr).
  split; split; try (split; assumption).
  - split; [lia|]. split; [lia|]. intros i Hi. apply Wr. lia.
  - split; [lia|]. split; [lia|]. intros i Hi. replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by lia. apply Wr. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section QCBS.
Variable P : acc -> Prop.
Variables (ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variable Q : machine_state -> Prop.
Variables (usp lo : Z) (CBP cb SB RI : Z) (b1 nhi nlo : Z) (aidw : word).
Variables (PA : Z) (cs : list (Z * Z)) (junk : list word) (ptrc bb : Z).
Variables (TSD CTX T rf rfd r0 rl : Z).
Notation INST := 0xaaf58.
Definition hk : Z := b1 + 256 * nhi.
Definition n : Z := nhi * 2^32 + nlo.

Hypothesis LOC : alloc_ceiling <= lo.
Hypothesis LO : lo <= usp - 80.
Hypothesis SPH : usp <= 2^47.
Hypothesis SPA : usp mod 16 = 0.
(* [comment removed for export] *)
Hypothesis HSB : 0x603000 <= SB /\ SB mod 4096 = 0 /\ SB + kSpaceSize + 4096 <= alloc_ceiling.
(* [comment removed for export] *)
Hypothesis HCB : 0x603000 <= cb /\ cb + 16 <= alloc_ceiling /\ cb mod 16 = 0.
Hypothesis HCBS : cb + 16 <= SB \/ SB + kSpaceSize <= cb.
Hypothesis HB1 : 0 <= b1 < 256.
Hypothesis HNHI : 0 <= nhi < 256.
Hypothesis HNLO : 0 <= nlo < 2^32.
(* [comment removed for export] *)
Hypothesis HPA : 0x603000 <= PA /\ PA + 8 * (Z.of_nat (length cs) + Z.of_nat (length junk)) <= alloc_ceiling.
Hypothesis RNG : Forall (fun c => 0x603000 <= fst c /\ fst c mod 4096 = 0 /\ 4096 <= snd c /\ fst c + snd c <= alloc_ceiling) cs.
Hypothesis HBB : bb = gbb_result cs cb.
Hypothesis HBBS : 0 < bb /\ bb + 16 <= alloc_ceiling /\ (bb + 16 <= SB \/ SB + kSpaceSize <= bb).
(* [comment removed for export] *)
Hypothesis HT1 : 0x5d0810 <= TSD.
Hypothesis HT2 : TSD + 8 <= 0x603000.
(* [comment removed for export] *)
Hypothesis HCX : 0x1000 <= r0 /\ r0 <= CTX /\ CTX + 160 <= r0 + rl /\ r0 + rl <= alloc_ceiling /\ (r0 + rl <= 0x10000 \/ 0x603000 <= r0).
Hypothesis HC4 : CTX + 4096 <= alloc_ceiling.
Hypothesis HTR : placed_s T 4096.
Hypothesis HTP : 0x5d0810 + 88 <= bv_unsigned tp < 0x603000.
Hypothesis HRF : 0 <= rf < 2^64.
Hypothesis HRFD : 0 <= rfd < 2^64.
(* [comment removed for export] *)
Hypothesis HTPA : PA + 8 * (Z.of_nat (length cs) + Z.of_nat (length junk)) <= T \/ T + 4096 <= PA.
Hypothesis HTL : forall j c', nth_error cs j = Some c' -> fst c' + snd c' <= T \/ T + 4096 <= fst c'.
Hypothesis HTCB : cb + 16 <= T \/ T + 4096 <= cb.
Hypothesis HTC : CTX + 160 <= T \/ T + 4096 <= CTX.
(* [comment removed for export] *)
Hypothesis PSTK : forall a k, lo <= a -> a + Z.of_nat k <= usp -> P (Z_to_bv 64 a, k).
Hypothesis PDAT : forall a k, 0xa5000 <= a -> a + Z.of_nat k <= 0x603000 -> P (Z_to_bv 64 a, k).
Hypothesis PCH : forall a k, cb <= a -> a + Z.of_nat k <= cb + 16 -> P (Z_to_bv 64 a, k).
Hypothesis PARR : forall a k, PA <= a -> a + Z.of_nat k <= PA + 8 * Z.of_nat (length cs) -> P (Z_to_bv 64 a, k).
Hypothesis PHDR : forall j c a k, nth_error cs j = Some c -> fst c <= a -> a + Z.of_nat k <= fst c + 32 -> P (Z_to_bv 64 a, k).
Hypothesis PCTX : P (Z_to_bv 64 (CTX + 152), 8%nat).
Hypothesis PT : forall a k, T <= a -> a + Z.of_nat k <= T + 4096 -> P (Z_to_bv 64 a, k).

Notation qsW := [(usp - 80, usp); (0xab200, 0xab204); (T + 2840, T + 2856)].

(* [comment removed for export] *)
Lemma qcbr_sec_walk : forall m,
  mem_inv bsegs m -> stk bsegs m lo usp ->
  rw_cells bsegs m 0xaaf78 [C8 (Z_to_bv 64 SB); C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 RI)] ->
  rw_cells bsegs m cb [C4 (Z_to_bv 64 (3 + 256 * hk)); C4 (Z_to_bv 64 nlo); C8 aidw] ->
  rw_cells bsegs m 0xaaf98 [C8 (Z_to_bv 64 4096); C8 (Z_to_bv 64 PA)] ->
  rw_cells bsegs m 0xaafc8 [C8 (Z_to_bv 64 ptrc); C8 (Z_to_bv 64 (Z.of_nat (length cs))); C1 (Z_to_bv 8 0)] ->
  rw_cells bsegs m 0xab200 [C4 (Z_to_bv 64 0)] ->
  u64arr bsegs m PA (gws cs junk) ->
  (forall j c', nth_error cs j = Some c' -> exists nd, rw_cells bsegs m (fst c') [C8 (Z_to_bv 64 (fst c')); C8 (Z_to_bv 64 (snd c')); C8 nd; C8 (Z_to_bv 64 (Z.of_nat j))]) ->
  thread_cells m tp TSD CTX T ->
  rw_cells bsegs m (T + 2840) [C8 (Z_to_bv 64 rf); C8 (Z_to_bv 64 rfd)] ->
  (forall m' (t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
     mem_inv bsegs m' -> stk bsegs m' lo usp -> munch qsW m m' -> wmono bsegs m m' ->
     rw_cells bsegs m' 0xaaf78 [C8 (Z_to_bv 64 SB); C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 RI)] ->
     rw_cells bsegs m' cb [C4 (Z_to_bv 64 (3 + 256 * hk)); C4 (Z_to_bv 64 nlo); C8 aidw] ->
     rw_cells bsegs m' 0xaaf98 [C8 (Z_to_bv 64 4096); C8 (Z_to_bv 64 PA)] ->
     rw_cells bsegs m' 0xaafc8 [C8 (Z_to_bv 64 ptrc); C8 (Z_to_bv 64 (Z.of_nat (length cs))); C1 (Z_to_bv 8 0)] ->
     rw_cells bsegs m' 0xab200 [C4 (Z_to_bv 64 0)] ->
     u64arr bsegs m' PA (gws cs junk) ->
     (forall j c', nth_error cs j = Some c' -> exists nd, rw_cells bsegs m' (fst c') [C8 (Z_to_bv 64 (fst c')); C8 (Z_to_bv 64 (snd c')); C8 nd; C8 (Z_to_bv 64 (Z.of_nat j))]) ->
     thread_cells m' tp TSD CTX T ->
     rw_cells bsegs m' (T + 2840) [C8 (Z_to_bv 64 (rf + 1)); C8 (Z_to_bv 64 (n + rfd))] ->
     evtA bsegs P Q (MS (mkR ra (Z_to_bv 64 usp) gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0xaaf98) (Z_to_bv 64 0xab208) (Z_to_bv 64 bb) a3' a4' a5' a6' a7'
                             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x35230) fc None m' (seg_rom bsegs))) ->
  evtA bsegs P Q (MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 CBP) (Z_to_bv 64 cb) a2 a3 a4 a5 a6 a7
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x34c64) fc None m (seg_rom bsegs)).
Proof. aceil.
  intros m MI SK INS HDR SEC NRS MTX ARR HDRS TC TST CONT.
  pose proof LOC as LOC0. aceil. pose proof HSB as HSB0. pose proof HCBS as HCBS0. pose proof HBBS as HBBS0.
  unfold kSpaceSize in HSB0, HCBS0, HBBS0.
  pose proof (placed_s_num _ _ HTR ltac:(clear; lia)) as (TQ1 & TQ2 & TQ3 & TQ4). clear TQ4.
  assert (HTb : T + 4096 <= alloc_ceiling) by (destruct HTR as (_ & X & _); exact X).
  pose proof HCX as (CQ1 & CQ2 & CQ3 & CQ4 & CQ5).
  assert (HKR : 0 <= hk < 2^16) by (unfold hk; lia).
  assert (Hn0 : 0 <= n < 2^40) by (unfold n; lia).
  assert (LEN : (length (gws cs junk) = length cs + length junk)%nat) by (unfold gws; rewrite length_app, length_map; reflexivity).
  (* [comment removed for export] *)
  pose proof (hide _ INS) as INS0. pose proof (hide _ HDR) as HDR0. pose proof (hide _ SEC) as SEC0. pose proof (hide _ NRS) as NRS0.
  pose proof (hide _ ARR) as ARR0. pose proof (hide _ TC) as TC0.
  destruct TC as (TC1 & TC2 & TC3 & TC4 & TC5).
  assert (MU : munch qsW m m) by apply munch_refl.
  assert (WM : wmono bsegs m m) by apply wmono_refl.
  carve_frame 48%nat SK.
  frame_stores 7 FR. (* [comment removed for export] *)
  do 2 zstepA. (* [comment removed for export] *)
  do 2 zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  do 2 zstepA. (* [comment removed for export] *)
  (* [comment removed for export] *)
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m1 end.
  set (CALL := fun ms1 => exists (a1x : word), ms1 = MS (mkR ra (Z_to_bv 64 (usp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 CBP) (Z_to_bv 64 cb) (Z_to_bv 64 SB) a1x a2 a3 a4 a5 a6 a7
                                  s2 (Z_to_bv 64 700248) (Z_to_bv 64 137438953472) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x34cd0) fc None m1 (seg_rom bsegs)).
  assert (KCALL : forall ms1, CALL ms1 -> evtA bsegs P Q ms1).
  2:{ zstepA. if_cases K1; zify_cond K1.
      - eapply KCALL. eexists. reflexivity.
      - zstepA. (* [comment removed for export] *)
        zstepA. if_cases K2; zify_cond K2.
        + eapply KCALL. eexists. reflexivity.
        + exfalso. revert K1 K2. rewrite ?unsigned_lit by lia. clear -CEILB HCBS0 HSB0 HCB. intros K1 K2. lia. }
  intros ms1 (a1x & ->). try clear CALL.
  (* [comment removed for export] *)
  lazymatch goal with NRS1 : rw_cells bsegs m1 0xaafc8 _ |- _ =>
    pose proof (rw_cells_app_split5 bsegs m1 0xaafc8 [C8 (Z_to_bv 64 ptrc)] [C8 (Z_to_bv 64 (Z.of_nat (length cs))); C1 (Z_to_bv 8 0)] NRS1) as [_ NCH2] end.
  pose proof (rw_cells_app_split5 bsegs m1 _ [C8 (Z_to_bv 64 (Z.of_nat (length cs)))] [C1 (Z_to_bv 8 0)] NCH2) as [NCH _]. clear NCH2.
  lazymatch type of NCH with rw_cells _ _ ?x _ => replace x with 0xaafd0 in NCH by (cbn; lia) end.
  assert (HDRS1 : forall j c', nth_error cs j = Some c' -> exists w3 w4, rw_cells bsegs m1 (fst c') [C8 (Z_to_bv 64 (fst c')); C8 (Z_to_bv 64 (snd c')); C8 w3; C8 w4]).
  { intros j c' Hj. destruct (HDRS j c' Hj) as [nd HD]. exists nd, (Z_to_bv 64 (Z.of_nat j)).
    pose proof (proj1 (Forall_forall _ _) RNG _ (nth_error_In _ _ Hj)) as (Q1' & Q2' & Q3' & Q4'). pose proof (HTL _ _ Hj) as Q5'. aceil.
    eapply rw_cells_transport; [exact HD| exact MU| exact WM| cbn; clear -CEILB Q1' Q3' Q4' Q5' LOC LO TQ1; repeat split; try exact I; lia]. }
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  lazymatch goal with SEC1 : rw_cells bsegs m1 0xaaf98 _, MTX1 : rw_cells bsegs m1 0xab200 _, ARR1 : u64arr bsegs m1 PA _ |- _ =>
  eapply (gbb_walk P _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 lo cb PA cs junk);
    [ rewrite unsigned_lit by lia; exact SK| exact LOC0| rewrite unsigned_lit by lia; lia| rewrite unsigned_lit by lia; lia| exact MI
    | aceil; lia| exact SEC1| exact NCH| exact MTX1| exact ARR1| exact HPA| exact HDRS1| exact RNG
    | rewrite unsigned_lit by lia; intros; apply PSTK; lia| exact PDAT| exact PARR| exact PHDR|];
  clear NCH HDRS1 MTX1 end.
  clear MI SK. intros m2 a1' a2' a3' a4' a5' a6' a7' t0' MI SK WMc MUc MTX2.
  rewrite !unsigned_lit in MUc, SK by lia.
  after_call m1 m2 MUc WMc. ret_pc_lit.
  rewrite <- HBB.
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  (* [comment removed for export] *)
  set (STATS := fun ms1 => ms1 = MS (mkR (Z_to_bv 64 0x34cdc) (Z_to_bv 64 (usp + -48)) gp tp t0' t1 t2 (Z_to_bv 64 CBP) (Z_to_bv 64 cb) (Z_to_bv 64 SB) (Z_to_bv 64 (SB + 137438953472)) a2' a3' a4' a5' a6' a7'
                                  (Z_to_bv 64 bb) (Z_to_bv 64 700248) (Z_to_bv 64 137438953472) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x34dd0) fc None m2 (seg_rom bsegs)).
  assert (KSTATS : forall ms1, STATS ms1 -> evtA bsegs P Q ms1).
  2:{ zstepA. if_cases K1; zify_cond K1.
      - zstepA. if_cases K2; zify_cond K2.
        + eapply KSTATS. reflexivity.
        + exfalso. revert K1 K2. rewrite ?unsigned_lit by lia. clear -CEILB HBBS0 HSB0. intros K1 K2. lia.
      - zstepA. (* [comment removed for export] *) eapply KSTATS. reflexivity. }
  intros ms1 ->. try clear STATS.
  zstepA. (* [comment removed for export] *)
  eapply evtA_cut.
  { eapply (gcts_walk P _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo TSD CTX T);
      [rewrite unsigned_lit by lia; exact SK| exact LOC0| rewrite unsigned_lit by lia; lia| rewrite unsigned_lit by lia; lia| exact MI
      | exact (conj TC1 (conj TC2 (conj TC3 (conj TC4 TC5))))| lia| exact HT2| lia| aceil; lia| lia| lia
      | rewrite unsigned_lit by lia; intros; apply PSTK; lia| exact PDAT| exact PCTX]. }
  cbv beta. intros ms' POST. unfold gcts_post in POST. destruct POST as (a1'' & m3 & -> & MUc & WMc & MI' & SK').
  rewrite !unsigned_lit in MUc, SK' by lia.
  clear MI SK. after_call m2 m3 MUc WMc. ret_pc_lit.
  (* [comment removed for export] *)
  lazymatch goal with HDR3 : rw_cells bsegs m3 cb _ |- _ =>
  assert (HDRB : rw_cells bsegs m3 cb [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 nhi); C4 (Z_to_bv 64 nlo); C8 aidw]);
  [ generalize HDR3; clear -CEILB HB1 HNHI HNLO HKR; intros HDR3;   (* [comment removed for export] *)
    eapply rw_cells_reshape; [| | exact HDR3]; [cells_wf_triv|];
    cbn [cells_bytes cbytes map app]; unfold le4, le2; rewrite !Z_to_bv_unsigned; cbn [Z_to_le_bytes map app];
    rewrite !Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 8) with 256; change (bv_modulus 64) with (2^64);
    unfold hk; rewrite !Z.shiftr_div_pow2 by lia; change (2^8) with 256; rewrite ?app_nil_r;
    rewrite !(Z.mod_small _ (2^64)) by lia;
    repeat (apply f_equal2; [Z.div_mod_to_equations; lia|]); reflexivity
  | clear HDR3 ] end.
  zstepA. (* [comment removed for export] *) rewrite fzx16_small by lia.
  zstepA. (* [comment removed for export] *) rewrite fzx32_small' by lia.
  zstepA. zstepA. (* [comment removed for export] *)
  zstepA. zstepA. (* [comment removed for export] *)
  replace (Z.shiftl nhi 32 mod 18446744073709551616) with (Z.shiftl nhi 32) by (symmetry; apply Z.mod_small; rewrite Z.shiftl_mul_pow2 by lia; lia).
  rewrite (lor_shiftl nhi nlo 32) by lia. fold n.
  zstepA. zstepA. (* [comment removed for export] *)
  (* [comment removed for export] *)
  clear HDRB.
  repeat match goal with H : rw_cells bsegs m3 ?a _ |- _ =>
    lazymatch a with usp + -48 => fail | T + 2840 => fail | 700928 => fail | _ => clear H end end.
  repeat match goal with H : u64arr bsegs m3 _ _ |- _ => clear H end.
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  zstepA. if_cases K1; zify_cond K1. { exfalso. revert K1. rewrite ?unsigned_lit by lia. clear -CEILB HBBS0. intros K1. lia. } clear K1. (* [comment removed for export] *)
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m4 end.
  assert (INS4 : rw_cells bsegs m4 0xaaf78 [C8 (Z_to_bv 64 SB); C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 RI)]).
  { pose proof INS0 as X. apply unhide in X. eapply rw_cells_transport; [exact X| exact MU| exact WM| cbn; clear -CEILB LOC LO TQ1 TQ3; repeat split; try exact I; dlia1]. }
  zstepA. (* [comment removed for export] *)
  (* [comment removed for export] *)
  set (TAIL := fun ms1 => exists (s4x : word), ms1 = MS (mkR (Z_to_bv 64 0x34dd4) (Z_to_bv 64 (usp + -48)) gp tp t0' t1 t2 (Z_to_bv 64 CBP) (Z_to_bv 64 cb)
                                  (Z_to_bv 64 (T + 2800)) (Z_to_bv 64 SB) (Z_to_bv 64 nlo) (Z_to_bv 64 rfd) (Z_to_bv 64 (rf + 1)) a5' a6' a7'
                                  (Z_to_bv 64 bb) (Z_to_bv 64 700248) s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x34e6c) fc None m4 (seg_rom bsegs)).
  assert (KTAIL : forall ms1, TAIL ms1 -> evtA bsegs P Q ms1).
  2:{ zstepA. if_cases K2; zify_cond K2.
      - eapply KTAIL. eexists. reflexivity.
      - zstepA. (* [comment removed for export] *)
        zstepA. if_cases K3; zify_cond K3.
        + eapply KTAIL. eexists. reflexivity.
        + exfalso. revert K2 K3. rewrite ?unsigned_lit by lia. clear -CEILB HBBS0 HSB0. intros K2 K3. lia. }
  intros ms1 (s4x & ->). try clear TAIL.
  zstepA. zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  do 7 zstepA. (* [comment removed for export] *)
  release_frame FR SK' usp.
  zstepA. (* [comment removed for export] *)
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m5 end.
  match goal with H : rw_cells bsegs m5 (T + 2840) _ |- _ => rename H into TST' end.
  match goal with H : rw_cells bsegs m5 0xab200 _ |- _ => rename H into MTX5 end.
  (* [comment removed for export] *)
  apply unhide in INS0. apply unhide in HDR0. apply unhide in SEC0. apply unhide in NRS0. apply unhide in ARR0. apply unhide in TC0.
  destruct TC0 as (TZ1 & TZ2 & TZ3 & TZ4 & TZ5).
  Ltac reissue H0 MU WM := eapply rw_cells_transport; [exact H0| exact MU| exact WM| cbn; repeat split; try exact I; dlia1].
  eapply CONT; [exact MI'| exact SK'| exact MU| exact WM| reissue INS0 MU WM| reissue HDR0 MU WM| reissue SEC0 MU WM| reissue NRS0 MU WM| exact MTX5| | | | exact TST'].
  - eapply u64arr_transport; [exact ARR0| exact MU| exact WM|]. rewrite LEN, Nat2Z.inj_add. cbn [disjoint_from]. clear -CEILB HPA HTPA LOC LO TQ1 TQ3. repeat split; try exact I; dlia1.
  - intros j c' Hj. destruct (HDRS j c' Hj) as [nd HD]. exists nd.
    pose proof (proj1 (Forall_forall _ _) RNG _ (nth_error_In _ _ Hj)) as (Q1' & Q2' & Q3' & Q4'). pose proof (HTL _ _ Hj) as Q5'. aceil.
    eapply rw_cells_transport; [exact HD| exact MU| exact WM| cbn; clear -CEILB Q1' Q3' Q4' Q5' LOC LO TQ1; repeat split; try exact I; lia].
  - split; [reissue TZ1 MU WM|]. split; [reissue TZ2 MU WM|]. split; [reissue TZ3 MU WM|]. split; [reissue TZ4 MU WM| reissue TZ5 MU WM].
Qed.
End QCBS.
End RC__1.
