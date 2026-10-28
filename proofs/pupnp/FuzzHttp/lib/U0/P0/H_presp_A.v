(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From stdpp Require Import base list.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Arr.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac CellConv.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs H_scanner_get_token H_vfmatch_A H_vfmatch_F H_vfmatch_G1 H_match H_membuffer_assign.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import HU_list_kit.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Ceiling.
Import ListNotations.
Open Scope Z_scope.
Set Printing Width 1000.
Set Printing Depth 100.

Definition parse_responseline_entry := 0x14904%Z.
Notation FMT_RESP := 0x10646%Z.
Notation FMT_STATUS := 0x105b3%Z.
Notation SSCANF_E := 0x1b1d0%Z.
Ltac sstep := step; fix_lit_store.
Ltac rl_b2z :=
  repeat match goal with |- context [Z.b2z (?a <? ?b)] =>
    first [ replace (a <? b) with true by (symmetry; apply Z.ltb_lt; lia) | replace (a <? b) with false by (symmetry; apply Z.ltb_ge; lia) ] end;
  cbn [Z.b2z]; change (Z.lxor 1 0) with 1%Z; change (Z.lxor 0 1) with 1%Z; change (Z.lxor 1 1) with 0%Z; change (Z.lxor 0 0) with 0%Z.

Definition rlFS (ra s0 s1 s2 s3 s4 : word) : list cell := [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Notation SCc S MB cur := ([C8 (wz MB); C8 (wz cur); C4 (wz 0)]).

Lemma tokm1 : forall ty, (0 <= ty <= 5)%Z ->
  (ty = 0 /\ Z.land (bv_swrap 32 (ty + -1)) 18446744073709551615 = 2^64 - 1)%Z
  \/ (1 <= ty /\ Z.land (bv_swrap 32 (ty + -1)) 18446744073709551615 = ty - 1)%Z.
Proof.
  intros ty H. rewrite swrap32_id by lia. change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_ones by lia.
  destruct (Z.eq_dec ty 0) as [->|NE]; [left; split; [reflexivity| reflexivity] | right]. split; [lia|]. apply Z.mod_small. lia.
Qed.

Lemma land64_neg : forall x, (-2^63 <= x < 0)%Z -> Z.land x 18446744073709551615 = (x + 2^64)%Z.
Proof.
  intros x H. change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_ones by lia.
  rewrite <- (Z.mod_add x 1 (2^64)) by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma land64_nonneg : forall x, (0 <= x < 2^64)%Z -> Z.land x 18446744073709551615 = x.
Proof. intros x H. change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.
Ltac killK K := exfalso; revert K; try (change 18446744073709551615%Z with (Z.ones 64); rewrite Z.land_ones by lia);
  first [ lia | rewrite Z.mod_small by lia; lia | rewrite <- (Z.mod_add _ 1 (2^64)) by lia; rewrite Z.mod_small by lia; lia ].
Ltac sgn K x := first [ rewrite (land64_neg x) in K by lia | rewrite (land64_nonneg x) in K by lia ].
Ltac rl_ub := first [ ubr | (let KU := fresh "KU" in if_cases KU; zify_cond KU; [killK KU | try clear KU]) ].

Definition bdig (bs : list byte) (t : Z) : Prop := exists b, nth_error bs (Z.to_nat t) = Some b /\ (48 <= bv_unsigned b <= 57)%Z.
Definition bndig (bs : list byte) (t : Z) : Prop := exists b, nth_error bs (Z.to_nat t) = Some b /\ (bv_unsigned b < 48 \/ 57 < bv_unsigned b)%Z.
Definition bblank (b : byte) : Prop := (bv_unsigned b = 32 \/ bv_unsigned b = 9)%Z.
Lemma byte_range : forall b : byte, (0 <= bv_unsigned b < 256)%Z.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R. lia. Qed.

Section SEGS.
Context {HCEIL : HasCeiling}.
  Variables (P q lo : Z).
  Notation S := (P + 480)%Z.
  Notation MB := (P + 400)%Z.
  Hypothesis QLO : (lo <= q)%Z.
  Hypothesis LO0 : (0x5d000 <= lo)%Z.
  Hypothesis QP : (q + 80 <= P)%Z.
  Hypothesis PHI : (P + 504 < 2^63)%Z.

  Definition rlFX (m : mem) : Prop :=
    (exists j0, rw_cells rsegs m q [CB 12 j0]) /\ (exists ty, rw_cells rsegs m (q + 12) [C4 ty])
    /\ (exists a b, rw_cells rsegs m (q + 16) [C8 a; C8 b]).

  #[using="QLO LO0 QP PHI"] Lemma rl_entry : forall (cur : Z) ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc m,
    stk rsegs m lo (q + 80) -> mem_inv rsegs m ->
    rw_cells rsegs m S (SCc S MB cur) -> (0 <= cur < 2^64)%Z -> (P mod 8 = 0)%Z ->
    evt rsegs (fun ms' => exists m' (j0 : list byte) (ty : word) (a b : word) (a0' : word),
        ms' = MS (mkR ra (wz q) gp tp t0 t1 t2 (wz P) (wz S) a0' a1 a2 a3 a4 a5 a6 a7 (wz 4) (wz 2) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (wz 0x1493c) fc None m' (seg_rom rsegs)
        /\ munch [(q, q + 80)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
        /\ stk rsegs m' lo q
        /\ rw_cells rsegs m' q [CB 12 j0] /\ rw_cells rsegs m' (q + 12) [C4 ty] /\ rw_cells rsegs m' (q + 16) [C8 a; C8 b]
        /\ rw_cells rsegs m' (q + 32) (rlFS ra s0 s1 s2 s3 s4)
        /\ rw_cells rsegs m' S (SCc S MB cur))
      (MS (mkR ra (wz (q + 80)) gp tp t0 t1 t2 s0 s1 (wz P) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz parse_responseline_entry) fc None m (seg_rom rsegs)).
  Proof.
    intros until m. intros ST MI SC CUR PAL. unfold parse_responseline_entry.
    pose proof (munch_refl [(q, q + 80)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
    assert (E : bv_unsigned (wz (q + 80)) = q + 80) by (apply unsigned_lit; lia).
    rewrite <- E in ST. carve_frame 80%nat ST. rewrite !E in *.
    replace (q + 80 + -80)%Z with q in FR by lia. replace (q + 80 + -80)%Z with q in ST by lia.
    do 7 sstep. ub_null. zstep. ub_align. zstep. zstep. zstep.
    name_junk FR. splitcb FR 0%nat [12; 4; 16]%nat. name_junk FR.
    recell FR 1%nat. splitcb FR 2%nat [8; 8]%nat. recell FR 2%nat. recell FR 3%nat.
    split_chunk FR 1%nat Q0 R1. split_chunk R1 1%nat Q12 R2. split_chunk R2 2%nat Q16 FSH.
    apply evt_done. eexists _, _, _, _, _, _. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
    split; [exact Q0|]. split; [exact Q12|]. split; [exact Q16|]. split; [exact FSH| exact SC].
  Qed.

  Notation PRS pc x1 t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 gp tp F fc m :=
    (MS (mkR x1 (wz q) gp tp t0 t1 t2 (wz P) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz pc) fc None m (seg_rom rsegs)).

  #[using="Type"] Lemma rl_head : forall gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 (F : bvmap 5 word) fc m,
    evt rsegs (fun ms' => ms' = PRS sgt_entry (wz 0x1494c) t0 t1 t2 (wz S) (wz S) (wz (q + 16)) (wz (q + 12)) a3 a4 a5 a6 a7 (wz 4) (wz 2) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 gp tp F fc m)
      (PRS 0x1493c x1 t0 t1 t2 (wz S) a0 a1 a2 a3 a4 a5 a6 a7 (wz 4) (wz 2) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 gp tp F fc m).
  Proof.
    intros until m. unfold sgt_entry. pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    zstep. zstep. zstep. zstep. apply evt_done. reflexivity.
  Qed.

  #[using="Type"] Lemma rl_h2 : forall (r ty : Z) (tyw : word) gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 (F : bvmap 5 word) fc m,
    mem_inv rsegs m -> rw_cells rsegs m (q + 12) [C4 tyw] -> (0 <= r <= 5)%Z -> (r = 4 -> tyw = wz ty /\ 0 <= ty <= 5)%Z ->
    evt rsegs (fun ms' =>
        (r <> 4 /\ ms' = PRS 0x14bf0 x1 t0 t1 t2 (wz S) (wz r) a1 a2 a3 a4 a5 a6 a7 (wz 4) (wz 2) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 gp tp F fc m)
        \/ (r = 4 /\ (ty = 1 \/ ty = 2) /\ exists a0', ms' = PRS 0x1493c x1 t0 t1 t2 (wz S) a0' a1 a2 a3 a4 a5 a6 a7 (wz 4) (wz 2) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 gp tp F fc m)
        \/ (r = 4 /\ ty <> 1 /\ ty <> 2 /\ exists a0', ms' = PRS 0x1495c x1 t0 t1 t2 (wz S) a0' a1 a2 a3 a4 a5 a6 a7 (wz 4) (wz 2) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 gp tp F fc m))
      (PRS 0x1494c x1 t0 t1 t2 (wz S) (wz r) a1 a2 a3 a4 a5 a6 a7 (wz 4) (wz 2) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 gp tp F fc m).
  Proof.
    intros until m. intros MI TYC RR TYR. pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    zstep. if_cases K; zify_cond K; condn K.
    - apply evt_done. left. split; [lia| reflexivity].
    - destruct (TYR ltac:(lia)) as [-> TYR']. zstep. rewrite (sx32_lit ty) by lia. zstep. zstep. if_cases K2; zify_cond K2; condn K2.
      + destruct (tokm1 ty TYR') as [[? EE]|[? EE]]; rewrite EE in K2; [lia|]. apply evt_done. right. left. split; [lia|]. split; [lia|]. eexists. reflexivity.
      + destruct (tokm1 ty TYR') as [[? EE]|[? EE]]; rewrite EE in K2. all: apply evt_done; right; right; split; [lia|]; split; [lia|]; split; [lia|]; eexists; reflexivity.
  Qed.

  #[using="QP PHI"] Lemma rl_pb : forall (tlz cur1 : Z) (tb : word) gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 (F : bvmap 5 word) fc m,
    mem_inv rsegs m -> rw_cells rsegs m (q + 16) [C8 tb; C8 (wz tlz)] -> rw_cells rsegs m S (SCc S MB cur1) ->
    (0 <= tlz <= cur1)%Z -> (cur1 < 2^63)%Z ->
    evt rsegs (fun ms' => exists m',
        ms' = PRS match_entry (wz 0x14980) t0 t1 t2 (wz S) (wz S) (wz FMT_RESP) (wz (q + 16)) a3 a4 a5 a6 a7 (wz 4) (wz 2) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 gp tp F fc m'
        /\ munch [(P + 488, P + 496)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
        /\ rw_cells rsegs m' (q + 16) [C8 tb; C8 (wz tlz)] /\ rw_cells rsegs m' S (SCc S MB (cur1 - tlz)))
      (PRS 0x1495c x1 t0 t1 t2 (wz S) a0 a1 a2 a3 a4 a5 a6 a7 (wz 4) (wz 2) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 gp tp F fc m).
  Proof.
    intros until m. intros MI Q16 SC TL CH. unfold match_entry.
    pose proof (munch_refl [(P + 488, P + 496)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
    zstep. zstep. zstep.
    sstep. zstep. zstep. zstep. zstep. zstep.
    apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact Q16| exact SC].
  Qed.

  #[using="Type"] Lemma rl_m2 : forall (r : Z) gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 (F : bvmap 5 word) fc m,
    (0 <= r <= 5)%Z ->
    evt rsegs (fun ms' =>
        (r <> 4 /\ ms' = PRS 0x14bf0 x1 t0 t1 t2 (wz S) (wz r) (wz 4) a2 a3 a4 a5 a6 a7 (wz 4) (wz 2) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 gp tp F fc m)
        \/ (r = 4 /\ ms' = PRS 0x14988 x1 t0 t1 t2 (wz S) (wz r) (wz 4) a2 a3 a4 a5 a6 a7 (wz 4) (wz 2) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 gp tp F fc m))
      (PRS 0x14980 x1 t0 t1 t2 (wz S) (wz r) a1 a2 a3 a4 a5 a6 a7 (wz 4) (wz 2) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 gp tp F fc m).
  Proof.
    intros until m. intros RR. pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    zstep. zstep. if_cases K; zify_cond K; condn K.
    - apply evt_done. left. split; [lia| reflexivity].
    - apply evt_done. right. split; [lia| reflexivity].
  Qed.

  #[using="QLO QP PHI"] Lemma rl_nul : forall (A o l : Z) (n : nat) (bs : list byte) gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 (F : bvmap 5 word) fc m,
    mem_inv rsegs m -> rw_cells rsegs m (q + 16) [C8 (wz (A + o)); C8 (wz l)] -> rw_cells rsegs m A [CB n bs] ->
    (0 <= o)%Z -> (0 <= l)%Z -> (o + l + 1 < Z.of_nat n)%Z -> (0 < A)%Z -> (A + Z.of_nat n <= lo)%Z ->
    evt rsegs (fun ms' => exists m' (b : byte), nth_error bs (Z.to_nat (o + l)) = Some b /\
        ms' = PRS SSCANF_E (wz 0x149dc) t0 t1 t2 (wz (P + 228)) (wz (A + o)) (wz FMT_STATUS) (wz (P + 276)) (wz (P + 280)) (wz (P + 228)) a5 a6 a7 (wz (P + 280)) (wz (P + 276)) (wz (bv_unsigned b)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 gp tp F fc m'
        /\ munch [(A + (o + l), A + (o + l) + 1)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
        /\ rw_cells rsegs m' (q + 16) [C8 (wz (A + o)); C8 (wz l)]
        /\ rw_cells rsegs m' A [CB n (firstn (Z.to_nat (o + l)) bs ++ [Z_to_bv 8 0] ++ skipn (Z.to_nat (o + l) + 1) bs)])
      (PRS 0x14988 x1 t0 t1 t2 (wz S) a0 a1 a2 a3 a4 a5 a6 a7 (wz 4) (wz 2) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 gp tp F fc m).
  Proof.
    intros until m. intros MI Q16 BLK O0 L0 KN A0 AHI.
    pose proof (munch_refl [(A + (o + l), A + (o + l) + 1)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
    assert (LBS : length bs = n) by (destruct BLK as [[W _] _]; cbn in W; LiaTuning.ctauto).
    destruct (nth_error bs (Z.to_nat (o + l))) as [b|] eqn:Hb. 2:{ exfalso. apply nth_error_None in Hb. lia. }

    apply (rw_cells_split_CB rsegs m A [] n bs [] [Z.to_nat (o + l); 1%nat; Z.to_nat (Z.of_nat n - (o + l) - 1)]) in BLK; [| cbn; lia].
    cbn [app mk_CB_cells] in BLK.
    lazymatch type of BLK with rw_cells _ _ _ [?c1; ?c2; ?c3] =>
      destruct (proj1 (rw_cells_app rsegs m A [c1] [c2; c3]) BLK) as [BLK1 BLK23] end. clear BLK.
    cbn [cells_size csize] in BLK23. rewrite Nat.add_0_r, Z2Nat.id in BLK23 by lia.
    assert (E1 : firstn 1 (skipn (Z.to_nat (o + l)) bs) = [b]).
    { destruct (nth_error_split _ _ _ Hb) as (pre & post & E & Hlen). rewrite E at 1. rewrite skipn_app, skipn_all2, Hlen, Nat.sub_diag by lia. reflexivity. }
    rewrite E1 in BLK23.
    zstep. zstep. zstep.
    step. ubr.
    zstep. zstep. zstep.
    step. first [ (rl_b2z; lit_branch) | ubr ].
    step. ubr.
    remember (A + (o + l))%Z as V eqn:EV.
    replace (wz (A + o + l)) with (wz V) by (f_equal; lia).
    zstep. sstep. subst V.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.

    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (BLK : rw_cells rsegs mm A [CB n (firstn (Z.to_nat (o + l)) bs ++ [Z_to_bv 8 0] ++ skipn (Z.to_nat (o + l) + 1) bs)]) end.
    { lazymatch type of BLK23 with rw_cells _ ?mm _ [?c2; ?c3] =>
        pose proof (proj2 (rw_cells_app rsegs mm A [CB (Z.to_nat (o + l)) (firstn (Z.to_nat (o + l)) bs)] [c2; c3])) as J;
        cbn [cells_size csize Nat.add] in J; rewrite Nat.add_0_r, Z2Nat.id in J by lia;
        specialize (J (conj BLK1 BLK23)); cbn [app] in J;
        pose proof (rw_cells_merge rsegs mm A [] [CB (Z.to_nat (o + l)) (firstn (Z.to_nat (o + l)) bs); c2; c3] []) as M
      end.
      rewrite !app_nil_r in M. cbn [app cells_size csize cells_bytes cbytes Nat.add] in M.
      replace (Z.to_nat (o + l) + Datatypes.S (Z.to_nat (Z.of_nat n - (o + l) - 1) + 0))%nat with n in M by lia.
      replace (firstn (Z.to_nat (Z.of_nat n - (o + l) - 1)) (skipn 1 (skipn (Z.to_nat (o + l)) bs))) with (skipn (Z.to_nat (o + l) + 1) bs) in *.
      2:{ rewrite skipn_skipn. replace (1 + Z.to_nat (o + l))%nat with (Z.to_nat (o + l) + 1)%nat by lia. symmetry. apply firstn_all2. rewrite length_skipn. lia. }
      pose proof (M J) as MJ. rewrite app_nil_r in MJ. exact MJ. }
    clear BLK1 BLK23.
    apply evt_done. eexists _, b. split; [reflexivity|]. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact Q16| exact BLK].
  Qed.

  #[using="QLO QP PHI"] Lemma rl_chk : forall (r A o l maj min sc : Z) (n : nat) (bs : list byte) (b : byte)
      gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 (F : bvmap 5 word) fc m,
    mem_inv rsegs m -> rw_cells rsegs m (q + 16) [C8 (wz (A + o)); C8 (wz l)] -> rw_cells rsegs m A [CB n bs] ->
    rw_cells rsegs m (P + 276) [C4 (wz maj)] -> rw_cells rsegs m (P + 280) [C4 (wz min)] -> rw_cells rsegs m (P + 228) [C4 (wz sc)] ->
    (- 2^31 <= maj < 2^31)%Z -> (- 2^31 <= min < 2^31)%Z -> (- 2^31 <= sc < 2^31)%Z -> (r = -1 \/ 0 <= r <= 3)%Z ->
    (0 <= o)%Z -> (0 <= l)%Z -> (o + l + 1 < Z.of_nat n)%Z -> (0 < A)%Z -> (A + Z.of_nat n <= lo)%Z ->
    evt rsegs (fun ms' => exists m' (a1' a2' a3' a4' : word),
        munch [(A + (o + l), A + (o + l) + 1)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
        /\ rw_cells rsegs m' (q + 16) [C8 (wz (A + o)); C8 (wz l)]
        /\ rw_cells rsegs m' A [CB n (firstn (Z.to_nat (o + l)) bs ++ [b] ++ skipn (Z.to_nat (o + l) + 1) bs)]
        /\ rw_cells rsegs m' (P + 276) [C4 (wz maj)] /\ rw_cells rsegs m' (P + 280) [C4 (wz min)] /\ rw_cells rsegs m' (P + 228) [C4 (wz sc)]
        /\ ( ((r <> 3 \/ maj < 0 \/ min < 0 \/ sc < 0)%Z
               /\ ms' = PRS 0x14bf0 x1 t0 t1 t2 (wz (P + 228)) (wz 3) a1' a2' a3' a4' a5 a6 a7 (wz (P + 280)) (wz (P + 276)) (wz (bv_unsigned b)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 gp tp F fc m')
           \/ ((r = 3 /\ 0 <= maj /\ 0 <= min /\ 0 <= sc)%Z
               /\ ms' = PRS 0x14a28 x1 t0 t1 t2 (wz (P + 228)) (wz 3) a1' a2' a3' a4' a5 a6 a7 (wz (P + 280)) (wz (P + 276)) (wz (bv_unsigned b)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 gp tp F fc m') ))
      (PRS 0x149dc x1 t0 t1 t2 (wz (P + 228)) (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 (wz (P + 280)) (wz (P + 276)) (wz (bv_unsigned b)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 gp tp F fc m).
  Proof.
    intros until m. intros MI Q16 BLK C1c C2c C3c MR NR SR RR O0 L0 KN A0 AHI.
    pose proof (munch_refl [(A + (o + l), A + (o + l) + 1)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
    pose proof (bv_unsigned_in_range 8 b) as BR. unfold bv_modulus in BR. cbn in BR.
    assert (LBS : length bs = n) by (destruct BLK as [[W _] _]; cbn in W; LiaTuning.ctauto).
    apply (rw_cells_split_CB rsegs m A [] n bs [] [Z.to_nat (o + l); 1%nat; Z.to_nat (Z.of_nat n - (o + l) - 1)]) in BLK; [| cbn; lia].
    cbn [app mk_CB_cells] in BLK.
    lazymatch type of BLK with rw_cells _ _ _ [?c1; ?c2; ?c3] =>
      destruct (proj1 (rw_cells_app rsegs m A [c1] [c2; c3]) BLK) as [BLK1 BLK23] end. clear BLK.
    cbn [cells_size csize] in BLK23. rewrite Nat.add_0_r, Z2Nat.id in BLK23 by lia.
    zstep. zstep. zstep.
    step. ubr.
    zstep. zstep. zstep. zstep.
    step. first [ (rl_b2z; lit_branch) | ubr ].
    step. ubr.
    remember (A + (o + l))%Z as V eqn:EV.
    replace (wz (A + o + l)) with (wz V) by (f_equal; lia).
    zstep.
    step. change (Z_to_bv 64 (bv_unsigned b)) with (zxb b). rewrite le1_zxb. mem_after_store. subst V.

    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (BLK : rw_cells rsegs mm A [CB n (firstn (Z.to_nat (o + l)) bs ++ [b] ++ skipn (Z.to_nat (o + l) + 1) bs)]) end.
    { lazymatch type of BLK23 with rw_cells _ ?mm _ [?c2; ?c3] =>
        pose proof (proj2 (rw_cells_app rsegs mm A [CB (Z.to_nat (o + l)) (firstn (Z.to_nat (o + l)) bs)] [c2; c3])) as J;
        cbn [cells_size csize Nat.add] in J; rewrite Nat.add_0_r, Z2Nat.id in J by lia;
        specialize (J (conj BLK1 BLK23)); cbn [app] in J;
        pose proof (rw_cells_merge rsegs mm A [] [CB (Z.to_nat (o + l)) (firstn (Z.to_nat (o + l)) bs); c2; c3] []) as M
      end.
      rewrite !app_nil_r in M. cbn [app cells_size csize cells_bytes cbytes Nat.add] in M.
      replace (Z.to_nat (o + l) + Datatypes.S (Z.to_nat (Z.of_nat n - (o + l) - 1) + 0))%nat with n in M by lia.
      replace (firstn (Z.to_nat (Z.of_nat n - (o + l) - 1)) (skipn 1 (skipn (Z.to_nat (o + l)) bs))) with (skipn (Z.to_nat (o + l) + 1) bs) in *.
      2:{ rewrite skipn_skipn. replace (1 + Z.to_nat (o + l))%nat with (Z.to_nat (o + l) + 1)%nat by lia. symmetry. apply firstn_all2. rewrite length_skipn. lia. }
      pose proof (M J) as MJ. rewrite app_nil_r in MJ. exact MJ. }
    clear BLK1 BLK23. unfold zxb.
    zstep. if_cases K; zify_cond K; condn K.
    { apply evt_done. eexists _, _, _, _, _. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact Q16|]. split; [exact BLK|].
      split; [exact C1c|]. split; [exact C2c|]. split; [exact C3c|]. left. split; [| reflexivity].
      left. intros ->. apply K. reflexivity. }
    assert (R3 : r = 3).
    { change 18446744073709551615%Z with (Z.ones 64) in K. rewrite Z.land_ones in K by lia.
      destruct RR as [->|RR']; [cbv in K; lia|]. rewrite Z.mod_small in K by lia. exact K. }
    subst r.
    zstep. rewrite (sx32_lit maj) by lia. zstep. if_cases K1; zify_cond K1.
    { apply evt_done. eexists _, _, _, _, _. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact Q16|]. split; [exact BLK|].
      split; [exact C1c|]. split; [exact C2c|]. split; [exact C3c|]. left. split; [| reflexivity]. destruct (Z.lt_ge_cases maj 0); [lia|]. sgn K1 maj. lia. }
    zstep. rewrite (sx32_lit min) by lia. zstep. if_cases K2; zify_cond K2.
    { apply evt_done. eexists _, _, _, _, _. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact Q16|]. split; [exact BLK|].
      split; [exact C1c|]. split; [exact C2c|]. split; [exact C3c|]. left. split; [| reflexivity]. destruct (Z.lt_ge_cases min 0); [lia|]. sgn K2 min. lia. }
    zstep. rewrite (sx32_lit sc) by lia. zstep. if_cases K3; zify_cond K3.
    { apply evt_done. eexists _, _, _, _, _. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact Q16|]. split; [exact BLK|].
      split; [exact C1c|]. split; [exact C2c|]. split; [exact C3c|]. left. split; [| reflexivity]. destruct (Z.lt_ge_cases sc 0); [lia|]. sgn K3 sc. lia. }
    apply evt_done. eexists _, _, _, _, _. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact Q16|]. split; [exact BLK|].
    split; [exact C1c|]. split; [exact C2c|]. split; [exact C3c|]. right. split; [| reflexivity].
    destruct (Z.lt_ge_cases maj 0); [sgn K1 maj; lia|]. destruct (Z.lt_ge_cases min 0); [sgn K2 min; lia|]. destruct (Z.lt_ge_cases sc 0); [sgn K3 sc; lia|]. lia.
  Qed.

  #[using="QLO"] Lemma rl_epi : forall ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      x1 x9 x18 x19 x20 (F : bvmap 5 word) fc m,
    stk rsegs m lo q -> mem_inv rsegs m -> rw_cells rsegs m (q + 32) (rlFS ra s0 s1 s2 s3 s4) -> rlFX m ->
    evt rsegs (fun ms' => ms' = MS (mkR ra (wz (q + 80)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                  F (ret_pc ra) fc None m (seg_rom rsegs)
                          /\ stk rsegs m lo (q + 80))
      (MS (mkR x1 (wz q) gp tp t0 t1 t2 (wz P) x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz 0x14bf0) fc None m (seg_rom rsegs)).
  Proof.
    intros until m. intros ST MI FSH FX. unfold rlFS in FSH.
    destruct FX as ([j0 Q0] & [ty Q12] & (a16 & b16 & Q16)).
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    do 6 zstep. zstep. zstep.
    eapply stk_release in Q0; [| exact ST| lia]. clear ST. release_all_ lo.
    apply evt_done. split; [reflexivity|]. lazymatch goal with H : stk rsegs m lo _ |- _ => exact H end.
  Qed.

  #[using="Type"] Lemma rl_U1 : forall (k : nat) (A t j pv : Z) (bs : list byte) gp tp t0 t1 t2 s1 a0 a1 a2 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 (F : bvmap 5 word) fc m,
    mem_inv rsegs m -> u8ro rsegs m A bs -> (j - t < Z.of_nat k)%Z -> (0 <= t < j)%Z -> pv = (A + t)%Z ->
    (forall u, (t < u < j)%Z -> bndig bs u) -> bdig bs j -> (0 < A)%Z -> (A + Z.of_nat (length bs) < 2^63)%Z ->
    evt rsegs (fun ms' => exists (b : byte) (pv' : Z), nth_error bs (Z.to_nat j) = Some b /\ pv' = (A + j)%Z /\
        ms' = PRS 0x14a68 x1 t0 t1 t2 s1 a0 (wz pv') a2 (wz (-1)) (wz (-10)) (wz pv') (wz (bv_unsigned b + -58)) a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 gp tp F fc m)
      (PRS 0x14a50 x1 t0 t1 t2 s1 a0 a1 a2 (wz (-1)) (wz (-10)) (wz pv) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 gp tp F fc m).
  Proof.
    induction k as [|k IH]; intros until m; intros MI BUF HK HTJ HP ND DJ A0 AHI; [lia|].
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    pose proof (bytes_at_bound _ _ _ _ BUF) as BB.
    assert (JL : (Z.to_nat j < length bs)%nat) by (destruct DJ as (bx & Hbx & _); exact (nth_error_lt _ _ _ Hbx)).
    step. rl_ub.
    destruct (Z.lt_ge_cases (t + 1) j) as [LT|GE].
    - destruct (ND (t + 1)%Z ltac:(lia)) as (b & Hb & NB). pose proof (byte_range b) as BR. pose proof (nth_error_lt _ _ _ Hb) as HL.
      pose proof (u8ro_read rsegs m A bs (t + 1) b (wa (A + (t + 1))) BUF Hb ltac:(lia) eq_refl) as RD.
      zstep. zstep. zstep. zstep. zstep. if_cases K; zify_cond K.
      + apply (IH A (t + 1)%Z j); try assumption; try lia. intros u Hu. apply ND. lia.
      + destruct NB as [NB|NB]; killK K.
    - assert (E : (t + 1 = j)%Z) by lia. destruct DJ as (b & Hb & DB). pose proof (byte_range b) as BR. pose proof (nth_error_lt _ _ _ Hb) as HL.
      pose proof (u8ro_read rsegs m A bs j b (wa (A + j)) BUF Hb ltac:(lia) eq_refl) as RD.
      zstep. zstep. zstep. zstep. zstep. if_cases K; zify_cond K.
      + killK K.
      + apply evt_done. eexists b, _. split; [exact Hb|]. split; [| reflexivity]. lia.
  Qed.

  #[using="Type"] Lemma rl_U2 : forall (k : nat) (A t e pv : Z) (bs : list byte) gp tp t0 t1 t2 s1 a0 a2 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 (F : bvmap 5 word) fc m,
    mem_inv rsegs m -> u8ro rsegs m A bs -> (e - t < Z.of_nat k)%Z -> (0 <= t < e)%Z -> pv = (A + t)%Z ->
    (forall u, (t < u < e)%Z -> bdig bs u) -> bndig bs e -> (0 < A)%Z -> (A + Z.of_nat (length bs) < 2^63)%Z ->
    evt rsegs (fun ms' => exists (b : byte) (pv' : Z), nth_error bs (Z.to_nat e) = Some b /\ pv' = (A + e)%Z /\
        ms' = PRS 0x14a98 x1 t0 t1 t2 s1 a0 (wz pv') a2 (wz pv') (wz (-1)) (wz 10) (wz (bv_unsigned b + -48)) a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 gp tp F fc m)
      (PRS 0x14a80 x1 t0 t1 t2 s1 a0 (wz pv) a2 a3 (wz (-1)) (wz 10) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 gp tp F fc m).
  Proof.
    induction k as [|k IH]; intros until m; intros MI BUF HK HTE HP DD NE A0 AHI; [lia|].
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    pose proof (bytes_at_bound _ _ _ _ BUF) as BB.
    assert (EL : (Z.to_nat e < length bs)%nat) by (destruct NE as (bx & Hbx & _); exact (nth_error_lt _ _ _ Hbx)).
    step. rl_ub.
    destruct (Z.lt_ge_cases (t + 1) e) as [LT|GE].
    - destruct (DD (t + 1)%Z ltac:(lia)) as (b & Hb & DB). pose proof (byte_range b) as BR. pose proof (nth_error_lt _ _ _ Hb) as HL.
      pose proof (u8ro_read rsegs m A bs (t + 1) b (wa (A + (t + 1))) BUF Hb ltac:(lia) eq_refl) as RD.
      zstep. zstep. zstep. zstep. zstep. if_cases K; zify_cond K.
      + apply (IH A (t + 1)%Z e); try assumption; try lia. intros u Hu. apply DD. lia.
      + killK K.
    - assert (E : (t + 1 = e)%Z) by lia. destruct NE as (b & Hb & NB). pose proof (byte_range b) as BR. pose proof (nth_error_lt _ _ _ Hb) as HL.
      pose proof (u8ro_read rsegs m A bs e b (wa (A + e)) BUF Hb ltac:(lia) eq_refl) as RD.
      zstep. zstep. zstep. zstep. zstep. if_cases K; zify_cond K.
      + destruct NB as [NB|NB]; killK K.
      + apply evt_done. eexists b, _. split; [exact Hb|]. split; [| reflexivity]. lia.
  Qed.

  #[using="Type"] Lemma rl_U3 : forall (k : nat) (A t j pv : Z) (bs : list byte) gp tp t0 t1 t2 s1 a0 a1 a2 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 (F : bvmap 5 word) fc m,
    mem_inv rsegs m -> u8ro rsegs m A bs -> (j - t < Z.of_nat k)%Z -> (0 <= t < j)%Z -> pv = (A + t)%Z ->
    (forall u, (t < u < j)%Z -> bndig bs u) -> bdig bs j -> (0 < A)%Z -> (A + Z.of_nat (length bs) < 2^63)%Z ->
    evt rsegs (fun ms' => exists (b : byte) (pv' : Z), nth_error bs (Z.to_nat j) = Some b /\ pv' = (A + j)%Z /\
        ms' = PRS 0x14ad0 x1 t0 t1 t2 s1 a0 (wz pv') a2 (wz pv') (wz (-1)) (wz (-10)) (wz (bv_unsigned b + -58)) a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 gp tp F fc m)
      (PRS 0x14ab8 x1 t0 t1 t2 s1 a0 a1 a2 (wz pv) (wz (-1)) (wz (-10)) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 gp tp F fc m).
  Proof.
    induction k as [|k IH]; intros until m; intros MI BUF HK HTJ HP ND DJ A0 AHI; [lia|].
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    pose proof (bytes_at_bound _ _ _ _ BUF) as BB.
    assert (JL : (Z.to_nat j < length bs)%nat) by (destruct DJ as (bx & Hbx & _); exact (nth_error_lt _ _ _ Hbx)).
    step. rl_ub.
    destruct (Z.lt_ge_cases (t + 1) j) as [LT|GE].
    - destruct (ND (t + 1)%Z ltac:(lia)) as (b & Hb & NB). pose proof (byte_range b) as BR. pose proof (nth_error_lt _ _ _ Hb) as HL.
      pose proof (u8ro_read rsegs m A bs (t + 1) b (wa (A + (t + 1))) BUF Hb ltac:(lia) eq_refl) as RD.
      zstep. zstep. zstep. zstep. zstep. if_cases K; zify_cond K.
      + apply (IH A (t + 1)%Z j); try assumption; try lia. intros u Hu. apply ND. lia.
      + destruct NB as [NB|NB]; killK K.
    - assert (E : (t + 1 = j)%Z) by lia. destruct DJ as (b & Hb & DB). pose proof (byte_range b) as BR. pose proof (nth_error_lt _ _ _ Hb) as HL.
      pose proof (u8ro_read rsegs m A bs j b (wa (A + j)) BUF Hb ltac:(lia) eq_refl) as RD.
      zstep. zstep. zstep. zstep. zstep. if_cases K; zify_cond K.
      + killK K.
      + apply evt_done. eexists b, _. split; [exact Hb|]. split; [| reflexivity]. lia.
  Qed.

  #[using="Type"] Lemma rl_U4 : forall (k : nat) (A t e pv : Z) (bs : list byte) gp tp t0 t1 t2 s1 a0 a2 a4 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 (F : bvmap 5 word) fc m,
    mem_inv rsegs m -> u8ro rsegs m A bs -> (e - t < Z.of_nat k)%Z -> (0 <= t < e)%Z -> pv = (A + t)%Z ->
    (forall u, (t < u < e)%Z -> bdig bs u) -> bndig bs e -> (0 < A)%Z -> (A + Z.of_nat (length bs) < 2^63)%Z ->
    evt rsegs (fun ms' => exists (b : byte) (pv' : Z), nth_error bs (Z.to_nat e) = Some b /\ pv' = (A + e)%Z /\
        ms' = PRS 0x14b08 x1 t0 t1 t2 s1 a0 (wz pv') a2 (wz (-1)) (wz pv') (wz 10) (wz (bv_unsigned b + -48)) a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 gp tp F fc m)
      (PRS 0x14af0 x1 t0 t1 t2 s1 a0 (wz pv) a2 (wz (-1)) a4 (wz 10) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 gp tp F fc m).
  Proof.
    induction k as [|k IH]; intros until m; intros MI BUF HK HTE HP DD NE A0 AHI; [lia|].
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    pose proof (bytes_at_bound _ _ _ _ BUF) as BB.
    assert (EL : (Z.to_nat e < length bs)%nat) by (destruct NE as (bx & Hbx & _); exact (nth_error_lt _ _ _ Hbx)).
    step. rl_ub.
    destruct (Z.lt_ge_cases (t + 1) e) as [LT|GE].
    - destruct (DD (t + 1)%Z ltac:(lia)) as (b & Hb & DB). pose proof (byte_range b) as BR. pose proof (nth_error_lt _ _ _ Hb) as HL.
      pose proof (u8ro_read rsegs m A bs (t + 1) b (wa (A + (t + 1))) BUF Hb ltac:(lia) eq_refl) as RD.
      zstep. zstep. zstep. zstep. zstep. if_cases K; zify_cond K.
      + apply (IH A (t + 1)%Z e); try assumption; try lia. intros u Hu. apply DD. lia.
      + killK K.
    - assert (E : (t + 1 = e)%Z) by lia. destruct NE as (b & Hb & NB). pose proof (byte_range b) as BR. pose proof (nth_error_lt _ _ _ Hb) as HL.
      pose proof (u8ro_read rsegs m A bs e b (wa (A + e)) BUF Hb ltac:(lia) eq_refl) as RD.
      zstep. zstep. zstep. zstep. zstep. if_cases K; zify_cond K.
      + destruct NB as [NB|NB]; killK K.
      + apply evt_done. eexists b, _. split; [exact Hb|]. split; [| reflexivity]. lia.
  Qed.

  #[using="Type"] Lemma rl_U5 : forall (k : nat) (A t j pv : Z) (bs : list byte) gp tp t0 t1 t2 s1 a0 a2 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 (F : bvmap 5 word) fc m,
    mem_inv rsegs m -> u8ro rsegs m A bs -> (j - t < Z.of_nat k)%Z -> (0 <= t < j)%Z -> pv = (A + t)%Z ->
    (forall u, (t < u < j)%Z -> bndig bs u) -> bdig bs j -> (0 < A)%Z -> (A + Z.of_nat (length bs) < 2^63)%Z ->
    evt rsegs (fun ms' => exists (b : byte) (pv' : Z), nth_error bs (Z.to_nat j) = Some b /\ pv' = (A + j)%Z /\
        ms' = PRS 0x14b40 x1 t0 t1 t2 s1 a0 (wz (-1)) a2 (wz pv') (wz pv') (wz (-10)) (wz (bv_unsigned b + -58)) a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 gp tp F fc m)
      (PRS 0x14b28 x1 t0 t1 t2 s1 a0 (wz (-1)) a2 a3 (wz pv) (wz (-10)) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 gp tp F fc m).
  Proof.
    induction k as [|k IH]; intros until m; intros MI BUF HK HTJ HP ND DJ A0 AHI; [lia|].
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    pose proof (bytes_at_bound _ _ _ _ BUF) as BB.
    assert (JL : (Z.to_nat j < length bs)%nat) by (destruct DJ as (bx & Hbx & _); exact (nth_error_lt _ _ _ Hbx)).
    step. rl_ub.
    destruct (Z.lt_ge_cases (t + 1) j) as [LT|GE].
    - destruct (ND (t + 1)%Z ltac:(lia)) as (b & Hb & NB). pose proof (byte_range b) as BR. pose proof (nth_error_lt _ _ _ Hb) as HL.
      pose proof (u8ro_read rsegs m A bs (t + 1) b (wa (A + (t + 1))) BUF Hb ltac:(lia) eq_refl) as RD.
      zstep. zstep. zstep. zstep. zstep. if_cases K; zify_cond K.
      + apply (IH A (t + 1)%Z j); try assumption; try lia. intros u Hu. apply ND. lia.
      + destruct NB as [NB|NB]; killK K.
    - assert (E : (t + 1 = j)%Z) by lia. destruct DJ as (b & Hb & DB). pose proof (byte_range b) as BR. pose proof (nth_error_lt _ _ _ Hb) as HL.
      pose proof (u8ro_read rsegs m A bs j b (wa (A + j)) BUF Hb ltac:(lia) eq_refl) as RD.
      zstep. zstep. zstep. zstep. zstep. if_cases K; zify_cond K.
      + killK K.
      + apply evt_done. eexists b, _. split; [exact Hb|]. split; [| reflexivity]. lia.
  Qed.

  #[using="Type"] Lemma rl_U6 : forall (k : nat) (A t e pv : Z) (bs : list byte) gp tp t0 t1 t2 s1 a0 a1 a2 a4 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 (F : bvmap 5 word) fc m,
    mem_inv rsegs m -> u8ro rsegs m A bs -> (e - t < Z.of_nat k)%Z -> (0 <= t < e)%Z -> pv = (A + t)%Z ->
    (forall u, (t < u < e)%Z -> bdig bs u) -> bndig bs e -> (0 < A)%Z -> (A + Z.of_nat (length bs) < 2^63)%Z ->
    evt rsegs (fun ms' => exists (b : byte) (pv' : Z), nth_error bs (Z.to_nat e) = Some b /\ pv' = (A + e)%Z /\
        ms' = PRS 0x14b78 x1 t0 t1 t2 s1 a0 (wz pv') a2 (wz pv') (wz (bv_unsigned b)) (wz (-1)) (wz 10) (wz (bv_unsigned b + -48)) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 gp tp F fc m)
      (PRS 0x14b60 x1 t0 t1 t2 s1 a0 a1 a2 (wz pv) a4 (wz (-1)) (wz 10) a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 gp tp F fc m).
  Proof.
    induction k as [|k IH]; intros until m; intros MI BUF HK HTE HP DD NE A0 AHI; [lia|].
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    pose proof (bytes_at_bound _ _ _ _ BUF) as BB.
    assert (EL : (Z.to_nat e < length bs)%nat) by (destruct NE as (bx & Hbx & _); exact (nth_error_lt _ _ _ Hbx)).
    step. rl_ub.
    destruct (Z.lt_ge_cases (t + 1) e) as [LT|GE].
    - destruct (DD (t + 1)%Z ltac:(lia)) as (b & Hb & DB). pose proof (byte_range b) as BR. pose proof (nth_error_lt _ _ _ Hb) as HL.
      pose proof (u8ro_read rsegs m A bs (t + 1) b (wa (A + (t + 1))) BUF Hb ltac:(lia) eq_refl) as RD.
      zstep. zstep. zstep. zstep. zstep. if_cases K; zify_cond K.
      + apply (IH A (t + 1)%Z e); try assumption; try lia. intros u Hu. apply DD. lia.
      + killK K.
    - assert (E : (t + 1 = e)%Z) by lia. destruct NE as (b & Hb & NB). pose proof (byte_range b) as BR. pose proof (nth_error_lt _ _ _ Hb) as HL.
      pose proof (u8ro_read rsegs m A bs e b (wa (A + e)) BUF Hb ltac:(lia) eq_refl) as RD.
      zstep. zstep. zstep. zstep. zstep. if_cases K; zify_cond K.
      + destruct NB as [NB|NB]; killK K.
      + apply evt_done. eexists b, _. split; [exact Hb|]. split; [| reflexivity]. lia.
  Qed.

  #[using="Type"] Lemma rl_U7 : forall (k : nat) (A o t e a1v a0v : Z) (bs : list byte) (be : byte) gp tp t0 t1 t2 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 (F : bvmap 5 word) fc m,
    mem_inv rsegs m -> u8ro rsegs m A bs -> (e - t < Z.of_nat k)%Z -> (0 <= o <= t)%Z -> (t < e)%Z ->
    nth_error bs (Z.to_nat e) = Some be -> ~ bblank be ->
    a1v = (A + t)%Z -> a0v = (t - o)%Z -> (0 < A)%Z -> (A + Z.of_nat (length bs) < 2^63)%Z ->
    evt rsegs (fun ms' => exists (t' a0v' a1v' : Z) (bt' : byte), (t < t' <= e)%Z /\ a0v' = (t' - o)%Z /\ a1v' = (A + t')%Z /\
        nth_error bs (Z.to_nat t') = Some bt' /\ ~ bblank bt' /\
        ms' = PRS 0x14bc0 x1 t0 t1 t2 s1 (wz a0v') (wz a1v') (wz (-1)) (wz 32) (wz 9) (wz (bv_unsigned bt')) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 gp tp F fc m)
      (PRS 0x14ba8 x1 t0 t1 t2 s1 (wz a0v) (wz a1v) (wz (-1)) (wz 32) (wz 9) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 gp tp F fc m).
  Proof.
    induction k as [|k IH]; intros until m; intros MI BUF HK HO HT Hbe NBE H1 H0 A0 AHI; [lia|].
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    pose proof (bytes_at_bound _ _ _ _ BUF) as BB. pose proof (nth_error_lt _ _ _ Hbe) as HLe.
    destruct (nth_error bs (Z.to_nat (t + 1))) as [b1|] eqn:Hb1. 2:{ exfalso. apply nth_error_None in Hb1. lia. }
    pose proof (byte_range b1) as BR.
    pose proof (u8ro_read rsegs m A bs (t + 1) b1 (wa (A + (t + 1))) BUF Hb1 ltac:(lia) eq_refl) as RD.
    assert (NXT : bblank b1 -> (t + 1 < e)%Z).
    { intros BL. destruct (Z.eq_dec (t + 1) e) as [E|NE]; [| lia]. exfalso. rewrite E in Hb1. rewrite Hb1 in Hbe. injection Hbe as <-. exact (NBE BL). }
    step. rl_ub.
    zstep. zstep. zstep. zstep. if_cases K1; zify_cond K1.
    - zstep. if_cases K2; zify_cond K2.
      + apply evt_done. exists (t + 1)%Z, (a0v + 1)%Z, (a1v + 1)%Z, b1. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact Hb1|]. split; [unfold bblank; lia| reflexivity].
      + eapply evt_mono. { apply (IH A o (t + 1)%Z e (a1v + 1)%Z (a0v + 1)%Z bs be); try eassumption; try lia. apply NXT. unfold bblank. lia. }
        cbv beta. intros ms' (t' & x0 & xa & bt' & R & REST). exists t', x0, xa, bt'. split; [lia| exact REST].
    - zstep. eapply evt_mono. { apply (IH A o (t + 1)%Z e (a1v + 1)%Z (a0v + 1)%Z bs be); try eassumption; try lia. apply NXT. unfold bblank. lia. }
      cbv beta. intros ms' (t' & x0 & xa & bt' & R & REST). exists t', x0, xa, bt'. split; [lia| exact REST].
  Qed.

  Definition runs3 (bs : list byte) (o j1 e1 j2 e2 j3 e3 : Z) : Prop :=
    (0 <= o <= j1 /\ j1 < e1 <= j2 /\ j2 < e2 <= j3 /\ j3 < e3)%Z
    /\ (forall t, (o <= t < j1)%Z -> bndig bs t) /\ bdig bs j1 /\ (forall t, (j1 <= t < e1)%Z -> bdig bs t) /\ bndig bs e1
    /\ (forall t, (e1 <= t < j2)%Z -> bndig bs t) /\ bdig bs j2 /\ (forall t, (j2 <= t < e2)%Z -> bdig bs t) /\ bndig bs e2
    /\ (forall t, (e2 <= t < j3)%Z -> bndig bs t) /\ bdig bs j3 /\ (forall t, (j3 + 1 <= t < e3)%Z -> bdig bs t) /\ bndig bs e3.

  #[using="Type"] Lemma rl_wfin : forall (A o l e3 : Z) (bs : list byte) (b3 be : byte) (sb : word)
      gp tp t0 t1 t2 a0 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 (F : bvmap 5 word) fc m,
    mem_inv rsegs m -> rw_cells rsegs m (q + 16) [C8 (wz (A + o)); C8 (wz l)] -> u8ro rsegs m A bs ->
    (0 <= o <= e3)%Z -> (e3 <= o + l)%Z -> nth_error bs (Z.to_nat e3) = Some b3 -> bblank b3 ->
    nth_error bs (Z.to_nat (o + l)) = Some be -> ~ bblank be -> (0 < A)%Z -> (A + Z.of_nat (length bs) < 2^63)%Z ->
    evt rsegs (fun ms' =>
      exists (t' nv : Z) (bt' : byte) a3' a4' a5' a6' a7', (e3 <= t' <= o + l)%Z /\ nth_error bs (Z.to_nat t') = Some bt' /\ ~ bblank bt' /\ nv = (l - (t' - o))%Z /\
             ms' = MS (mkR (wz 0x14bd0) (wz q) gp tp t0 t1 t2 (wz P) (wz (P + 228)) (wz (P + 232)) (wz (A + t')) (wz nv) a3' a4' a5' a6' a7' (wz (P + 280)) (wz (P + 276)) sb s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                      F (wz membuffer_assign_entry) fc None m (seg_rom rsegs))
      (PRS 0x14b90 x1 t0 t1 t2 (wz (P + 228)) a0 (wz (A + e3)) (wz (A + o)) (wz 32) a4 a5 a6 a7 (wz (P + 280)) (wz (P + 276)) sb s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 gp tp F fc m).
  Proof.
    intros until m. intros MI Q16 BUF OE E3 Hb3 BL3 Hbe NBE A0 AHI. unfold membuffer_assign_entry.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    pose proof (bytes_at_bound _ _ _ _ BUF) as BB. pose proof (nth_error_lt _ _ _ Hbe) as HLe. pose proof (byte_range b3) as BR3.
    pose proof (u8ro_read rsegs m A bs e3 b3 (wa (A + e3)) BUF Hb3 ltac:(lia) eq_refl) as RD.
    assert (NE3 : (e3 < o + l)%Z).
    { destruct (Z.eq_dec e3 (o + l)) as [E|NE]; [| lia]. exfalso. rewrite E in Hb3. rewrite Hb3 in Hbe. injection Hbe as <-. exact (NBE BL3). }
    unfold bblank in BL3.
    zstep. zstep. zstep. zstep.
    zstep. if_cases K1; zify_cond K1; [| zstep; if_cases K2; zify_cond K2; [exfalso; lia|] ].
    all: eapply evt_cut; [ eapply (rl_U7 (Datatypes.S (Z.to_nat (o + l - e3))) A o e3 (o + l)); try eassumption; try lia | ].
    all: cbv beta; intros ms7 (t' & x0 & xa & bt' & R7 & E0 & E1 & Hbt' & NB7 & ->); subst x0 xa.
    all: zstep; zstep; zstep; zstep.
    all: apply evt_done; exists t', (l - (t' - o))%Z, bt'; do 5 eexists.
    all: split; [lia|]; split; [exact Hbt'|]; split; [exact NB7|]; split; [lia| reflexivity].
  Qed.

  #[using="Type"] Lemma rl_wtail : forall (A o l j1 e1 j2 e2 j3 e3 : Z) (bs : list byte) (be : byte) (sb : word)
      gp tp t0 t1 t2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 (F : bvmap 5 word) fc m,
    mem_inv rsegs m -> rw_cells rsegs m (q + 16) [C8 (wz (A + o)); C8 (wz l)] -> u8ro rsegs m A bs ->
    runs3 bs o j1 e1 j2 e2 j3 e3 -> (e3 <= o + l)%Z ->
    nth_error bs (Z.to_nat (o + l)) = Some be -> ~ bblank be -> (0 < A)%Z -> (A + Z.of_nat (length bs) < 2^63)%Z ->
    evt rsegs (fun ms' =>
         (exists a1' a2' a3' a4' a5' a6' a7', ms' = PRS 0x14bf0 x1 t0 t1 t2 (wz (P + 228)) (wz 3) a1' a2' a3' a4' a5' a6' a7' (wz (P + 280)) (wz (P + 276)) sb s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 gp tp F fc m)
      \/ (exists (t' nv : Z) (bt' : byte) a3' a4' a5' a6' a7', (e3 <= t' <= o + l)%Z /\ nth_error bs (Z.to_nat t') = Some bt' /\ ~ bblank bt' /\ nv = (l - (t' - o))%Z /\
             ms' = MS (mkR (wz 0x14bd0) (wz q) gp tp t0 t1 t2 (wz P) (wz (P + 228)) (wz (P + 232)) (wz (A + t')) (wz nv) a3' a4' a5' a6' a7' (wz (P + 280)) (wz (P + 276)) sb s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                      F (wz membuffer_assign_entry) fc None m (seg_rom rsegs)))
      (PRS 0x14a68 x1 t0 t1 t2 (wz (P + 228)) (wz 3) (wz (A + j1)) (wz (A + o)) a3 a4 a5 a6 a7 (wz (P + 280)) (wz (P + 276)) sb s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 gp tp F fc m).
  Proof.
    intros until m. intros MI Q16 BUF RU E3 Hbe NBE A0 AHI.
    destruct RU as (ORD & N1 & D1 & R1 & X1 & N2 & D2 & R2 & X2 & N3 & D3 & R3 & X3).
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    pose proof (bytes_at_bound _ _ _ _ BUF) as BB. pose proof (nth_error_lt _ _ _ Hbe) as HLe.
    assert (E1J2 : (e1 < j2)%Z).
    { destruct (Z.eq_dec e1 j2) as [E|NE]; [| lia]. exfalso. rewrite E in X1. destruct X1 as (bx & Hbx & NX). destruct D2 as (by' & Hby & DY).
      rewrite Hbx in Hby. injection Hby as <-. lia. }
    assert (E2J3 : (e2 < j3)%Z).
    { destruct (Z.eq_dec e2 j3) as [E|NE]; [| lia]. exfalso. rewrite E in X2. destruct X2 as (bx & Hbx & NX). destruct D3 as (by' & Hby & DY).
      rewrite Hbx in Hby. injection Hby as <-. lia. }
    destruct D1 as (b1 & Hb1 & DB1). pose proof (byte_range b1) as BR1. pose proof (nth_error_lt _ _ _ Hb1) as HL1.
    pose proof (u8ro_read rsegs m A bs j1 b1 (wa (A + j1)) BUF Hb1 ltac:(lia) eq_refl) as RD1.
    zstep. zstep. zstep. zstep. if_cases K; zify_cond K; [killK K| clear K].
    zstep. zstep.
    assert (R1' : forall u, (j1 < u < e1)%Z -> bdig bs u) by (intros u Hu; apply R1; lia).
    eapply evt_cut. { eapply (rl_U2 (Datatypes.S (Z.to_nat (e1 - j1))) A j1 e1); try eassumption; lia. }
    cbv beta. intros ms1 (c1 & v1 & Hc1 & Hv1 & ->). subst v1. clear RD1.
    destruct X1 as (bx & Hbx & NX1). rewrite Hc1 in Hbx. injection Hbx as <-. pose proof (byte_range c1) as BC1. pose proof (nth_error_lt _ _ _ Hc1) as HC1.
    pose proof (u8ro_read rsegs m A bs e1 c1 (wa (A + e1)) BUF Hc1 ltac:(lia) eq_refl) as RD2.
    zstep. zstep. zstep. zstep. zstep. if_cases K; zify_cond K; [destruct NX1 as [NX1|NX1]; killK K| clear K].
    zstep. zstep.
    assert (N2' : forall u, (e1 < u < j2)%Z -> bndig bs u) by (intros u Hu; apply N2; lia).
    eapply evt_cut. { eapply (rl_U3 (Datatypes.S (Z.to_nat (j2 - e1))) A e1 j2); try eassumption; lia. }
    cbv beta. intros ms2 (c2 & v2 & Hc2 & Hv2 & ->). subst v2. clear RD2.
    destruct D2 as (bx & Hbx & DB2). rewrite Hc2 in Hbx. injection Hbx as <-. pose proof (byte_range c2) as BC2. pose proof (nth_error_lt _ _ _ Hc2) as HC2.
    pose proof (u8ro_read rsegs m A bs j2 c2 (wa (A + j2)) BUF Hc2 ltac:(lia) eq_refl) as RD3.
    zstep. zstep. zstep. zstep. zstep. if_cases K; zify_cond K; [killK K| clear K].
    zstep. zstep.
    assert (R2' : forall u, (j2 < u < e2)%Z -> bdig bs u) by (intros u Hu; apply R2; lia).
    eapply evt_cut. { eapply (rl_U4 (Datatypes.S (Z.to_nat (e2 - j2))) A j2 e2); try eassumption; lia. }
    cbv beta. intros ms3 (c3 & v3 & Hc3 & Hv3 & ->). subst v3. clear RD3.
    destruct X2 as (bx & Hbx & NX2). rewrite Hc3 in Hbx. injection Hbx as <-. pose proof (byte_range c3) as BC3. pose proof (nth_error_lt _ _ _ Hc3) as HC3.
    pose proof (u8ro_read rsegs m A bs e2 c3 (wa (A + e2)) BUF Hc3 ltac:(lia) eq_refl) as RD4.
    zstep. zstep. zstep. zstep. zstep. if_cases K; zify_cond K; [destruct NX2 as [NX2|NX2]; killK K| clear K].
    zstep. zstep.
    assert (N3' : forall u, (e2 < u < j3)%Z -> bndig bs u) by (intros u Hu; apply N3; lia).
    eapply evt_cut. { eapply (rl_U5 (Datatypes.S (Z.to_nat (j3 - e2))) A e2 j3); try eassumption; lia. }
    cbv beta. intros ms4 (c4 & v4 & Hc4 & Hv4 & ->). subst v4. clear RD4.
    destruct D3 as (bx & Hbx & DB3). rewrite Hc4 in Hbx. injection Hbx as <-. pose proof (byte_range c4) as BC4. pose proof (nth_error_lt _ _ _ Hc4) as HC4.
    pose proof (u8ro_read rsegs m A bs j3 c4 (wa (A + j3)) BUF Hc4 ltac:(lia) eq_refl) as RD5.
    zstep. zstep. zstep. zstep. zstep. if_cases K; zify_cond K; [killK K| clear K].
    zstep. zstep.
    assert (R3' : forall u, (j3 < u < e3)%Z -> bdig bs u) by (intros u Hu; apply R3; lia).
    eapply evt_cut. { eapply (rl_U6 (Datatypes.S (Z.to_nat (e3 - j3))) A j3 e3); try eassumption; lia. }
    cbv beta. intros ms5 (c5 & v5 & Hc5 & Hv5 & ->). subst v5. clear RD5. pose proof (byte_range c5) as BC5.
    zstep. zstep. zstep. if_cases K1; zify_cond K1.
    - eapply evt_mono. { eapply (rl_wfin A o l e3 bs c5 be sb); try eassumption; try lia. unfold bblank. lia. }
      cbv beta. intros ms' X. right. exact X.
    - zstep. zstep. if_cases K2; zify_cond K2.
      + apply evt_done. left. do 7 eexists. reflexivity.
      + eapply evt_mono. { eapply (rl_wfin A o l e3 bs c5 be sb); try eassumption; try lia. unfold bblank. lia. }
        cbv beta. intros ms' X. right. exact X.
  Qed.

  #[using="Type"] Lemma rl_walk : forall (A o l j1 e1 j2 e2 j3 e3 : Z) (bs : list byte) (be : byte) (sb : word)
      gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 (F : bvmap 5 word) fc m,
    mem_inv rsegs m -> rw_cells rsegs m (q + 16) [C8 (wz (A + o)); C8 (wz l)] -> u8ro rsegs m A bs ->
    runs3 bs o j1 e1 j2 e2 j3 e3 -> (e3 <= o + l)%Z ->
    nth_error bs (Z.to_nat (o + l)) = Some be -> ~ bblank be -> (0 < A)%Z -> (A + Z.of_nat (length bs) < 2^63)%Z ->
    evt rsegs (fun ms' =>
         (exists a1' a2' a3' a4' a5' a6' a7', ms' = PRS 0x14bf0 x1 t0 t1 t2 (wz (P + 228)) (wz 3) a1' a2' a3' a4' a5' a6' a7' (wz (P + 280)) (wz (P + 276)) sb s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 gp tp F fc m)
      \/ (exists (t' nv : Z) (bt' : byte) a3' a4' a5' a6' a7', (e3 <= t' <= o + l)%Z /\ nth_error bs (Z.to_nat t') = Some bt' /\ ~ bblank bt' /\ nv = (l - (t' - o))%Z /\
             ms' = MS (mkR (wz 0x14bd0) (wz q) gp tp t0 t1 t2 (wz P) (wz (P + 228)) (wz (P + 232)) (wz (A + t')) (wz nv) a3' a4' a5' a6' a7' (wz (P + 280)) (wz (P + 276)) sb s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                      F (wz membuffer_assign_entry) fc None m (seg_rom rsegs)))
      (PRS 0x14a28 x1 t0 t1 t2 (wz (P + 228)) (wz 3) a1 a2 a3 a4 a5 a6 a7 (wz (P + 280)) (wz (P + 276)) sb s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 gp tp F fc m).
  Proof.
    intros until m. intros MI Q16 BUF RU E3 Hbe NBE A0 AHI.
    pose proof RU as RU0. destruct RU0 as (ORD & N1 & D1 & _).
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    pose proof (bytes_at_bound _ _ _ _ BUF) as BB. pose proof (nth_error_lt _ _ _ Hbe) as HLe.
    destruct (nth_error bs (Z.to_nat o)) as [b0|] eqn:Hb0. 2:{ exfalso. apply nth_error_None in Hb0. lia. }
    pose proof (byte_range b0) as BR0.
    pose proof (u8ro_read rsegs m A bs o b0 (wa (A + o)) BUF Hb0 ltac:(lia) eq_refl) as RD0.
    zstep. step. rl_ub.
    zstep. zstep. zstep. zstep. zstep. if_cases K; zify_cond K.
    - assert (OJ : o = j1).
      { destruct (Z.eq_dec o j1) as [E|NE]; [exact E|]. exfalso. destruct (N1 o ltac:(lia)) as (bx & Hbx & NB). rewrite Hb0 in Hbx. injection Hbx as <-.
        destruct NB as [NB|NB]; killK K. }
      subst j1. eapply (rl_wtail A o l o e1 j2 e2 j3 e3); eassumption.
    - assert (OJ : (o < j1)%Z).
      { destruct (Z.eq_dec o j1) as [E|NE]; [| lia]. exfalso. rewrite <- E in D1. destruct D1 as (bx & Hbx & DB). rewrite Hb0 in Hbx. injection Hbx as <-. killK K. }
      zstep. zstep. zstep.
      assert (N1' : forall u, (o < u < j1)%Z -> bndig bs u) by (intros u Hu; apply N1; lia).
      eapply evt_cut. { eapply (rl_U1 (Datatypes.S (Z.to_nat (j1 - o))) A o j1); try eassumption; lia. }
      cbv beta. intros ms1 (c0 & v0 & Hc0 & Hv0 & ->). subst v0.
      eapply (rl_wtail A o l j1 e1 j2 e2 j3 e3); eassumption.
  Qed.

  Definition ctl9 (err hack pos entp clen csz esp : Z) : list cell :=
    [C4 (wz err); C4 (wz hack); C4 (wz pos); C4 (wz entp); C4 (wz clen); C4 (wz 0); C8 (wz csz); C8 (wz esp)].
  #[using="QLO QP PHI"] Lemma rl_fin : forall (r err hack pos entp clen csz esp : Z) ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      x1 x9 x18 x19 x20 (F : bvmap 5 word) fc m,
    stk rsegs m lo q -> mem_inv rsegs m -> rw_cells rsegs m (q + 32) (rlFS ra s0 s1 s2 s3 s4) -> rlFX m ->
    rw_cells rsegs m (P + 440) (ctl9 err hack pos entp clen csz esp) -> (r = 0 \/ r = -104)%Z ->
    evt rsegs (fun ms' => exists a0' m', ms' = MS (mkR ra (wz (q + 80)) gp tp t0 t1 t2 s0 s1 a0' a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                  F (ret_pc ra) fc None m' (seg_rom rsegs)
                          /\ munch [(P + 440, P + 452)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
                          /\ stk rsegs m' lo (q + 80)
                          /\ ( (r = 0 /\ a0' = wz 4 /\ rw_cells rsegs m' (P + 440) (ctl9 err hack 2 entp clen csz esp))
                             \/ (r <> 0 /\ a0' = wz 3 /\ rw_cells rsegs m' (P + 440) (ctl9 500 hack pos entp clen csz esp)) )%Z)
      (MS (mkR x1 (wz q) gp tp t0 t1 t2 (wz P) x9 (wz r) a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz 0x14bd0) fc None m (seg_rom rsegs)).
  Proof.
    intros until m. intros ST MI FSH FX CTL RR. unfold ctl9 in *. unfold rlFS in FSH.
    destruct FX as ([j0 Q0] & [ty Q12] & (a16 & b16 & Q16)).
    pose proof (munch_refl [(P + 440, P + 452)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
    zstep. if_cases K; zify_cond K.
    -   zstep. sstep. zstep.
      eapply evt_cut. { eapply rl_epi; try eassumption. split; [eexists; eassumption|]. split; [eexists; eassumption| do 2 eexists; eassumption]. }
      cbv beta. intros ms' [-> ST']. apply evt_done. do 2 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST'|].
      left. split; [| split; [reflexivity| assumption]]. destruct RR as [E|E]; [exact E| exfalso; subst r; cbv in K; lia].
    - zstep. sstep. zstep. zstep.
      eapply evt_cut. { eapply rl_epi; try eassumption. split; [eexists; eassumption|]. split; [eexists; eassumption| do 2 eexists; eassumption]. }
      cbv beta. intros ms' [-> ST']. apply evt_done. do 2 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST'|].
      right. split; [| split; [reflexivity| assumption]]. intros ->. apply K. reflexivity.
  Qed.
End SEGS.
