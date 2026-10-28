(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From stdpp Require Import base list.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Arr.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import ScanInt.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac CellConv.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs F_syscalls Stdio_base F_shgetc_A F_shgetc_B F_strtol F_vfscanf_lib F_sscanf H_map_str_to_int H_memptr_cmp H_presp_A H_presp_B H_phdr_B HU_list_kit.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Ceiling.
Import ListNotations.
Open Scope Z_scope.
Set Printing Width 1000.
Set Printing Depth 100.

Notation FMT09 := 0x10331%Z.
Notation FMTREQ := 0x10423%Z.
Notation MTAB := 0x2b3b8%Z.
Notation FMT_VER := 0x10365%Z.
Notation HEAD := 0x15c98%Z.
Ltac rqv_sstep := step; fix_lit_store.

Lemma rqv_land64_neg : forall x, (-2^63 <= x < 0)%Z -> Z.land x 18446744073709551615 = (x + 2^64)%Z.
Proof.
  intros x H. change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_ones by lia.
  rewrite <- (Z.mod_add x 1 (2^64)) by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma rqv_land64_nonneg : forall x, (0 <= x < 2^64)%Z -> Z.land x 18446744073709551615 = x.
Proof. intros x H. change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.
Ltac rqv_sgn K x := first [ rewrite (rqv_land64_neg x) in K by lia | rewrite (rqv_land64_nonneg x) in K by lia ].

Notation zb := (Z_to_bv 8 0).

Definition rqv_hidden (P : Prop) := P.
Ltac rqv_stash H := lazymatch type of H with rqv_hidden _ => idtac | ?T => change T with (rqv_hidden T) in H end.
Ltac rqv_unstash := unfold rqv_hidden in *.

Ltac rqv_lit_branch :=
  lazymatch goal with |- evt _ _ (MS _ _ (if ?c then ?a else ?b) _ _ _ _) =>
    first [ replace (if c then a else b) with a by (vm_compute; reflexivity)
          | replace (if c then a else b) with b by (vm_compute; reflexivity) ] end.

Ltac rqv_zlia := first [ lia | (rewrite ?zb_lxor_ones by lia; lia) ].
Ltac rqv_b2z :=
  repeat match goal with |- context [Z.b2z (?a <? ?b)] =>
    first [ replace (a <? b) with true by (symmetry; apply Z.ltb_lt; rqv_zlia) | replace (a <? b) with false by (symmetry; apply Z.ltb_ge; rqv_zlia) ] end;
  cbn [Z.b2z]; change (Z.lxor 1 0) with 1; change (Z.lxor 0 1) with 1; change (Z.lxor 1 1) with 0; change (Z.lxor 0 0) with 0.

Section RQV.
Context {HCEIL : HasCeiling}.
  Hypothesis SNC : strncasecmp_stmt.
  Variables (P q lo : Z).
  Notation S := (P + 480)%Z.
  Hypothesis QLO : (lo + 1096 <= q)%Z.
  Hypothesis LO0 : (0x5d000 <= lo)%Z.
  Hypothesis QP : (q + 208 <= P)%Z.
  Hypothesis PHI : (P + 504 < 2^62)%Z.
  Variable mws : list word.
  Hypothesis MWSL : length mws = 22%nat.
  Hypothesis MID : forall i, (0 <= i < 11)%Z -> exists id, nth_error mws (Z.to_nat (2 * i + 1)) = Some (wz id) /\ (0 <= id <= 11)%Z.
  Hypothesis MT : table_strings mws 11 lo.


  Notation PRS pc x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7v s9v t3 t4 t5 t6 gp tp F fc m :=
    (MS (mkR x1 (wz q) gp tp t0 t1 t2 (wz P) (wz S) a0 a1 a2 a3 a4 a5 a6 a7 (wz (-1)) (wz 47) (wz 2) (wz FMT09) (wz MTAB) s7v (wz 3) s9v (wz 1) (wz 4) t3 t4 t5 t6)
        F (wz pc) fc None m (seg_rom rsegs)).
  Notation FIX m := (rw_cells rsegs m (q + 16) [C8 (wz (P + 280)); C8 (wz (P + 276)); C8 (wz (P + 8)); C8 (wz (2^64 - 1 - MTAB)); C8 (wz FMTREQ)]).

  #[using="mws MWSL"] Lemma rqv_ts_mono : forall ws ne B B', table_strings ws ne B -> (B <= B')%Z -> table_strings ws ne B'.
  Proof.
    intros ws ne B B' TS LE i Hi. destruct (TS i Hi) as (Sx & str & slack & H1 & H2 & H3 & H4 & H5).
    exists Sx, str, slack. repeat (split; [assumption|]). lia.
  Qed.

  Definition rqv_ctl8 (err hack pos entp clen csz esp : Z) : list cell :=
    [C4 (wz err); C4 (wz hack); C4 (wz pos); C4 (wz entp); C4 (wz clen); C4 (wz 0); C8 (wz csz); C8 (wz esp)].

  #[using="QLO LO0 QP PHI"] Lemma rqv_msi : forall (r err A o l : Z) (n : nat) (bs : list byte) (j8 s9v : word) gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 x1 (F : bvmap 5 word) fc m,
    mem_inv rsegs m -> rw_cells rsegs m (P + 440) [C4 (wz err)] ->
    rw_cells rsegs m (q + 8) [C8 j8] -> FIX m -> rw_cells rsegs m (q + 72) [C8 (wz (A + o)); C8 (wz l)] -> rw_cells rsegs m A [CB n bs] ->
    (r = -1 \/ 0 <= r < 11)%Z -> (0 <= err < 2^32)%Z ->
    (0 <= o)%Z -> (0 <= l)%Z -> (o + l + 1 < Z.of_nat n)%Z -> (0 < A)%Z -> (A + Z.of_nat n <= lo)%Z ->
    evt rsegs (fun ms' => exists m',
        ( r = -1 /\ ms' = PRS HEAD x1 t0 t1 t2 (wz 3) a1 a2 a3 a4 a5 a6 a7 (wz MTAB) s9v t3 t4 t5 t6 gp tp F fc m'
          /\ munch [(P + 440, P + 444)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
          /\ rw_cells rsegs m' (P + 440) [C4 (wz 501)] /\ rw_cells rsegs m' (q + 8) [C8 j8] /\ FIX m'
          /\ rw_cells rsegs m' (q + 72) [C8 (wz (A + o)); C8 (wz l)] /\ rw_cells rsegs m' A [CB n bs] )
     \/ ( exists b : byte, (0 <= r)%Z /\ nth_error bs (Z.to_nat (o + l)) = Some b
          /\ ms' = PRS SSCANF (wz 0x15ecc) t0 t1 t2 (wz (A + o)) (wz FMT_VER) (wz (P + 276)) (wz (P + 280)) a4 a5 a6 a7 (wz (bv_unsigned b)) (wz r) t3 t4 t5 t6 gp tp F fc m'
          /\ munch [(q + 8, q + 16); (A + (o + l), A + (o + l) + 1)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
          /\ rw_cells rsegs m' (P + 440) [C4 (wz err)] /\ rw_cells rsegs m' (q + 8) [C8 (wz MTAB)] /\ FIX m'
          /\ rw_cells rsegs m' (q + 72) [C8 (wz (A + o)); C8 (wz l)]
          /\ rw_cells rsegs m' A [CB n (firstn (Z.to_nat (o + l)) bs ++ [Z_to_bv 8 0] ++ skipn (Z.to_nat (o + l) + 1) bs)] ))
      (PRS 0x15e7c x1 t0 t1 t2 (wz r) a1 a2 a3 a4 a5 a6 a7 (wz MTAB) s9v t3 t4 t5 t6 gp tp F fc m).
  Proof. clear MID MT MWSL.
    intros until m. intros MI EC Q8 FX Q72 BLK RR ER O0 L0 KN A0 AHI. unfold SSCANF.
    pose proof (wmono_refl rsegs m) as WM.
    assert (LBS : length bs = n) by (destruct BLK as [[W _] _]; cbn in W; LiaTuning.ctauto).
    zstep. if_cases K0; zify_cond K0.
    {
      pose proof (munch_refl [(P + 440, P + 444)]%Z m) as MU.
      assert (R1 : r = -1) by (destruct RR as [E|RR']; [exact E| exfalso; rqv_sgn K0 r; lia]).
      zstep. zstep. rqv_sstep. zstep. zstep.
      apply evt_done. eexists. left. split; [exact R1|]. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
      repeat (split; [eassumption|]). eassumption. }
    assert (R0 : (0 <= r < 11)%Z) by (destruct RR as [->|RR']; [exfalso; cbv in K0; first [lia| discriminate| exact (K0 eq_refl)]| exact RR']).
    pose proof (munch_refl [(q + 8, q + 16); (A + (o + l), A + (o + l) + 1)]%Z m) as MU.
    destruct (nth_error bs (Z.to_nat (o + l))) as [b|] eqn:Hb. 2:{ exfalso. apply nth_error_None in Hb. lia. }

    apply (rw_cells_split_CB rsegs m A [] n bs [] [Z.to_nat (o + l); 1%nat; Z.to_nat (Z.of_nat n - (o + l) - 1)]) in BLK; [| cbn; lia].
    cbn [app mk_CB_cells] in BLK.
    lazymatch type of BLK with rw_cells _ _ _ [?c1; ?c2; ?c3] =>
      destruct (proj1 (rw_cells_app rsegs m A [c1] [c2; c3]) BLK) as [BLK1 BLK23] end. clear BLK.
    cbn [cells_size csize] in BLK23. rewrite Nat.add_0_r, Z2Nat.id in BLK23 by lia.
    assert (E1 : firstn 1 (skipn (Z.to_nat (o + l)) bs) = [b]).
    { destruct (nth_error_split _ _ _ Hb) as (pre & post & E & Hlen). rewrite E at 1. rewrite skipn_app, skipn_all2, Hlen, Nat.sub_diag by lia. reflexivity. }
    rewrite E1 in BLK23.
    zstep. rqv_sstep. zstep. zstep. zstep.
    step. ubr.
    zstep. zstep. zstep. rqv_b2z. step. rqv_lit_branch.
    step. ubr.
    remember (A + (o + l))%Z as V eqn:EV.
    replace (wz (A + o + l)) with (wz V) by (f_equal; lia).
    zstep. rqv_sstep. subst V.
    zstep. zstep. zstep. zstep. zstep. zstep.

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
    apply evt_done. eexists. right. exists b. split; [lia|]. split; [first [exact Hb| reflexivity]|]. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. repeat (split; [eassumption|]). exact BLK.
    Unshelve. all: try exact (wz 0); try exact m.
  Qed.

  #[using="QLO LO0 QP PHI MWSL"] Lemma rqv_ver : forall (r idx id A o l maj min err meth pos : Z) (n : nat) (bs : list byte) (b : byte) (hack entp clen csz esp : Z)
      gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 x1 (F : bvmap 5 word) fc m,
    mem_inv rsegs m -> u64arr rsegs m MTAB mws -> nth_error mws (Z.to_nat (2 * idx + 1)) = Some (wz id) -> (0 <= idx < 11)%Z -> (0 <= id < 64)%Z ->
    rw_cells rsegs m (q + 8) [C8 (wz MTAB)] -> FIX m -> rw_cells rsegs m (q + 72) [C8 (wz (A + o)); C8 (wz l)] -> rw_cells rsegs m A [CB n bs] ->
    rw_cells rsegs m (P + 276) [C4 (wz maj)] -> rw_cells rsegs m (P + 280) [C4 (wz min)] ->
    rw_cells rsegs m (P + 440) (rqv_ctl8 err hack pos entp clen csz esp) -> rw_cells rsegs m P [C4 (wz 1); C4 (wz meth)] ->
    (- 2^31 <= maj < 2^31)%Z -> (- 2^31 <= min < 2^31)%Z -> (r = -1 \/ 0 <= r <= 2)%Z -> (0 <= err < 2^32)%Z -> (0 <= meth < 2^32)%Z -> (0 <= pos < 2^32)%Z ->
    (0 <= o)%Z -> (0 <= l)%Z -> (o + l + 1 < Z.of_nat n)%Z -> (0 < A)%Z -> (A + Z.of_nat n <= lo)%Z ->
    (A + Z.of_nat n <= 0x2a000 \/ 0x5d000 <= A)%Z ->
    evt rsegs (fun ms' => exists m' (ra0 err' meth' pos' : Z) a0' a1' a2' a3' a4' a5' s7' s9',
        ms' = PRS HEAD x1 t0 t1 t2 (wz ra0) a1' a2' a3' a4' a5' a6 a7 s7' s9' t3 t4 t5 t6 gp tp F fc m'
        /\ munch [(A + (o + l), A + (o + l) + 1); (P + 440, P + 444); (P + 448, P + 452); (P + 4, P + 8)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
        /\ rw_cells rsegs m' (q + 8) [C8 (wz MTAB)] /\ FIX m' /\ rw_cells rsegs m' (q + 72) [C8 (wz (A + o)); C8 (wz l)]
        /\ rw_cells rsegs m' A [CB n (firstn (Z.to_nat (o + l)) bs ++ [b] ++ skipn (Z.to_nat (o + l) + 1) bs)]
        /\ rw_cells rsegs m' (P + 276) [C4 (wz maj)] /\ rw_cells rsegs m' (P + 280) [C4 (wz min)]
        /\ rw_cells rsegs m' (P + 440) (rqv_ctl8 err' hack pos' entp clen csz esp) /\ rw_cells rsegs m' P [C4 (wz 1); C4 (wz meth')]
        /\ u64arr rsegs m' MTAB mws
        /\ ( (ra0 = 3 /\ err' = 505 /\ meth' = meth /\ pos' = pos)
           \/ (ra0 = 4 /\ err' = err /\ meth' = id /\ pos' = 2 /\ r = 2 /\ 0 <= maj) )%Z /\ (a0' : word) = a0')
      (PRS 0x15ecc x1 t0 t1 t2 (wz r) a1 a2 a3 a4 a5 a6 a7 (wz (bv_unsigned b)) (wz idx) t3 t4 t5 t6 gp tp F fc m).
  Proof. clear MID MT.
    intros until m. intros MI TAB HN IR IDR Q8 FX Q72 BLK C1c C2c CTL MC MR NR RR ER METR PR O0 L0 KN A0 AHI AW. unfold rqv_ctl8 in *.
    lazymatch goal with |- evt _ ?Q _ => set (POSTV := Q) end.
    assert (SH4 : Z.shiftl idx 4 = 16 * idx) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    pose proof (munch_refl [(A + (o + l), A + (o + l) + 1); (P + 440, P + 444); (P + 448, P + 452); (P + 4, P + 8)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
    pose proof (bv_unsigned_in_range 8 b) as BR. unfold bv_modulus in BR. cbn in BR.
    assert (LBS : length bs = n) by (destruct BLK as [[W _] _]; cbn in W; LiaTuning.ctauto).
    apply (rw_cells_split_CB rsegs m A [] n bs [] [Z.to_nat (o + l); 1%nat; Z.to_nat (Z.of_nat n - (o + l) - 1)]) in BLK; [| cbn; lia].
    cbn [app mk_CB_cells] in BLK.
    lazymatch type of BLK with rw_cells _ _ _ [?c1; ?c2; ?c3] =>
      destruct (proj1 (rw_cells_app rsegs m A [c1] [c2; c3]) BLK) as [BLK1 BLK23] end. clear BLK.
    cbn [cells_size csize] in BLK23. rewrite Nat.add_0_r, Z2Nat.id in BLK23 by lia.
    zstep. zstep. zstep. zstep. zstep.
    step. ubr.
    zstep. zstep. zstep. rqv_b2z. step. rqv_lit_branch.
    step. ubr.
    remember (A + (o + l))%Z as V eqn:EV.
    replace (wz (A + o + l)) with (wz V) by (f_equal; lia).
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

    assert (FAIL : forall (a1v a2v a3v a4v a5v s9v : word) mm, munch [(A + (o + l), A + (o + l) + 1); (P + 440, P + 444); (P + 448, P + 452); (P + 4, P + 8)]%Z m mm -> wmono rsegs m mm -> mem_inv rsegs mm ->
      rw_cells rsegs mm (q + 8) [C8 (wz MTAB)] -> FIX mm -> rw_cells rsegs mm (q + 72) [C8 (wz (A + o)); C8 (wz l)] ->
      rw_cells rsegs mm A [CB n (firstn (Z.to_nat (o + l)) bs ++ [b] ++ skipn (Z.to_nat (o + l) + 1) bs)] ->
      rw_cells rsegs mm (P + 276) [C4 (wz maj)] -> rw_cells rsegs mm (P + 280) [C4 (wz min)] ->
      rw_cells rsegs mm (P + 440) [C4 (wz err); C4 (wz hack); C4 (wz pos); C4 (wz entp); C4 (wz clen); C4 (wz 0); C8 (wz csz); C8 (wz esp)] ->
      rw_cells rsegs mm P [C4 (wz 1); C4 (wz meth)] -> u64arr rsegs mm MTAB mws ->
      evt rsegs POSTV (PRS 0x15fc8 x1 t0 t1 t2 (wz 3) a1v a2v a3v a4v a5v a6 a7 (wz (bv_unsigned b)) s9v t3 t4 t5 t6 gp tp F fc mm)).
    { intros a1v a2v a3v a4v a5v s9v mm MU' WM' MI' Q8' FX' Q72' BLK' C1' C2' CTL' MC' TAB'.
      clear MU WM MI Q8 FX Q72 BLK C1c C2c CTL MC TAB.
      zstep. rqv_sstep. zstep.
      unfold POSTV. apply evt_done. eexists _, 3, 505, meth, pos. do 8 eexists. split; [reflexivity|]. split; [exact MU'|]. split; [exact WM'|]. split; [eassumption|].
      repeat (split; [eassumption|]). split; [left; repeat split; reflexivity| reflexivity]. }
    zstep. if_cases K; zify_cond K; condn K.
    { eapply FAIL; eassumption. }
    assert (R2 : r = 2).
    { change 18446744073709551615%Z with (Z.ones 64) in K. rewrite Z.land_ones in K by lia.
      destruct RR as [->|RR']; [cbv in K; lia|]. rewrite Z.mod_small in K by lia. exact K. }
    subst r.
    zstep. zstep. rewrite (sx32_lit maj) by lia. zstep. if_cases K1; zify_cond K1.
    { eapply FAIL; eassumption. }
    assert (MJ0 : (0 <= maj)%Z) by (destruct (Z.lt_ge_cases maj 0); [rqv_sgn K1 maj; lia| lia]).
    pose proof (u64arr_read4 _ MTAB mws (2 * idx + 1) (wz id) (Z_to_bv 64 (MTAB + Z.shiftl idx 4 + 8)) TAB HN ltac:(lia)
                  ltac:(unfold wa; f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia)) as RD.
    assert (OK : forall (a0v a2v a3v a4v a5v s9v : word) mm, munch [(A + (o + l), A + (o + l) + 1); (P + 440, P + 444); (P + 448, P + 452); (P + 4, P + 8)]%Z m mm -> wmono rsegs m mm -> mem_inv rsegs mm ->
      rw_cells rsegs mm (q + 8) [C8 (wz MTAB)] -> FIX mm -> rw_cells rsegs mm (q + 72) [C8 (wz (A + o)); C8 (wz l)] ->
      rw_cells rsegs mm A [CB n (firstn (Z.to_nat (o + l)) bs ++ [b] ++ skipn (Z.to_nat (o + l) + 1) bs)] ->
      rw_cells rsegs mm (P + 276) [C4 (wz maj)] -> rw_cells rsegs mm (P + 280) [C4 (wz min)] ->
      rw_cells rsegs mm (P + 440) [C4 (wz err); C4 (wz hack); C4 (wz pos); C4 (wz entp); C4 (wz clen); C4 (wz 0); C8 (wz csz); C8 (wz esp)] ->
      rw_cells rsegs mm P [C4 (wz 1); C4 (wz meth)] -> u64arr rsegs mm MTAB mws ->
      evt rsegs POSTV (PRS 0x15f38 x1 t0 t1 t2 a0v (wz (Z.shiftl idx 4)) a2v a3v a4v a5v a6 a7 (wz (bv_unsigned b)) s9v t3 t4 t5 t6 gp tp F fc mm)).
    { intros a0v a2v a3v a4v a5v s9v mm MU' WM' MI' Q8' FX' Q72' BLK' C1' C2' CTL' MC' TAB'.
      clear MU WM MI Q8 FX Q72 BLK C1c C2c CTL MC TAB K K1.
      pose proof (u64arr_read4 mm MTAB mws (2 * idx + 1) (wz id) (Z_to_bv 64 (MTAB + Z.shiftl idx 4 + 8)) TAB' HN ltac:(lia)
                    ltac:(unfold wa; f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia)) as RD'.
      zstep. zstep. zstep. rewrite (sx32_lit id) by lia. rqv_sstep. rqv_sstep. zstep. zstep.
      unfold POSTV. apply evt_done. eexists _, 4, err, id, 2. do 8 eexists. split; [reflexivity|]. split; [exact MU'|]. split; [exact WM'|]. split; [eassumption|].
      repeat (split; [eassumption|]). split; [right; repeat split; try reflexivity; lia| reflexivity]. }
    assert (CHK : forall (a2v a3v a4v a5v : word) mm, munch [(A + (o + l), A + (o + l) + 1); (P + 440, P + 444); (P + 448, P + 452); (P + 4, P + 8)]%Z m mm -> wmono rsegs m mm -> mem_inv rsegs mm ->
      rw_cells rsegs mm (q + 8) [C8 (wz MTAB)] -> FIX mm -> rw_cells rsegs mm (q + 72) [C8 (wz (A + o)); C8 (wz l)] ->
      rw_cells rsegs mm A [CB n (firstn (Z.to_nat (o + l)) bs ++ [b] ++ skipn (Z.to_nat (o + l) + 1) bs)] ->
      rw_cells rsegs mm (P + 276) [C4 (wz maj)] -> rw_cells rsegs mm (P + 280) [C4 (wz min)] ->
      rw_cells rsegs mm (P + 440) [C4 (wz err); C4 (wz hack); C4 (wz pos); C4 (wz entp); C4 (wz clen); C4 (wz 0); C8 (wz csz); C8 (wz esp)] ->
      rw_cells rsegs mm P [C4 (wz 1); C4 (wz meth)] -> u64arr rsegs mm MTAB mws ->
      evt rsegs POSTV (PRS 0x15f20 x1 t0 t1 t2 (wz 3) (wz (Z.shiftl idx 4)) a2v a3v a4v a5v a6 a7 (wz (bv_unsigned b)) (wz idx) t3 t4 t5 t6 gp tp F fc mm)).
    { intros a2v a3v a4v a5v mm MU' WM' MI' Q8' FX' Q72' BLK' C1' C2' CTL' MC' TAB'.
      zstep. zstep. step. ubr. zstep. zstep. rqv_b2z. step. rqv_lit_branch.
      eapply OK; eassumption. }
    zstep. zstep. if_cases K2; zify_cond K2; condn K2.
    { eapply CHK; eassumption. }
    zstep. zstep. rewrite (sx32_lit min) by lia. zstep. if_cases K3; zify_cond K3.
    2:{ eapply CHK; eassumption. }
    zstep. zstep. step. ubr. zstep. step. ubr.
    zstep. zstep. zstep. zstep. rewrite (sx32_lit id) by lia. zstep. zstep. if_cases K4; zify_cond K4; condn K4.
    { step; try rqv_lit_branch. eapply OK; eassumption. }
    eapply FAIL; eassumption.
    Unshelve. all: try exact (wz 0); try exact m.
  Qed.

  Hypothesis Q8A : (q mod 8 = 0)%Z.

  #[using="SNC QLO LO0 QP PHI Q8A MWSL MID MT"] Lemma rqv_vtail : forall (A len cap o1 l1 o3 l3 err meth pos hack entp clen csz esp maj min : Z) (bs sl : list byte) (bcr : byte)
      (j8 s9v canary errv tp : word) gp t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 (F : bvmap 5 word) fc m,
    mem_inv rsegs m -> stk rsegs m lo q -> bv_unsigned tp = 0x3b820%Z ->
    rw_cells rsegs m (q + 8) [C8 j8] -> FIX m -> rw_cells rsegs m (q + 72) [C8 (wz (A + o3)); C8 (wz l3)] -> rw_cells rsegs m (q + 88) [C8 (wz (A + o1)); C8 (wz l1)] ->
    rw_cells rsegs m A [CB (Z.to_nat (cap + 1)) bs] -> bytes_at rsegs m (A + (cap + 1)) sl ->
    (0 <= o1)%Z -> (1 <= l1)%Z -> (o1 + l1 < len)%Z -> (0 <= o3)%Z -> (0 <= l3)%Z -> (o3 + l3 < len)%Z -> (len <= cap)%Z -> (cap + 1 <= 2^26 + 16)%Z -> (4096 <= A)%Z ->
    ((A + (cap + 1) + Z.of_nat (length sl)) mod 8 = 0)%Z -> (Z.of_nat (length sl) <= 8)%Z -> (A + (cap + 1) + Z.of_nat (length sl) <= lo)%Z ->
    (A + (cap + 1) + Z.of_nat (length sl) <= 0x2a000 \/ 0x5d000 <= A)%Z ->
    nth_error bs (Z.to_nat (o3 + l3)) = Some bcr -> (bv_unsigned bcr = 13 \/ bv_unsigned bcr = 10)%Z ->
    rw_cells rsegs m (P + 276) [C4 (wz maj)] -> rw_cells rsegs m (P + 280) [C4 (wz min)] -> (- 2^31 <= maj < 2^31)%Z -> (- 2^31 <= min < 2^31)%Z ->
    rw_cells rsegs m (P + 440) (rqv_ctl8 err hack pos entp clen csz esp) -> rw_cells rsegs m P [C4 (wz 1); C4 (wz meth)] ->
    (0 <= err < 2^31)%Z -> (0 <= meth <= 12)%Z -> (0 <= pos <= 4)%Z ->
    u64arr rsegs m MTAB mws -> ssp_cells m canary -> rw_cells rsegs m 0x3b77c [C4 errv] ->
    evt rsegs (fun ms' => exists m' (ra0 err' meth' pos' maj' min' : Z) (ev' j8' : word) x1 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s7' s9' t3' t4' t5' t6',
        ms' = PRS HEAD x1 t0' t1' t2' (wz ra0) a1' a2' a3' a4' a5' a6' a7' s7' s9' t3' t4' t5' t6' gp tp F fc m' /\ (a0' : word) = a0'
        /\ munch [(lo, q); (A + (o3 + l3), A + (o3 + l3) + 1); (P + 440, P + 444); (P + 448, P + 452); (P + 4, P + 8); (P + 276, P + 284); (q + 8, q + 16); (0x3b77c, 0x3b77c + 4)]%Z m m'
        /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo q
        /\ rw_cells rsegs m' (q + 8) [C8 j8'] /\ FIX m' /\ rw_cells rsegs m' (q + 72) [C8 (wz (A + o3)); C8 (wz l3)] /\ rw_cells rsegs m' (q + 88) [C8 (wz (A + o1)); C8 (wz l1)]
        /\ rw_cells rsegs m' A [CB (Z.to_nat (cap + 1)) bs] /\ bytes_at rsegs m' (A + (cap + 1)) sl
        /\ rw_cells rsegs m' (P + 276) [C4 (wz maj')] /\ rw_cells rsegs m' (P + 280) [C4 (wz min')] /\ (- 2^31 <= maj' < 2^31)%Z /\ (- 2^31 <= min' < 2^31)%Z
        /\ rw_cells rsegs m' (P + 440) (rqv_ctl8 err' hack pos' entp clen csz esp) /\ rw_cells rsegs m' P [C4 (wz 1); C4 (wz meth')]
        /\ u64arr rsegs m' MTAB mws /\ ssp_cells m' canary /\ rw_cells rsegs m' 0x3b77c [C4 ev']
        /\ ( (ra0 = 3 /\ pos' = pos /\ meth' = meth /\ (err' = 501 \/ err' = 505))
           \/ (ra0 = 4 /\ err' = err /\ 0 <= meth' <= 11 /\ pos' = 2) )%Z)
      (PRS map_str_to_int_entry (wz 0x15e7c) t0 t1 t2 (wz (A + o1)) (wz l1) (wz MTAB) (wz 11) (wz 1) a5 a6 a7 (wz MTAB) s9v t3 t4 t5 t6 gp tp F fc m).
  Proof.
    intros until m. intros MI ST TPV Q8 FX Q72 Q88 BLK SLK O1 L1 OL1 O3 L3 OL3 LC CMX A4 AL8 SL8 ALO WIN Hbcr CRLF PMJ PMN MJR MNR CTL MC ER MR PR TAB [SSP1 SSP2] ERR.
    unfold got_ssp, ssp_guard in SSP1, SSP2.
    pose proof (bytes_at_bound _ _ _ _ SLK) as BSL.
    assert (LBS : length bs = Z.to_nat (cap + 1)) by (destruct BLK as [[W _] _]; cbn in W; LiaTuning.ctauto).
    assert (EQ : bv_unsigned (wz q) = q) by (apply unsigned_lit; lia).

    set (tok := firstn (Z.to_nat l1) (skipn (Z.to_nat o1) bs)).
    assert (LT : Z.of_nat (length tok) = l1). { subst tok. rewrite firstn_length_le; [lia|]. rewrite length_skipn. lia. }
    assert (BT : bytes_at rsegs m (A + o1) tok).
    { pose proof (proj2 (proj1 BLK)) as BY. cbn [cells_bytes cbytes] in BY. rewrite app_nil_r in BY.
      rewrite <- (firstn_skipn (Z.to_nat o1) bs) in BY. apply bytes_at_app in BY. destruct BY as [_ BY].
      rewrite firstn_length_le in BY by lia. replace (A + Z.of_nat (Z.to_nat o1))%Z with (A + o1)%Z in BY by lia.
      rewrite <- (firstn_skipn (Z.to_nat l1) (skipn (Z.to_nat o1) bs)) in BY. apply bytes_at_app in BY. destruct BY as [BY _]. exact BY. }
    destruct (stk_split rsegs _ _ (q - 144)%Z _ ST ltac:(lia)) as [STlo SThi].
    pose proof (map_str_to_int_spec SNC) as MS_. unfold map_str_to_int_stmt in MS_.
    pose proof (munch_refl [(lo, q); (A + (o3 + l3), A + (o3 + l3) + 1); (P + 440, P + 444); (P + 448, P + 452); (P + 4, P + 8); (P + 276, P + 284); (q + 8, q + 16); (0x3b77c, 0x3b77c + 4)]%Z m) as MUacc.
    pose proof (wmono_refl rsegs m) as WMacc. rqv_stash MUacc. rqv_stash WMacc.
    eapply evt_cut.
    { eapply (MS_ (A + o1)%Z l1 MTAB 11 1 tok mws); rewrite ?EQ; try eassumption; try reflexivity; try lia.
      all: try (rewrite MWSL; reflexivity). all: try (eapply rqv_ts_mono; [exact MT| lia]). }
    clear MS_. intros ms1 PO. unfold map_str_to_int_post in PO. rewrite ?EQ in PO.
    destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & r & -> & MU1 & WM1 & MI1 & ST1 & RR).
    replace (ret_pc (wz 0x15e7c)) with (wz 0x15e7c : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (ST1' : stk rsegs m1 lo q).
    { eapply (stk_merge rsegs _ lo (q - 144)%Z q); [| exact ST1| lia]. eapply (stk_transport_disjoint rsegs); [exact STlo| exact MU1| exact WM1| cbn; lia]. }
    clear STlo SThi ST1 ST BT. transport_after_call rsegs m m1 MU1 WM1.
    rqv_unstash. apply (munch_trans _ _ _ m1) in MUacc. 2:{ eapply munch_weaken; [| exact MU1]. unfold sub_fp; cbn [outside]; intros; lia. }
    apply (wmono_trans rsegs _ _ m1) in WMacc; [| exact WM1]. clear MU1 WM1 MI. rqv_stash MUacc. rqv_stash WMacc.

    unfold rqv_ctl8 in CTL.
    lazymatch type of CTL with rw_cells _ _ _ (?c0 :: ?rest) => destruct (proj1 (rw_cells_app rsegs m1 (P + 440) [c0] rest) CTL) as [EC CTL7]; cbn [cells_size csize Nat.add] in CTL7 end.
    eapply evt_cut.
    { eapply (rqv_msi r err A o3 l3 (Z.to_nat (cap + 1)) bs j8); try eassumption; try LiaTuning.alia. }
    cbv beta. intros ms2 (m2 & ALT).
    destruct ALT as [(-> & -> & MU2 & WM2 & MI2 & EC2 & Q82 & FX2 & Q722 & BLK2)|(b & R0 & Hb & -> & MU2 & WM2 & MI2 & EC2 & Q82 & FX2 & Q722 & BLK2)].
    {
      clear EC Q8 FX Q72 BLK CTL. transport_after_call rsegs m1 m2 MU2 WM2.
      rqv_unstash. apply (munch_trans _ _ _ m2) in MUacc. 2:{ eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; intros; lia. }
      apply (wmono_trans rsegs _ _ m2) in WMacc; [| exact WM2].
      apply evt_done. eexists m2, 3, 501, meth, pos, maj, min, errv, j8. do 18 eexists. split; [reflexivity|]. split; [reflexivity|].
      split; [exact MUacc|]. split; [exact WMacc|]. split; [exact MI2|]. split; [exact ST1'|].
      split; [exact Q82|]. split; [exact FX2|]. split; [exact Q722|]. split; [eassumption|]. split; [exact BLK2|]. split; [eassumption|].
      split; [eassumption|]. split; [eassumption|]. split; [lia|]. split; [lia|].
      split. { unfold rqv_ctl8. apply (proj2 (rw_cells_app rsegs m2 (P + 440) [C4 (wz 501)] _)). split; [exact EC2|]. cbn [cells_size csize Nat.add]. eassumption. }
      split; [eassumption|]. split; [eassumption|]. split; [split; eassumption|]. split; [eassumption|].
      left. repeat split; try lia. }
    rewrite Hbcr in Hb. injection Hb as <-.
    set (k := (o3 + l3)%Z) in *. assert (Hk : k = (o3 + l3)%Z) by reflexivity.
    change (firstn (Z.to_nat k) bs ++ [zb] ++ skipn (Z.to_nat k + 1) bs) with (set_byte bs (Z.to_nat k) zb) in BLK2.
    assert (ST2 : stk rsegs m2 lo q) by (eapply (stk_transport_disjoint rsegs); [exact ST1'| exact MU2| exact WM2| cbn; lia]).
    clear EC Q8 FX Q72 BLK CTL ST1'. transport_after_call rsegs m1 m2 MU2 WM2.
    rqv_unstash. apply (munch_trans _ _ _ m2) in MUacc. 2:{ eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; intros; lia. }
    apply (wmono_trans rsegs _ _ m2) in WMacc; [| exact WM2]. clear MU2 WM2 MI1. rqv_stash MUacc. rqv_stash WMacc.

    set (bs1 := set_byte bs (Z.to_nat k) zb) in *.
    assert (LB1 : length bs1 = length bs) by (subst bs1; apply set_byte_length; lia).
    assert (INZ : In zb (skipn (Z.to_nat o3) bs1)).
    { apply (nth_error_In _ (Z.to_nat l3)). rewrite nth_error_skipnZ. replace (Z.to_nat o3 + Z.to_nat l3)%nat with (Z.to_nat k) by lia. subst bs1. apply set_byte_same. lia. }
    destruct (first_nulB _ _ INZ) as (s & rr & SPLIT & NIN).
    set (txt := map bv_unsigned (skipn (Z.to_nat o3) bs1 ++ sl)). set (pre := map bv_unsigned s). set (post := map bv_unsigned (rr ++ sl)).
    assert (LS : (length s <= Z.to_nat l3)%nat).
    { destruct (Nat.le_gt_cases (length s) (Z.to_nat l3)) as [LE|GT]; [exact LE| exfalso]. apply NIN.
      apply (nth_error_In _ (Z.to_nat l3)). rewrite <- (nth_error_app1 s (zb :: rr)) by lia. rewrite <- SPLIT, nth_error_skipnZ.
      replace (Z.to_nat o3 + Z.to_nat l3)%nat with (Z.to_nat k) by lia. subst bs1. apply set_byte_same. lia. }
    assert (LSK : length (skipn (Z.to_nat o3) bs1) = (length s + 1 + length rr)%nat) by (rewrite SPLIT, length_app; cbn; lia).
    rewrite length_skipn in LSK.
    assert (TXT : rtext (A + o3) txt pre post).
    { unfold rtext. split.
      { subst txt pre post. rewrite SPLIT, <- app_assoc. cbn [app]. rewrite map_app. cbn [map]. replace (bv_unsigned zb) with 0%Z by (vm_compute; reflexivity). reflexivity. }
      split.
      { subst pre. apply Forall_map. apply Forall_forall. intros bb Hbb. cbv beta. pose proof (byte_range bb) as R.
        assert (bb <> zb) by (intros ->; exact (NIN Hbb)). enough (bv_unsigned bb <> 0)%Z by lia.
        intros E. apply H. apply bv_eq. rewrite E. vm_compute. reflexivity. }
      split.
      { subst txt. apply Forall_map. apply Forall_forall. intros bb _. cbv beta. pose proof (byte_range bb). lia. }
      split.
      { subst pre post. unfold Prelim.zlength. rewrite ?length_map, ?map_length, ?length_app, ?app_length, ?length_map, ?map_length.
        enough (HH : ((- (A + o3 + Z.of_nat (length s) + 1)) mod 8 <= A + (cap + 1) + Z.of_nat (length sl) - (A + o3 + Z.of_nat (length s) + 1))%Z) by lia.
        set (N := (A + o3 + Z.of_nat (length s) + 1)%Z). set (E8 := (A + (cap + 1) + Z.of_nat (length sl))%Z) in *.
        assert (HN : (N <= E8)%Z) by (subst N E8; lia).
        rewrite <- (Z.mod_add (- N) (E8 / 8) 8) by lia.
        replace (- N + E8 / 8 * 8)%Z with (E8 - N)%Z by (Z.div_mod_to_equations; lia).
        apply Z.mod_le; lia. }
      subst txt. unfold Prelim.zlength. rewrite ?length_map, ?map_length, ?length_app, ?app_length, ?length_skipn, ?skipn_length. lia. }
    assert (BYT : bytes_at rsegs m2 (A + o3) (zbytes txt)).
    { subst txt. rewrite zbytes_bytes. apply bytes_at_app. split.
      - pose proof (proj2 (proj1 BLK2)) as BB1. cbn [cells_bytes cbytes] in BB1. rewrite app_nil_r in BB1.
        rewrite <- (firstn_skipn (Z.to_nat o3) bs1) in BB1. apply bytes_at_app in BB1. destruct BB1 as [_ BB1].
        rewrite firstn_length_le in BB1 by lia. replace (A + Z.of_nat (Z.to_nat o3))%Z with (A + o3)%Z in BB1 by lia. exact BB1.
      - rewrite length_skipn. replace (A + o3 + Z.of_nat (length bs1 - Z.to_nat o3))%Z with (A + (cap + 1))%Z by lia. exact SLK. }
    assert (LTXT : Prelim.zlength txt = (cap + 1 - o3 + Z.of_nat (length sl))%Z).
    { subst txt. unfold Prelim.zlength. rewrite ?length_map, ?map_length, ?length_app, ?app_length, ?length_skipn, ?skipn_length. lia. }

    pose proof sscanf_version_spec as SS. unfold sscanf_version_stmt, SSCANF_DEPTH, ERRNOA, FA_VERSION in SS.
    eapply evt_cut.
    { eapply SS with (sp := wz q) (txt := txt) (pre := pre) (post := post) (lo := lo) (canary := canary); rewrite ?EQ;
        first [ exact TXT | exact BYT | eassumption | unfold ssp_cells, got_ssp, ssp_guard; split; eassumption | apply unsigned_lit; lia | lia ]. }
    clear SS. intros ms3 PO. unfold sscanf2_post, ERRNOA in PO.
    destruct PO as (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m3 & ev & v1 & v2 & rs
                    & -> & SM & RRS & MU3 & WM3 & MI3 & ST3 & BYT3 & [SSP1' SSP2'] & ERR3 & PC1 & PC2).
    unfold got_ssp, ssp_guard in SSP1', SSP2'. rewrite EQ in MU3, ST3.
    clear MI2 ST2 BYT PMJ PMN SSP1 SSP2 ERR.
    transport_after_call rsegs m2 m3 MU3 WM3.
    rqv_unstash. apply (munch_trans _ _ _ m3) in MUacc. 2:{ eapply munch_weaken; [| exact MU3]. unfold sub_fp; cbn [outside]; intros; lia. }
    apply (wmono_trans rsegs _ _ m3) in WMacc; [| exact WM3]. clear MU3 WM3. rqv_stash MUacc. rqv_stash WMacc.
    apply rw_cells_C4_s32v in PC1. apply rw_cells_C4_s32v in PC2.
    pose proof (s32v_range v1) as R1. pose proof (s32v_range v2) as R2.
    replace (ret_pc (wz 0x15ecc)) with (wz 0x15ecc : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

    destruct (MID r ltac:(lia)) as (id & HN & IDR).
    assert (CTL3 : rw_cells rsegs m3 (P + 440) (rqv_ctl8 err hack pos entp clen csz esp)).
    { unfold rqv_ctl8. apply (proj2 (rw_cells_app rsegs m3 (P + 440) [C4 (wz err)] _)). split; [exact EC2|]. cbn [cells_size csize Nat.add]. exact CTL7. }
    clear EC2 CTL7.
    eapply evt_cut.
    { eapply (rqv_ver rs r id A o3 l3 (s32v v1) (s32v v2) err meth pos (Z.to_nat (cap + 1)) bs1 bcr); try eassumption; try LiaTuning.alia. }
    cbv beta. intros ms4 (m4 & ra0 & err' & meth' & pos' & a0_4 & a1_4 & a2_4 & a3_4 & a4_4 & a5_4 & s7_4 & s9_4 & -> & MU4 & WM4 & MI4 & Q84 & FX4 & Q724 & BLK4 & PC14 & PC24 & CTL4 & MC4 & TAB4 & ALT & _).
    fold k in MU4, BLK4.
    change (firstn (Z.to_nat k) bs1 ++ [bcr] ++ skipn (Z.to_nat k + 1) bs1) with (set_byte bs1 (Z.to_nat k) bcr) in BLK4.
    assert (RESTORE : set_byte bs1 (Z.to_nat k) bcr = bs) by (subst bs1; apply set_byte_restore; subst k; exact Hbcr). rewrite RESTORE in BLK4. clear RESTORE.
    clear BYT3 BLK2 MI3 Q82 FX2 Q722 PC1 PC2 CTL3 MC TAB.
    transport_after_call rsegs m3 m4 MU4 WM4.
    rqv_unstash. apply (munch_trans _ _ _ m4) in MUacc. 2:{ eapply munch_weaken; [| exact MU4]. unfold sub_fp; cbn [outside]; intros; subst k; lia. }
    apply (wmono_trans rsegs _ _ m4) in WMacc; [| exact WM4]. clear MU4 WM4.
    apply evt_done. exists m4, ra0, err', meth', pos', (s32v v1), (s32v v2), ev, (wz MTAB). do 18 eexists. split; [reflexivity|]. split; [reflexivity|].
    split; [subst k; exact MUacc|]. split; [exact WMacc|]. split; [exact MI4|]. split; [assumption|].
    split; [exact Q84|]. split; [exact FX4|]. split; [subst k; exact Q724|]. split; [eassumption|]. split; [exact BLK4|]. split; [eassumption|].
    split; [exact PC14|]. split; [exact PC24|]. split; [lia|]. split; [lia|].
    split; [exact CTL4|]. split; [exact MC4|]. split; [exact TAB4|]. split; [split; eassumption|]. split; [eassumption|].
    destruct ALT as [(-> & -> & -> & ->)|(-> & -> & -> & -> & _ & _)]; [left| right]; repeat split; lia.
    Unshelve. all: try exact (wz 0); try exact 0%Z.
  Qed.
End RQV.
