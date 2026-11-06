(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From stdpp Require Import base list.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Arr.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import ScanInt.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac CellConv.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.P0 Require Import Segs F_syscalls Stdio_base F_shgetc_A F_shgetc_B F_strtol F_vfscanf_lib F_sscanf H_map_str_to_int H_memptr_cmp H_presp_A H_presp_B.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.P0 Require Import H_reql_A.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Ceiling.
Import ListNotations.
Open Scope Z_scope.
Set Printing Width 1000.
Set Printing Depth 100.

Notation zb := (Z_to_bv 8 0).

Definition hiddenV (P : Prop) := P.
Ltac stash H := lazymatch type of H with hiddenV _ => idtac | ?T => change T with (hiddenV T) in H end.
Ltac unstash := unfold hiddenV in *.

Lemma rw_cells_C8_C44s : forall m X (w : word),
  rw_cells rsegs m X [C8 w] -> exists a b : word, rw_cells rsegs m X [C4 a; C4 b] /\ le_bytes_to_word (le4 a ++ le4 b) = w.
Proof.
  intros m X w H.
  pose proof (rw_cells_split_CB rsegs m X [] 8 (le8 w) [] [4; 4]%nat) as SP. cbn [app mk_CB_cells] in SP.
  assert (H8 : rw_cells rsegs m X [CB 8 (le8 w)]).
  { destruct H as [[W B] R]. split; [split; [cbn; split; [reflexivity| exact I]| exact B]| exact R]. }
  specialize (SP H8 eq_refl).
  pose proof (rw_cells_CB_C4 rsegs m X [] (firstn 4 (le8 w)) [CB 4 (firstn 4 (skipn 4 (le8 w)))] SP) as S1. cbn [app] in S1.
  pose proof (rw_cells_CB_C4 rsegs m X [C4 (le_bytes_to_word (firstn 4 (le8 w)))] (firstn 4 (skipn 4 (le8 w))) [] S1) as S2. cbn [app] in S2.
  eexists _, _. split; [exact S2|].
  pose proof (length_le8 w) as L8.
  rewrite !le4_of_bytes by (rewrite ?firstn_length, ?length_firstn, ?skipn_length, ?length_skipn; lia).
  rewrite (firstn_all2 (skipn 4 (le8 w))) by (rewrite length_skipn; lia). rewrite firstn_skipn. apply le_bytes_to_word_le8.
Qed.

Section VT.
Context {HCEIL : HasCeiling}.
  Hypothesis SNC : strncasecmp_stmt.
  Variables (P q lo : Z).
  Notation S := (P + 480)%Z.
  Notation MB := (P + 400)%Z.
  Hypothesis QLO : (lo + 1096 <= q)%Z.
  Hypothesis LO0 : (0x5c000 <= lo)%Z.
  Hypothesis QP : (q + 192 <= P)%Z.
  Hypothesis PHI : (P + 504 < 2^62)%Z.
  Variable mws : list word.
  Hypothesis MWSL : length mws = 22%nat.
  Hypothesis MID : forall i, (0 <= i < 11)%Z -> exists id, nth_error mws (Z.to_nat (2 * i + 1)) = Some (wz id) /\ (0 <= id <= 11)%Z.
  Hypothesis MT : table_strings mws 11 lo.

  #[using="QLO mws MWSL"] Lemma QLO1 : (lo <= q)%Z. Proof. lia. Qed.
  #[using="PHI mws MWSL"] Lemma PHI63 : (P + 504 < 2^63)%Z. Proof. lia. Qed.
  #[using="MWSL MID"] Lemma MID' : forall i, (0 <= i < 11)%Z -> exists id, nth_error mws (Z.to_nat (2 * i + 1)) = Some (wz id) /\ (0 <= id < 64)%Z.
  Proof. intros i Hi. destruct (MID i Hi) as (id & H1 & H2). exists id. split; [exact H1| lia]. Qed.

  Notation PRS pc x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7v s8v s9v t3 t4 t5 t6 gp tp F fc m :=
    (MS (mkR x1 (wz q) gp tp t0 t1 t2 (wz P) (wz S) a0 a1 a2 a3 a4 a5 a6 a7 (wz 3) (wz 47) (wz 2) (wz FMT09) (wz MTAB) s7v s8v s9v (wz 1) (wz 4) t3 t4 t5 t6)
        F (wz pc) fc None m (seg_rom rsegs)).
  Notation S7 := (wz (P + 8)). Notation S8 := (wz (P + 276)). Notation S9 := (wz (P + 280)).

  #[using="mws MWSL"] Lemma rq_mreq : forall (r : Z) (ub ul : word) gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 x1 s7v (F : bvmap 5 word) fc m,
    mem_inv rsegs m -> rw_cells rsegs m (q + 40) [C8 ub; C8 ul] -> (0 <= r <= 5)%Z ->
    evt rsegs (fun ms' =>
        ( r <> 4 /\ ms' = PRS HEAD x1 t0 t1 t2 (wz r) a1 a2 a3 a4 a5 a6 a7 s7v S8 S9 t3 t4 t5 t6 gp tp F fc m)
     \/ ( r = 4 /\ ms' = PRS 0x156e0 x1 t0 t1 t2 ub a1 ul a3 a4 a5 a6 a7 s7v S8 S9 t3 t4 t5 t6 gp tp F fc m))
      (PRS 0x156d4 x1 t0 t1 t2 (wz r) a1 a2 a3 a4 a5 a6 a7 s7v S8 S9 t3 t4 t5 t6 gp tp F fc m).
  Proof.
    intros until m. intros MI Q40 RR.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    zstep. if_cases K; zify_cond K; condn K.
    - apply evt_done. left. split; [lia| reflexivity].
    - zstep. zstep. apply evt_done. right. split; [lia| reflexivity].
  Qed.

  #[using="mws MWSL"] Lemma table_strings_monoV : forall ws ne B B', table_strings ws ne B -> (B <= B')%Z -> table_strings ws ne B'.
  Proof.
    intros ws ne B B' TS LE i Hi. destruct (TS i Hi) as (Sx & str & slack & H1 & H2 & H3 & H4 & H5).
    exists Sx, str, slack. repeat (split; [assumption|]). lia.
  Qed.

  #[using="SNC QLO LO0 QP PHI MWSL MID MT"] Lemma rq_vtail : forall (A len cap o1 l1 o3 l3 err meth pos hack entp clen csz esp maj min : Z) (bs sl : list byte) (bcr : byte)
      (j8 canary errv tp : word) gp t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 (F : bvmap 5 word) fc m,
    mem_inv rsegs m -> stk rsegs m lo q -> bv_unsigned tp = 0x3ad30%Z ->
    rw_cells rsegs m (q + 8) [C8 j8; C8 S9; C8 S8] -> rw_cells rsegs m (q + 56) [C8 (wz (A + o3)); C8 (wz l3)] -> rw_cells rsegs m (q + 72) [C8 (wz (A + o1)); C8 (wz l1)] ->
    rw_cells rsegs m A [CB (Z.to_nat (cap + 1)) bs] -> bytes_at rsegs m (A + (cap + 1)) sl ->
    (0 <= o1)%Z -> (1 <= l1)%Z -> (o1 + l1 < len)%Z -> (0 <= o3)%Z -> (0 <= l3)%Z -> (o3 + l3 < len)%Z -> (len <= cap)%Z -> (cap + 1 <= 2^26 + 16)%Z -> (4096 <= A)%Z ->
    ((A + (cap + 1) + Z.of_nat (length sl)) mod 8 = 0)%Z -> (Z.of_nat (length sl) <= 8)%Z -> (A + (cap + 1) + Z.of_nat (length sl) <= lo)%Z ->
    (A + (cap + 1) + Z.of_nat (length sl) <= 0x29000 \/ 0x5c000 <= A)%Z ->
    nth_error bs (Z.to_nat (o3 + l3)) = Some bcr -> (bv_unsigned bcr = 13 \/ bv_unsigned bcr = 10)%Z ->
    rw_cells rsegs m (P + 276) [C4 (wz maj)] -> rw_cells rsegs m (P + 280) [C4 (wz min)] -> (- 2^31 <= maj < 2^31)%Z -> (- 2^31 <= min < 2^31)%Z ->
    rw_cells rsegs m (P + 440) (ctl8 err hack pos entp clen csz esp) -> rw_cells rsegs m P [C4 (wz 1); C4 (wz meth)] ->
    (0 <= err < 2^31)%Z -> (0 <= meth <= 12)%Z -> (0 <= pos <= 4)%Z ->
    u64arr rsegs m MTAB mws -> ssp_cells m canary -> rw_cells rsegs m 0x3ac8c [C4 errv] ->
    evt rsegs (fun ms' => exists m' (ra0 err' meth' pos' maj' min' : Z) (ev' j8' : word) x1 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
        ms' = PRS HEAD x1 t0' t1' t2' (wz ra0) a1' a2' a3' a4' a5' a6' a7' S7 S8 S9 t3' t4' t5' t6' gp tp F fc m' /\ (a0' : word) = a0'
        /\ munch [(lo, q); (A + (o3 + l3), A + (o3 + l3) + 1); (P + 440, P + 444); (P + 448, P + 452); (P + 4, P + 8); (P + 276, P + 284); (q + 8, q + 16); (0x3ac8c, 0x3ac8c + 4)]%Z m m'
        /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo q
        /\ rw_cells rsegs m' (q + 8) [C8 j8'; C8 S9; C8 S8] /\ rw_cells rsegs m' (q + 56) [C8 (wz (A + o3)); C8 (wz l3)] /\ rw_cells rsegs m' (q + 72) [C8 (wz (A + o1)); C8 (wz l1)]
        /\ rw_cells rsegs m' A [CB (Z.to_nat (cap + 1)) bs] /\ bytes_at rsegs m' (A + (cap + 1)) sl
        /\ rw_cells rsegs m' (P + 276) [C4 (wz maj')] /\ rw_cells rsegs m' (P + 280) [C4 (wz min')] /\ (- 2^31 <= maj' < 2^31)%Z /\ (- 2^31 <= min' < 2^31)%Z
        /\ rw_cells rsegs m' (P + 440) (ctl8 err' hack pos' entp clen csz esp) /\ rw_cells rsegs m' P [C4 (wz 1); C4 (wz meth')]
        /\ u64arr rsegs m' MTAB mws /\ ssp_cells m' canary /\ rw_cells rsegs m' 0x3ac8c [C4 ev']
        /\ ( (ra0 = 3 /\ pos' = pos /\ meth' = meth /\ (err' = 501 \/ err' = 505))
           \/ (ra0 = 4 /\ err' = err /\ 0 <= meth' <= 11 /\ pos' = 2) )%Z)
      (PRS map_str_to_int_entry (wz 0x15788) t0 t1 t2 (wz (A + o1)) (wz l1) (wz MTAB) (wz 11) (wz 1) a5 a6 a7 S7 (wz MTAB) S9 t3 t4 t5 t6 gp tp F fc m).
  Proof.
    intros until m. intros MI ST TPV Q8 Q56 Q72 BLK SLK O1 L1 OL1 O3 L3 OL3 LC CMX A4 AL8 SL8 ALO WIN Hbcr CRLF PMJ PMN MJR MNR CTL MC ER MR PR TAB [SSP1 SSP2] ERR.
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
    pose proof (munch_refl [(lo, q); (A + (o3 + l3), A + (o3 + l3) + 1); (P + 440, P + 444); (P + 448, P + 452); (P + 4, P + 8); (P + 276, P + 284); (q + 8, q + 16); (0x3ac8c, 0x3ac8c + 4)]%Z m) as MUacc.
    pose proof (wmono_refl rsegs m) as WMacc. stash MUacc. stash WMacc.
    eapply evt_cut.
    { eapply (MS_ (A + o1)%Z l1 MTAB 11 1 tok mws); rewrite ?EQ; try eassumption; try reflexivity; try lia.
      all: try (rewrite MWSL; reflexivity). all: try (eapply table_strings_monoV; [exact MT| lia]). }
    clear MS_. intros ms1 PO. unfold map_str_to_int_post in PO. rewrite ?EQ in PO.
    destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & r & -> & MU1 & WM1 & MI1 & ST1 & RR).
    replace (ret_pc (wz 0x15788)) with (wz 0x15788 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (ST1' : stk rsegs m1 lo q).
    { eapply (stk_merge rsegs _ lo (q - 144)%Z q); [| exact ST1| lia]. eapply (stk_transport_disjoint rsegs); [exact STlo| exact MU1| exact WM1| cbn; lia]. }
    clear STlo SThi ST1 ST BT. transport_after_call rsegs m m1 MU1 WM1.
    unstash. apply (munch_trans _ _ _ m1) in MUacc. 2:{ eapply munch_weaken; [| exact MU1]. unfold sub_fp; cbn [outside]; intros; lia. }
    apply (wmono_trans rsegs _ _ m1) in WMacc; [| exact WM1]. clear MU1 WM1 MI. stash MUacc. stash WMacc.

    unfold ctl8 in CTL.
    lazymatch type of CTL with rw_cells _ _ _ (?c0 :: ?rest) => destruct (proj1 (rw_cells_app rsegs m1 (P + 440) [c0] rest) CTL) as [EC CTL7]; cbn [cells_size csize Nat.add] in CTL7 end.
    eapply evt_cut.
    { eapply (rq_msi P q lo QLO1 QP PHI63 r err A o3 l3 (Z.to_nat (cap + 1)) bs j8); try eassumption; try LiaTuning.alia. }
    cbv beta. intros ms2 (m2 & ALT).
    destruct ALT as [(-> & -> & MU2 & WM2 & MI2 & EC2 & Q82 & Q562 & BLK2)|(b & R0 & Hb & -> & MU2 & WM2 & MI2 & EC2 & Q82 & Q562 & BLK2)].
    {
      clear EC Q8 Q56 BLK CTL. transport_after_call rsegs m1 m2 MU2 WM2.
      unstash. apply (munch_trans _ _ _ m2) in MUacc. 2:{ eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; intros; lia. }
      apply (wmono_trans rsegs _ _ m2) in WMacc; [| exact WM2].
      apply evt_done. eexists m2, 3, 501, meth, pos, maj, min, errv, j8. do 16 eexists. split; [reflexivity|]. split; [reflexivity|].
      split; [exact MUacc|]. split; [exact WMacc|]. split; [exact MI2|]. split; [exact ST1'|].
      split; [exact Q82|]. split; [exact Q562|]. split; [eassumption|]. split; [exact BLK2|]. split; [eassumption|].
      split; [eassumption|]. split; [eassumption|]. split; [lia|]. split; [lia|].
      split. { unfold ctl8. apply (proj2 (rw_cells_app rsegs m2 (P + 440) [C4 (wz 501)] _)). split; [exact EC2|]. cbn [cells_size csize Nat.add]. eassumption. }
      split; [eassumption|]. split; [eassumption|]. split; [split; eassumption|]. split; [eassumption|].
      left. repeat split; try lia. }
    rewrite Hbcr in Hb. injection Hb as <-.
    set (k := (o3 + l3)%Z) in *. assert (Hk : k = (o3 + l3)%Z) by reflexivity.
    change (firstn (Z.to_nat k) bs ++ [zb] ++ skipn (Z.to_nat k + 1) bs) with (set_byte bs (Z.to_nat k) zb) in BLK2.
    assert (ST2 : stk rsegs m2 lo q) by (eapply (stk_transport_disjoint rsegs); [exact ST1'| exact MU2| exact WM2| cbn; lia]).
    clear EC Q8 Q56 BLK CTL ST1'. transport_after_call rsegs m1 m2 MU2 WM2.
    unstash. apply (munch_trans _ _ _ m2) in MUacc. 2:{ eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; intros; lia. }
    apply (wmono_trans rsegs _ _ m2) in WMacc; [| exact WM2]. clear MU2 WM2 MI1. stash MUacc. stash WMacc.

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
    unstash. apply (munch_trans _ _ _ m3) in MUacc. 2:{ eapply munch_weaken; [| exact MU3]. unfold sub_fp; cbn [outside]; intros; lia. }
    apply (wmono_trans rsegs _ _ m3) in WMacc; [| exact WM3]. clear MU3 WM3. stash MUacc. stash WMacc.
    apply rw_cells_C4_s32v in PC1. apply rw_cells_C4_s32v in PC2.
    pose proof (s32v_range v1) as R1. pose proof (s32v_range v2) as R2.
    replace (ret_pc (wz 0x157c0)) with (wz 0x157c0 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

    destruct (MID r ltac:(lia)) as (id & HN & IDR).
    assert (CTL3 : rw_cells rsegs m3 (P + 440) (ctl8 err hack pos entp clen csz esp)).
    { unfold ctl8. apply (proj2 (rw_cells_app rsegs m3 (P + 440) [C4 (wz err)] _)). split; [exact EC2|]. cbn [cells_size csize Nat.add]. exact CTL7. }
    clear EC2 CTL7.
    eapply evt_cut.
    { eapply (rq_ver P q lo QLO1 LO0 QP PHI63 mws MWSL rs r id A o3 l3 (s32v v1) (s32v v2) err meth pos (Z.to_nat (cap + 1)) bs1 bcr); try eassumption; try LiaTuning.alia. }
    cbv beta. intros ms4 (m4 & ra0 & err' & meth' & pos' & a0_4 & a1_4 & a2_4 & -> & MU4 & WM4 & MI4 & Q84 & Q564 & BLK4 & PC14 & PC24 & CTL4 & MC4 & TAB4 & ALT & _).
    fold k in MU4, BLK4.
    change (firstn (Z.to_nat k) bs1 ++ [bcr] ++ skipn (Z.to_nat k + 1) bs1) with (set_byte bs1 (Z.to_nat k) bcr) in BLK4.
    assert (RESTORE : set_byte bs1 (Z.to_nat k) bcr = bs) by (subst bs1; apply set_byte_restore; subst k; exact Hbcr). rewrite RESTORE in BLK4. clear RESTORE.
    clear BYT3 BLK2 MI3 Q82 Q562 PC1 PC2 CTL3 MC TAB.
    transport_after_call rsegs m3 m4 MU4 WM4.
    unstash. apply (munch_trans _ _ _ m4) in MUacc. 2:{ eapply munch_weaken; [| exact MU4]. unfold sub_fp; cbn [outside]; intros; subst k; lia. }
    apply (wmono_trans rsegs _ _ m4) in WMacc; [| exact WM4]. clear MU4 WM4.
    apply evt_done. exists m4, ra0, err', meth', pos', (s32v v1), (s32v v2), ev, S7. do 16 eexists. split; [reflexivity|]. split; [reflexivity|].
    split; [subst k; exact MUacc|]. split; [exact WMacc|]. split; [exact MI4|]. split; [assumption|].
    split; [exact Q84|]. split; [subst k; exact Q564|]. split; [eassumption|]. split; [exact BLK4|]. split; [eassumption|].
    split; [exact PC14|]. split; [exact PC24|]. split; [lia|]. split; [lia|].
    split; [exact CTL4|]. split; [exact MC4|]. split; [exact TAB4|]. split; [split; eassumption|]. split; [eassumption|].
    destruct ALT as [(-> & -> & -> & ->)|(-> & -> & -> & -> & _ & _)]; [left| right]; repeat split; lia.
    Unshelve. all: try exact (wz 0); try exact 0%Z.
  Qed.
End VT.

