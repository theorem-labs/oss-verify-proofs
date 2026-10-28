(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr ITree Nodes Decode.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF ITreeA.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg AProto ABase ABytes ARep ARepFrame ALayout AHeapP ASecFacts ASec ASecFrame
     AKitQ ARepQ ARepQP ARepKit ARepExt AFreeModel AFreeRep AFrameD FsKit AFake_iface.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Lemma granules_rup : forall n, 0 <= n -> granules n = shlen (rup n 8).
Proof.
  intros n N. unfold granules, shlen, rup. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
  Z.div_mod_to_equations. nia.
Qed.
Lemma rup8_facts : forall n, 0 <= n -> n <= rup n 8 <= n + 7 /\ rup n 8 mod 8 = 0 /\ shlen (rup n 8) = rup n 8 / 8.
Proof. intros n N. unfold rup, shlen. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations. nia. Qed.

Lemma achunk_eq_dec : forall c1 c2 : achunk, {c1 = c2} + {c1 <> c2}.
Proof. decide equality; apply Z.eq_dec. Defined.

Lemma filter_is_sec_perm : forall (l l' : list achunk), Permutation l l' -> Permutation (List.filter is_sec l) (List.filter is_sec l').
Proof.
  intros l l' HP. induction HP; cbn; [constructor| | |].
  - destruct (is_sec x); [apply perm_skip|]; assumption.
  - destruct (is_sec x), (is_sec y); try apply perm_swap; try apply perm_skip; try apply Permutation_refl.
  - eapply Permutation_trans; eassumption.
Qed.

(* [comment removed for export] *)
Lemma live_in_achunks : forall st (p : aptr) ch, (a_live st) !! p = Some ch -> In ch (achunks st).
Proof.
  intros st p ch L. unfold achunks. apply in_or_app. left.
  pose proof (map_to_list_delete (a_live st) p ch L) as P.
  apply (Permutation_map snd) in P. cbn [map snd] in P. eapply Permutation_in; [exact P| left; reflexivity].
Qed.
Lemma live_sec_in : forall st (p : aptr) mb ms n, (a_live st) !! p = Some (CSec mb ms n) -> In (CSec mb ms n) (sec_chunks_of st).
Proof. intros st p mb ms n L. unfold sec_chunks_of. apply List.filter_In. split; [eapply live_in_achunks; exact L| reflexivity]. Qed.

(* [comment removed for export] *)
Lemma sec_chunks_of_delete_sec : forall st st' (p : aptr) mb ms n,
  (a_live st) !! p = Some (CSec mb ms n) ->
  a_live st' = delete p (a_live st) ->
  Permutation (List.filter is_sec (flat_map b_chunks (a_qloc st' ++ a_qglob st')))
              (List.filter is_sec (flat_map b_chunks (a_qloc st ++ a_qglob st))) ->
  Permutation (CSec mb ms n :: sec_chunks_of st') (sec_chunks_of st).
Proof.
  intros st st' p mb ms n SOME E1 PQ. unfold sec_chunks_of, achunks. rewrite E1, !filter_is_sec_app.
  change (CSec mb ms n :: List.filter is_sec (map snd (map_to_list (delete p (a_live st)))) ++ List.filter is_sec (flat_map b_chunks (a_qloc st' ++ a_qglob st')))
    with ((CSec mb ms n :: List.filter is_sec (map snd (map_to_list (delete p (a_live st))))) ++ List.filter is_sec (flat_map b_chunks (a_qloc st' ++ a_qglob st'))).
  apply Permutation_app; [| exact PQ].
  pose proof (map_to_list_delete (a_live st) p (CSec mb ms n) SOME) as P.
  apply (Permutation_map snd) in P. cbn [map snd] in P. apply filter_is_sec_perm in P. cbn in P. exact P.
Qed.

(* [comment removed for export] *)
Lemma enq_app_qfilt_sec : forall s1 ch s, is_sec ch = true -> enq_app s1 ch = Some s ->
  Permutation (qfilt is_sec s) (ch :: qfilt is_sec s1).
Proof.
  intros s1 ch s Hf E. unfold enq_app in E.
  destruct (rev (a_qloc s1)) as [|b rl] eqn:RV; [discriminate|].
  destruct (b_count b =? Q_BATCH); [discriminate|]. injection E as <-.
  unfold qfilt. cbn [a_qloc a_qglob set_qloc].
  assert (QL : a_qloc s1 = rev rl ++ [b]) by (rewrite <- (rev_involutive (a_qloc s1)), RV; reflexivity).
  rewrite QL. cbn [rev]. rewrite !flat_map_app_chunks. cbn [flat_map b_chunks app]. rewrite !app_nil_r.
  rewrite !List.filter_app. cbn [List.filter]. rewrite Hf.
  rewrite <- !app_assoc. cbn [app]. apply Permutation_sym. apply Permutation_middle.
Qed.
Lemma enq_new_qfilt_sec : forall s1 ch, is_sec ch = true -> Permutation (qfilt is_sec (enq_new s1 ch)) (ch :: qfilt is_sec s1).
Proof.
  intros s1 ch Hf. unfold enq_new, qfilt. cbn [a_qloc a_qglob set_qloc put_cls set_cls].
  rewrite !flat_map_app_chunks. cbn [flat_map b_chunks app]. rewrite !List.filter_app. cbn [List.filter]. rewrite Hf.
  rewrite <- app_assoc. cbn [app]. apply Permutation_sym. apply Permutation_middle.
Qed.
Lemma st_enq_qfilt_sec : forall s1 ch, is_sec ch = true -> Permutation (qfilt is_sec (st_enq s1 ch)) (ch :: qfilt is_sec s1).
Proof.
  intros s1 ch Hf. unfold st_enq. destruct (enq_app s1 ch) as [s|] eqn:E; [exact (enq_app_qfilt_sec s1 ch s Hf E)| exact (enq_new_qfilt_sec s1 ch Hf)].
Qed.
Lemma st_after_enq_qfilt_sec : forall s1 ch, is_sec ch = true -> Permutation (qfilt is_sec (st_after (st_enq s1 ch))) (ch :: qfilt is_sec s1).
Proof.
  intros s1 ch Hf. eapply Permutation_trans; [apply st_after_qfilt| apply st_enq_qfilt_sec; exact Hf].
Qed.

(* [comment removed for export] *)
Lemma sec_chunks_of_free_sec : forall st (p : aptr) mb ms n s,
  (a_live st) !! p = Some (CSec mb ms n) ->
  a_live s = delete p (a_live st) ->
  Permutation (qfilt is_sec s) (CSec mb ms n :: qfilt is_sec st) ->
  Permutation (sec_chunks_of s) (sec_chunks_of st).
Proof.
  intros st p mb ms n s SOME EL PQ. unfold sec_chunks_of, achunks. rewrite EL, !filter_is_sec_app.
  pose proof (map_to_list_delete (a_live st) p (CSec mb ms n) SOME) as P.
  apply (Permutation_map snd) in P. cbn [map snd] in P. apply filter_is_sec_perm in P. cbn in P.
  unfold qfilt in PQ.
  eapply Permutation_trans; [apply Permutation_app_head; exact PQ|].
  eapply Permutation_trans; [apply Permutation_sym; apply Permutation_middle|].
  cbn [app]. rewrite app_comm_cons. apply Permutation_app_tail. exact P.
Qed.

(* [comment removed for export] *)
Lemma sec_chunks_of_quar_sec : forall s s' mb ms n,
  a_live s' = a_live s ->
  Permutation (qfilt is_sec s') (CSec mb ms n :: qfilt is_sec s) ->
  Permutation (sec_chunks_of s') (CSec mb ms n :: sec_chunks_of s).
Proof.
  intros s s' mb ms n EL PQ. unfold sec_chunks_of, achunks. rewrite EL, !filter_is_sec_app. unfold qfilt in PQ.
  eapply Permutation_trans; [apply Permutation_app_head; exact PQ|]. apply Permutation_sym. apply Permutation_middle.
Qed.

(* [comment removed for export] *)
Lemma awf_delete_sec : forall L st X (p : aptr) mb ms n s,
  awf L st X -> (a_live st) !! p = Some (CSec mb ms n) ->
  a_space_beg s = a_space_beg st -> a_ptr_array s = a_ptr_array st -> a_cinit s = a_cinit st -> a_cls s = a_cls st ->
  a_live s = delete p (a_live st) -> a_next s = a_next st ->
  awf L s X.
Proof.
  intros L st X p mb ms n s WF LIVE E1 E2 E3 E4 E5 E6.
  pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVEB & FRESH & UNIQ).
  assert (GC : forall c', get_cls s c' = get_cls st c') by (intros c'; unfold get_cls; rewrite E4; reflexivity).
  assert (MC : forall c', max_count s c' = max_count st c') by (intros c'; unfold max_count; rewrite E3; reflexivity).
  assert (ND : forall c', ndist s c' = ndist st c') by (intros c'; unfold ndist; rewrite GC; reflexivity).
  unfold awf. rewrite E1, E2, E5, E6.
  split; [exact SBE|]. split; [exact PAE|]. split; [exact SAL|]. split; [exact SLO|]. split; [exact SHI|].
  split. { intros c Hc. cbv zeta. rewrite GC, MC, ND. exact (PERC c Hc). }
  split. { intros c Hc. rewrite GC. exact (OUTC c Hc). }
  split. { intros b Hb. destruct (BUSY b Hb) as [CL M]. split; [exact CL|]. destruct (xb_st b) as [q| |]; [| exact M| exact M].
           destruct M as (M1 & M2 & M3 & M4 & M5 & M6). repeat (split; [assumption|]).
           rewrite lookup_delete_ne; [exact M6|]. intros ->. rewrite LIVE in M6. discriminate. }
  split. { intros q c n' Hq. apply lookup_delete_Some in Hq. destruct Hq as [_ Hq]. exact (LIVEB q c n' Hq). }
  split. { intros q ch Hq. apply lookup_delete_Some in Hq. destruct Hq as [_ Hq]. exact (FRESH q ch Hq). }
  exact UNIQ.
Qed.

(* [comment removed for export] *)
Lemma ablocks_free_sec : forall L st X LB (p : aptr) mb ms n st' X',
  (a_live st) !! p = Some (CSec mb ms n) -> awf L st X ->
  a_live st' = delete p (a_live st) -> (forall y, In y (x_busy X) -> In y (x_busy X')) ->
  ablocks L st X LB -> ablocks L st' X' (lb_remove p LB).
Proof.
  intros L st X LB p mb ms n st' X' LIVE WF EL INCL (BH & BF & NDI & NDL). split; [| split; [| split]].
  - intros p' A n' Hin. apply In_lb_remove in Hin. destruct Hin as [Hin NE]. cbn in NE.
    destruct (BH p' A n' Hin) as [(y & Hy & Sy & R)|(mb' & ms' & Lp & R)].
    + left. exists y. split; [apply INCL; exact Hy|]. split; [exact Sy| exact R].
    + right. exists mb', ms'. split; [| exact R]. rewrite EL, lookup_delete_ne; [exact Lp| congruence].
  - intros cls A n' Hin. apply In_lb_remove in Hin. destruct Hin as [Hin _]. exact (BF cls A n' Hin).
  - rewrite hb_ids_lb_remove. apply List.NoDup_filter. exact NDI.
  - apply NoDup_lb_remove. exact NDL.
Qed.

(* [comment removed for export] *)
Lemma freed_block_sec : forall L st X LB (p : aptr) mb ms n A n',
  awf L st X -> ablocks L st X LB -> In (HB p A n') LB -> (a_live st) !! p = Some (CSec mb ms n) ->
  A = mb + SEC_UOFF /\ n' = n /\ sec_wf1 L (CSec mb ms n).
Proof.
  intros L st X LB p mb ms n A n' WF (BH & _) Hin LIVE.
  destruct (BH p A n' Hin) as [(y & Hy & Sy & Uy & Ny)|(mb' & ms' & Lp & EA & G)].
  - exfalso. destruct WF as (_ & _ & _ & _ & _ & _ & _ & BUSY & _). destruct (BUSY y Hy) as [_ M]. rewrite Sy in M.
    destruct M as (_ & _ & _ & _ & _ & M6). rewrite LIVE in M6. discriminate.
  - rewrite LIVE in Lp. injection Lp as <- <- <-. split; [exact EA|]. split; [reflexivity| exact G].
Qed.

(* [comment removed for export] *)
Lemma no_busy_live_sec : forall L st X (p : aptr) mb ms n y,
  awf L st X -> (a_live st) !! p = Some (CSec mb ms n) -> In y (x_busy X) -> xb_st y <> BLive p.
Proof.
  intros L st X p mb ms n y WF LIVE Hy E. destruct WF as (_ & _ & _ & _ & _ & _ & _ & BUSY & _).
  destruct (BUSY y Hy) as [_ M]. rewrite E in M. destruct M as (_ & _ & _ & _ & _ & M6). rewrite LIVE in M6. discriminate.
Qed.

(* [comment removed for export] *)
Lemma arng_sub : forall L RNG st st',
  (forall c, 1 <= c < K_NUM_CLASSES -> get_cls st' c = get_cls st c) -> a_nres st' = a_nres st ->
  (forall ch, In ch (sec_chunks_of st') -> In ch (sec_chunks_of st)) ->
  arng L RNG st -> arng L RNG st'.
Proof.
  intros L RNG st st' EC EN SUB (A1 & A2 & A3 & A4 & A5 & A6 & A6a & A6b & A6c & A7 & A8 & A9 & A10).
  repeat (split; [assumption|]). split.
  { intros c Hc. rewrite (EC c Hc). exact (A7 c Hc). }
  rewrite EN. split; [exact A8|]. split; [| exact A10].
  unfold RSEC in *. rewrite Forall_forall in A9 |- *. intros x Hx. apply A9. apply SUB. exact Hx.
Qed.

(* [comment removed for export] *)
Lemma sec_not_live_after : forall L st cs (p : aptr) mb ms n s,
  asec_wf L st cs -> Permutation cs (sec_chunks_of st) ->
  (a_live st) !! p = Some (CSec mb ms n) -> a_live s = delete p (a_live st) ->
  ~ sec_live s (CSec mb ms n).
Proof.
  intros L st cs p mb ms n s WFS PC LIVE EL [q Hq]. rewrite EL in Hq.
  apply lookup_delete_Some in Hq. destruct Hq as [NE Hq].
  destruct WFS as (_ & _ & _ & _ & _ & _ & [ND _]).
  (* [comment removed for export] *)
  pose proof (map_to_list_delete (a_live st) p (CSec mb ms n) LIVE) as P1.
  assert (Hq' : delete p (a_live st) !! q = Some (CSec mb ms n)) by (rewrite lookup_delete_ne by exact NE; exact Hq).
  pose proof (map_to_list_delete (delete p (a_live st)) q (CSec mb ms n) Hq') as P2.
  assert (P : Permutation ((p, CSec mb ms n) :: (q, CSec mb ms n) :: map_to_list (delete q (delete p (a_live st)))) (map_to_list (a_live st))).
  { eapply Permutation_trans; [apply perm_skip; exact P2| exact P1]. }
  apply (Permutation_map snd) in P. cbn [map snd] in P. apply filter_is_sec_perm in P. cbn [List.filter is_sec] in P.
  assert (P3 : Permutation (CSec mb ms n :: CSec mb ms n :: List.filter is_sec (map snd (map_to_list (delete q (delete p (a_live st)))))
                                 ++ List.filter is_sec (flat_map b_chunks (a_qloc st ++ a_qglob st))) cs).
  { eapply Permutation_trans; [| apply Permutation_sym; exact PC]. unfold sec_chunks_of, achunks. rewrite filter_is_sec_app.
    change (CSec mb ms n :: CSec mb ms n :: List.filter is_sec (map snd (map_to_list (delete q (delete p (a_live st))))) ++ List.filter is_sec (flat_map b_chunks (a_qloc st ++ a_qglob st)))
      with ((CSec mb ms n :: CSec mb ms n :: List.filter is_sec (map snd (map_to_list (delete q (delete p (a_live st)))))) ++ List.filter is_sec (flat_map b_chunks (a_qloc st ++ a_qglob st))).
    apply Permutation_app_tail. exact P. }
  pose proof (Permutation_NoDup (Permutation_sym P3) ND) as ND2. cbn [app] in ND2.
  inversion ND2 as [|x l NI ND3]; subst. apply NI. left. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma sec_live_other : forall st (p : aptr) mb ms n s ch,
  (a_live st) !! p = Some (CSec mb ms n) -> a_live s = delete p (a_live st) -> ch <> CSec mb ms n ->
  (sec_live s ch <-> sec_live st ch).
Proof.
  intros st p mb ms n s ch LIVE EL NE. unfold sec_live. rewrite EL. split; intros [q Hq].
  - apply lookup_delete_Some in Hq. destruct Hq as [_ Hq]. exists q. exact Hq.
  - exists q. rewrite lookup_delete_ne; [exact Hq|]. intros ->. apply NE. pose proof (eq_trans (eq_sym Hq) LIVE) as XX. injection XX as <-. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma sec_wf1_facts' : forall L mb ms n, sec_wf1 L (CSec mb ms n) ->
     mb mod 4096 = 0 /\ ablk mb (mb + ms) /\ mb + ms <= ATOP /\ ms = sec_map_size n /\ 64512 < n <= AREQMAX
  /\ rz_size n = 2048 /\ 73728 <= ms <= 671109120 /\ ms mod 4096 = 0 /\ needed_size n + 4096 <= ms /\ 0 <= needed_size n
  /\ sec_clear L mb ms /\ is_primary n = false /\ n + 6144 <= needed_size n + 4096.
Proof.
  intros L mb ms n W. pose proof W as W0. destruct W0 as (MAL & MLO & MCE & MSE & NB & NPR & SCL).
  pose proof (sec_facts n ltac:(lia) NPR) as (_ & RZ & _ & RS1 & _ & NS & MS & MSB & MSAL & MSR). rewrite <- MSE in MSB, MSAL, MSR.
  unfold AREQMAX in *.
  repeat (lazymatch goal with |- _ /\ _ => split end); first [assumption| reflexivity| lia].
Qed.

(* [comment removed for export] *)
Lemma read_chunk_sec : forall cs L st X m (p : aptr) mb ms n,
  ASECc cs L st X m -> Permutation cs (sec_chunks_of st) -> (a_live st) !! p = Some (CSec mb ms n) ->
  let hm := mb + 6128 in
  exists order i b1 ctx uw,
     Permutation order cs /\ nth_error order i = Some (CSec mb ms n) /\ (i < length order)%nat
  /\ Z.of_nat (length order) = a_nsec st
  /\ Forall (sec_wf1 L) order /\ sec_disjoint order
  /\ u64arr bsegs m (al_ptr_array L) (map (fun ch => Z_to_bv 64 (sec_mb ch)) order)
  /\ junk_at m (al_ptr_array L + 8 * a_nsec st) (8 * (a_nres st - a_nsec st))
  /\ (forall j ch, nth_error order j = Some ch -> exists lv : bool, (lv = true <-> sec_live st ch) /\ asec_chunk m ch (Z.of_nat j) lv)
  /\ asec_chunk m (CSec mb ms n) (Z.of_nat i) true
  /\ rw_cells bsegs m mb [C8 (Z_to_bv 64 mb); C8 (Z_to_bv 64 ms); C8 (Z_to_bv 64 (needed_size n)); C8 (Z_to_bv 64 (Z.of_nat i))]
  /\ rw_cells bsegs m hm [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 ctx)]
  /\ 0 <= b1 < 256 /\ Z.land b1 3 = 1 /\ 0 <= ctx < 2^31
  /\ rw_cells bsegs m (hm + 16) [C8 uw] /\ junk_at m (hm + 24) (ms - SEC_UOFF - 8)
  /\ fill_at m (shad mb) 768 0xfa
  /\ rw_cells bsegs m (shad (hm + 16)) [CB (Z.to_nat (shlen (rup n 8))) (block_shadow_bytes n)]
  /\ fill_at m (shad (hm + 16) + shlen (rup n 8)) (ms / 8 - 768 - shlen (rup n 8)) 0xfa.
Proof.
  intros cs L st X m p mb ms n (WFS & ARR & INST & PZ & SHZ) PC LIVE hm.
  pose proof WFS as (ALO & WP & WR & WL & WB & WF1 & WD).
  destruct ARR as (order & PO & U64 & JK & PER).
  assert (IN : In (CSec mb ms n) cs) by (eapply Permutation_in; [apply Permutation_sym; exact PC| eapply live_sec_in; exact LIVE]).
  assert (INo : In (CSec mb ms n) order) by (eapply Permutation_in; [apply Permutation_sym; exact PO| exact IN]).
  destruct (In_nth_error _ _ INo) as [i NTH].
  assert (IL : (i < length order)%nat) by (apply (proj1 (nth_error_Some order i)); rewrite NTH; discriminate).
  assert (WF1o : Forall (sec_wf1 L) order).
  { rewrite Forall_forall in WF1 |- *. intros c Hc. apply WF1. eapply Permutation_in; [exact PO| exact Hc]. }
  assert (WDo : sec_disjoint order) by (eapply sec_disjoint_perm; [apply Permutation_sym; exact PO| exact WD]).
  destruct (PER i _ NTH) as (lv & LV & CH).
  assert (Elv : lv = true) by (apply (proj2 LV); exists p; exact LIVE). subst lv.
  pose proof (proj1 (Forall_forall _ _) WF1o _ INo) as Wch.
  destruct (sec_wf1_facts' L mb ms n Wch) as (MAL & MLO & MCE & MSE & NB & RZ & MSB & MSAL & NMS & NS0 & SCL & NPR & N6).
  pose proof CH as CH0. cbn [asec_chunk] in CH0.
  destruct CH0 as (H1 & H2 & H3 & H4 & (b1 & cx & H5 & B1 & B3 & CX) & H6 & S1 & S2 & S3).
  unfold SEC_UOFF in H5, H6, S2, S3. replace (mb + 6144 - 16) with hm in H5 by (subst hm; lia).
  destruct (junk_split m _ 8 (ms - 6144 - 8) ltac:(replace (8 + (ms - 6144 - 8)) with (ms - 6144) by lia; exact H6) ltac:(lia) ltac:(lia)) as [U8 UR].
  destruct (c8_of_junk m _ U8) as [uw HUW].
  exists order, i, b1, cx, uw.
  split; [exact PO|]. split; [exact NTH|]. split; [exact IL|]. split; [rewrite (Permutation_length PO); exact WL|].
  split; [exact WF1o|]. split; [exact WDo|]. split; [exact U64|]. split; [exact JK|]. split; [exact PER|]. split; [exact CH|].
  split; [exact H1|]. split; [exact H5|]. split; [exact B1|]. split; [exact B3|]. split; [exact CX|].
  replace (hm + 16) with (mb + 6144) by (subst hm; lia). replace (hm + 24) with (mb + 6144 + 8) by (subst hm; lia).
  split; [exact HUW|]. split; [unfold SEC_UOFF; exact UR|]. split; [exact S1|].
  rewrite <- (granules_rup n) by lia. unfold sec_user_shadow in S2. split; [exact S2| exact S3].
Qed.

(* [comment removed for export] *)
Lemma asec_chunk_frameD' : forall L W m m' mb ms n idx lv,
  munch W m m' -> sec_wf1 L (CSec mb ms n) ->
  (forall A k, mb + 32 <= A -> 0 < k -> A + k <= mb + ms -> disjoint_from W A k) ->
  (forall A k, shad mb <= A -> 0 < k -> A + k <= shad mb + ms / 8 -> disjoint_from W A k) ->
  rw_cells bsegs m' mb [C8 (Z_to_bv 64 mb); C8 (Z_to_bv 64 ms); C8 (Z_to_bv 64 (needed_size n)); C8 (Z_to_bv 64 idx)] ->
  (exists idx0, asec_chunk m (CSec mb ms n) idx0 lv) -> asec_chunk m' (CSec mb ms n) idx lv.
Proof.
  intros L W m m' mb ms n idx lv MU WF1 DC DS HDR [idx0 CH].
  pose proof WF1 as WF0. cbn [sec_wf1] in WF0. destruct WF0 as (G1 & G2 & G3 & G4 & G5 & G6 & _).
  pose proof (sec_facts n ltac:(lia) G6) as (_ & _ & RSE & RSR & _ & NSE & _ & MSR & MSM & _). rewrite <- G4 in MSR, MSM.
  assert (GR : 0 <= granules n /\ shad (mb + SEC_UOFF) = shad mb + 768 /\ 768 + granules n <= ms / 8).
  { unfold granules, SEC_UOFF. rewrite !shad_div, shlen_div. clear -G1 G5 RSR NSE MSR MSM. Z.div_mod_to_equations. lia. }
  destruct GR as (GR1 & GR2 & GR3).
  cbn [asec_chunk] in CH |- *. destruct CH as (H1 & H2 & H3 & H4 & (b1 & ctx & H5 & B1 & B3 & CX) & H6 & S1 & S2 & S3).
  unfold SEC_UOFF in *.
  split; [exact HDR|].
  split; [eapply junk_frameD; [exact H2| exact MU| intros _; apply DC; clear -RSR NSE MSR G4 G5; lia]|].
  split; [eapply cells_frameD; [exact H3| exact MU| cbn; apply DC; clear -RSR NSE MSR G4 G5; lia]|].
  split; [eapply junk_frameD; [exact H4| exact MU| intros _; apply DC; clear -RSR NSE MSR G4 G5; lia]|].
  split. { exists b1, ctx. split; [| split; [exact B1| split; [exact B3| exact CX]]].
           eapply cells_frameD; [exact H5| exact MU| cbn; apply DC; clear -RSR NSE MSR G4 G5; lia]. }
  split; [eapply junk_frameD; [exact H6| exact MU| intros _; apply DC; clear -RSR NSE MSR G4 G5; lia]|].
  split; [eapply fill_frameD; [exact S1| exact MU| intros _; apply DS; clear -GR3 GR1; lia]|].
  assert (GRP : 0 < granules n) by (unfold granules; rewrite shlen_div; clear -G5; Z.div_mod_to_equations; lia).
  split; [eapply cells_frameD; [exact S2| exact MU| cbn; rewrite Nat.add_0_r, Z2Nat.id by exact GR1; rewrite GR2; apply DS; clear -GR3 GR1 GRP; lia]|].
  eapply fill_frameD; [exact S3| exact MU| intros POS; rewrite GR2; apply DS; clear -GR3 GR1 POS; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sec_same0 (st st' : astate) : Prop :=
     a_nsec st' = a_nsec st /\ a_nres st' = a_nres st /\ a_ptr_array st' = a_ptr_array st
  /\ (forall ch, is_sec ch = true -> (sec_live st' ch <-> sec_live st ch)).

Lemma asecc_frame : forall cs L W m m' st st' X X',
  ASECc cs L st X m -> munch W m m' -> wmono bsegs m m' -> sec_untouched L W -> sec_same0 st st' ->
  ASECc cs L st' X' m'.
Proof.
  intros cs L W0 m m' st st' X X' (WFS & ARR & INST & PZ & SHZ) MU0 WM SU0 (EN & ER & EP & EL).
  pose proof WFS as (ALO & WP & WR & WL & WB & WF1 & WD).
  pose proof (munch_filter_nonempty W0 m m' MU0) as MU. pose proof (sec_untouched_filter L W0 SU0) as SU. pose proof (nonempty_filter W0) as NE.
  set (W := List.filter nonempty W0) in MU, SU, NE.
  assert (ALLSEC : forall ch, In ch cs -> exists mb ms n, ch = CSec mb ms n /\ sec_wf1 L (CSec mb ms n)).
  { intros ch Hin. pose proof (proj1 (Forall_forall _ _) WF1 ch Hin) as W1. destruct ch as [c n|mb ms n]; [destruct W1|].
    exists mb, ms, n. split; [reflexivity| exact W1]. }
  split; [| split; [| split; [| split]]].
  - unfold asec_wf. rewrite EP, ER, EN. exact WFS.
  - destruct ARR as (order & PO & U64 & JK & PER). exists order.
    assert (LEN : Z.of_nat (length order) = a_nsec st) by (rewrite (Permutation_length PO); exact WL).
    split; [exact PO|]. split; [| split].
    + destruct order as [|o0 order'].
      * destruct U64 as [[B0 [B1 _]] [V0 [V1 _]]]. split; [split; [exact B0| split; [exact B1| cbn; intros; lia]] | split; [exact V0| split; [exact V1| cbn; intros; lia]]].
      * eapply u64arr_frame; [exact U64| exact MU| exact WM|]. rewrite length_map. apply (D_ptr L W0 SU0 ALO); cbn [length] in LEN |- *; clear -LEN WB WR; lia.
    + rewrite EN, ER. eapply junk_frame; [exact JK| exact MU| exact WM|]. intros POS. apply (D_ptr L W0 SU0 ALO); clear -POS WB WR; lia.
    + intros i ch Hi. destruct (PER i ch Hi) as (lv & LV & CH).
      assert (Hin : In ch cs) by (eapply Permutation_in; [exact PO| eapply nth_error_In; exact Hi]).
      destruct (ALLSEC ch Hin) as (mb & ms & n & -> & W1).
      exists lv. split; [| eapply (asec_chunk_frame L W0 m m' MU0 WM SU0 ALO); [exact W1| exact CH]].
      rewrite LV. apply iff_sym. apply EL. reflexivity.
  - destruct INST as (I1 & [srt I2] & I3 & I4 & I5 & I6). unfold asec_inst. unfold AINSTANCE in *.
    split; [eapply cells_frame; [exact I1| exact MU| exact WM| cbn; apply (D_inst L W0 SU0 ALO); unfold AINSTANCE; lia]|].
    split; [exists srt; eapply cells_frame; [exact I2| exact MU| exact WM| cbn; apply (D_inst L W0 SU0 ALO); unfold AINSTANCE; lia]|].
    split; [eapply junk_frame; [exact I3| exact MU| exact WM| intros _; apply (D_inst L W0 SU0 ALO); unfold AINSTANCE; lia]|].
    split; [eapply junk_frame; [exact I4| exact MU| exact WM| intros _; apply (D_inst L W0 SU0 ALO); unfold AINSTANCE; lia]|].
    split; [eapply cells_frame; [exact I5| exact MU| exact WM| cbn; apply (D_inst L W0 SU0 ALO); unfold AINSTANCE; lia]|].
    eapply junk_frame; [exact I6| exact MU| exact WM| intros _; apply (D_inst L W0 SU0 ALO); unfold AINSTANCE; lia].
  - unfold aprim0 in *. eapply azero_frame; [exact PZ| exact MU| exact WM|]. intros POS.
    apply (su_disjoint L); [exact SU| exact NE| exact POS|]. intros a Ha. apply (clear_prim0 L ALO). exact Ha.
  - intros x Hx HF HC.
    assert (SX : 0 <= shad x < 2^64) by (pose proof atop_range as ATR; rewrite shad_div; unfold ASHOFF, K_HIGH_MEM, AIMG_HI, KLS in *; clear -Hx ATR; Z.div_mod_to_equations; lia).   (* [comment removed for export] *)
    rewrite <- (SHZ x Hx HF HC). apply MU. rewrite wa_unsigned by exact SX.
    eapply (disjoint_outside W (shad x) 1); [| clear; lia].
    apply (su_disjoint L); [exact SU| exact NE| clear; lia|]. intros a Ha K. apply (clear_free_shadow L ALO x Hx HF). replace (shad x) with a by (clear -Ha; lia). exact K.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition depot_frameD_law (AD : alayout -> amem -> Prop) : Prop :=
  forall L m m' W, AD L m -> munch W m m' ->
    Forall (fun iv => forall a, fst iv <= a < snd iv ->
              ~ (0x1a1bc8 <= a < 0x5f1c10) /\ ~ (al_nodes L <= a < al_nodes L + 1048576) /\ ~ (al_store L <= a < al_store L + 8388608)) W ->
    AD L m'.
(* [comment removed for export] *)
Definition fake_frameD_law (AFK : alayout -> list ablock -> amem -> Prop) : Prop :=
  forall L LB m m' W, AFK L LB m -> munch W m m' -> fake_untouched L W ->
    Forall (fun iv => snd iv <= al_t L + 48 \/ al_t L + 64 <= fst iv) W -> AFK L LB m'.

Lemma dc_at_frameD : forall W m m' A n, dc_at m A n -> munch W m m' -> (0 < n -> disjoint_from W A n) -> dc_at m' A n.
Proof. intros W m m' A n H MU D. exact (junk_frameD W m m' A n H MU D). Qed.

Lemma afake_frameD : fake_frameD_law AFAKE.
Proof.
  intros L LB m m' W (G & CE & (h0 & h1 & h2 & hs & HS) & LOG & NGC & DC1 & DC2 & FL & LV) MU UT UT2.
  pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11). unfold FAKESZ in *. pose proof (ablk_lin _ _ G2) as (GL1 & GL2 & GL3 & GL4).   (* [comment removed for export] *)
  assert (DF : disjoint_from W (al_fake L) 11571200) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9); exact X1).
  assert (DS : disjoint_from W (shad (al_fake L)) (shlen 11571200)) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9); exact X2).
  assert (DD : disjoint_from W (al_dtls L) 4096) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9); exact X3).
  assert (D1 : disjoint_from W 0xc90f0 8) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9); exact X4).
  assert (D2 : disjoint_from W 0x602ca8 16) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9); exact X5).
  assert (D3 : disjoint_from W 0x602cb8 8) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9); exact X6).
  assert (D4 : disjoint_from W 0x602cd8 8) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9); exact X7).
  assert (D5 : disjoint_from W 0x1618b1 1) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9); exact X8).
  assert (D6 : disjoint_from W 0x15f798 4) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9); exact X9).
  assert (DT : disjoint_from W (al_t L + 48) 16).
  { apply disjoint_from_Forall. eapply Forall_impl; [| exact UT2]. cbv beta. intros iv Hiv. lia. }
  split; [exact G|].
  split.
  { destruct CE as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8). unfold afake_cells.
    repeat lazymatch goal with |- _ /\ _ => split end;
      try (eapply rw_cells_transportD; [eassumption| exact MU| cbn [cells_size csize Nat.add]; first [assumption | eapply disjoint_from_sub; [exact DD| lia| lia| lia]]]).
    eapply dc_at_frameD; [exact C8| exact MU| intros _; exact DT]. }
  split.
  { exists h0, h1, h2, hs. eapply rw_cells_transportD; [exact HS| exact MU| cbn; eapply disjoint_from_sub; [exact DF| lia| lia| lia]]. }
  split; [eapply rw_cells_transportD; [exact LOG| exact MU| cbn; eapply disjoint_from_sub; [exact DF| lia| lia| lia]]|].
  split; [eapply rw_cells_transportD; [exact NGC| exact MU| cbn; eapply disjoint_from_sub; [exact DF| lia| lia| lia]]|].
  split; [eapply dc_at_frameD; [exact DC1| exact MU| intros _; unfold FAKESZ; eapply disjoint_from_sub; [exact DF| lia| lia| lia]]|].
  split.
  { eapply dc_at_frameD; [exact DC2| exact MU| intros _; unfold FAKESZ; exact DS]. }
  split.
  - intros c pos b Hc Hp Hb NZ. pose proof (fk_flag_range L c pos Hc Hp).
    rewrite (munch_outside_range W m m' (al_fake L) 11571200) in Hb by (assumption || lia). eauto.
  - intros c F n Hin. destruct (LV c F n Hin) as (Hc & Hn & pos & Hp & HF & Hb). split; [exact Hc|]. split; [exact Hn|].
    exists pos. split; [exact Hp|]. split; [exact HF|]. pose proof (fk_flag_range L c pos Hc Hp).
    rewrite (munch_outside_range W m m' (al_fake L) 11571200) by (assumption || lia). exact Hb.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma qcoupled_add1_sec : forall L s s' X X' Q Q' mb ms n k (newb : list xbusy),
  qcoupled L s X Q ->
  length (q_loc Q') = length (a_qloc s') -> length (q_glob Q') = length (a_qglob s') ->
  Permutation (qentries (a_qloc s') (q_loc Q') ++ qentries (a_qglob s') (q_glob Q'))
              ((CSec mb ms n, k) :: qentries (a_qloc s) (q_loc Q) ++ qentries (a_qglob s) (q_glob Q)) ->
  Permutation (map qb_slot (q_loc Q' ++ q_glob Q')) (map xb_slot newb ++ map qb_slot (q_loc Q ++ q_glob Q)) ->
  (forall y, In y (x_busy X') /\ xb_st y = BQuar <-> In y (x_busy X) /\ xb_st y = BQuar) ->
  (forall y, In y (x_busy X') /\ xb_st y = BBatch <-> (In y (x_busy X) /\ xb_st y = BBatch) \/ In y newb) ->
  Forall (fun y => xb_st y = BBatch /\ xb_class y = K_BATCH_CLASS /\ 0 <= xb_slot y) newb ->
  (forall y, In y (x_busy X) -> xb_st y = BBatch -> xb_class y = K_BATCH_CLASS -> In (xb_slot y) (map xb_slot newb) -> False) ->
  List.NoDup (map xb_slot newb) ->
  q_pend Q' = q_pend Q ->
  qcoupled L s' X' Q'.
Proof.
  intros L s s' X X' Q Q' mb ms n k newb (LN1 & LN2 & OK & ND1 & ND2 & BS & PS & NN) L1 L2 PE PB HQ HB NEWB FB NDB PD.
  assert (PEQ : Permutation (qprim_ids (qentries (a_qloc s') (q_loc Q') ++ qentries (a_qglob s') (q_glob Q')))
                             (qprim_ids (qentries (a_qloc s) (q_loc Q) ++ qentries (a_qglob s) (q_glob Q)))).
  { pose proof (qprim_ids_perm _ _ PE) as P. cbn [qprim_ids flat_map fst snd app] in P. exact P. }
  unfold qcoupled. cbv zeta. rewrite PD.
  split; [exact L1|]. split; [exact L2|]. split.
  { eapply Permutation_Forall; [apply Permutation_sym; exact PE|]. constructor; [exact I|].
    eapply Forall_impl; [| exact OK]. intros [ch k'] HOK. unfold qentry_ok in *. cbn [fst snd] in *.
    destruct ch as [c' n'| mb' ms' n']; [| exact I]. destruct HOK as (b1' & ctx' & Hin). exists b1', ctx'.
    apply (proj1 (proj2 (HQ _) (conj Hin eq_refl))). }
  split; [eapply Permutation_NoDup'; [apply Permutation_app_tail; apply Permutation_sym; exact PEQ| exact ND1]|].
  split.
  { eapply Permutation_NoDup'; [apply Permutation_sym; exact PB|]. apply List.NoDup_app; [exact NDB| exact ND2|].
    intros k0 Hn Ho. apply (BS k0) in Ho. destruct Ho as (y & Hy & Sy & Cy & Ky). subst k0. exact (FB y Hy Sy Cy Hn). }
  split.
  { intros k0. split.
    - intros H. apply (Permutation_in _ PB) in H. apply in_app_iff in H. destruct H as [H|H].
      + apply in_map_iff in H. destruct H as (y & <- & Hy). pose proof (proj1 (Forall_forall _ _) NEWB y Hy) as (Sy & Cy & _).
        exists y. split; [apply (proj1 (proj2 (HB y) (or_intror Hy)))|]. auto.
      + apply (BS k0) in H. destruct H as (y & Hy & Sy & Cy & Ky). exists y. split; [apply (proj1 (proj2 (HB y) (or_introl (conj Hy Sy))))|]. auto.
    - intros (y & Hy & Sy & Cy & Ky). eapply Permutation_in; [apply Permutation_sym; exact PB|]. apply in_app_iff.
      destruct (proj1 (HB y) (conj Hy Sy)) as [[Hy0 _]|Hn].
      + right. apply (BS k0). exists y. auto.
      + left. subst k0. apply in_map. exact Hn. }
  split.
  { intros c0 k0. split.
    - intros H. apply (Permutation_in _ (Permutation_app_tail (q_pend Q) PEQ)) in H.
      apply (PS c0 k0) in H. destruct H as (y & Hy & Sy & Cy & Ky). exists y. split; [apply (proj1 (proj2 (HQ y) (conj Hy Sy)))|]. auto.
    - intros (y & Hy & Sy & Cy & Ky). eapply Permutation_in; [apply Permutation_app_tail; apply Permutation_sym; exact PEQ|].
      apply (PS c0 k0). exists y. pose proof (proj1 (HQ y) (conj Hy Sy)) as [Hy0 _]. auto. }
  eapply Permutation_Forall; [apply Permutation_sym; exact PB|]. apply Forall_app. split; [| exact NN].
  apply Forall_forall. intros k0 H. apply in_map_iff in H. destruct H as (y & <- & Hy).
  pose proof (proj1 (Forall_forall _ _) NEWB y Hy) as (_ & _ & P). exact P.
Qed.

Section QUpdatesS.
Variables (L : alayout) (st : astate) (X : aconc) (Q : qconc) (mb ms n : Z).
Let ch := CSec mb ms n.
Hypothesis WF : awf L st X.
Hypothesis CP : qcoupled L st X Q.

(* [comment removed for export] *)
Lemma qcoupled_app_sec : forall s' l bl ql qz ia k,
  a_qloc st = l ++ [bl] -> q_loc Q = ql ++ [qz] ->
  a_qloc s' = l ++ [mkABatch (b_count bl + 1) (b_size bl + n) (ch :: b_chunks bl)] -> a_qglob s' = a_qglob st ->
  qcoupled L s' X (mkQConc (ql ++ [mkQB (qb_slot qz) (k :: qb_ks qz)]) (q_glob Q) ia (q_pend Q)).
Proof.
  intros s' l bl ql qz ia k QL QQ QL' QG'.
  pose proof CP as CP0. destruct CP0 as (LN1 & LN2 & _).
  assert (LNl : length ql = length l).
  { rewrite QL, QQ, !length_app in LN1. cbn in LN1. lia. }
  eapply (qcoupled_add1_sec L st s' X X Q _ mb ms n k []); try exact CP.
  - cbn [q_loc]. rewrite QL', !length_app. cbn. lia.
  - cbn [q_glob]. rewrite QG'. exact LN2.
  - cbn [q_loc q_glob]. rewrite QL', QG', QL, QQ. rewrite !qentries_app by exact LNl. cbn [qentries combine b_chunks qb_ks app].
    rewrite <- !app_assoc. cbn [app]. apply Permutation_sym. rewrite ?app_nil_r.
    apply Permutation_middle.
  - cbn [q_loc q_glob map app]. rewrite QQ, !map_app. cbn [map qb_slot]. apply Permutation_refl.
  - intros y; tauto.
  - intros y. cbn [In]. tauto.
  - constructor.
  - intros y _ _ _ [].
  - constructor.
  - reflexivity.
Qed.

(* [comment removed for export] *)
Lemma qcoupled_new_sec : forall s' k24 cnt sz ia k,
  c_count (get_cls st K_BATCH_CLASS) = cnt -> 0 < cnt ->
  nth_error (xc_cache (x_cls X K_BATCH_CLASS)) (Z.to_nat (cnt - 1)) = Some k24 ->
  a_qloc s' = a_qloc st ++ [mkABatch 1 sz [ch]] -> a_qglob s' = a_qglob st ->
  qcoupled L s' (xbatch X k24) (mkQConc (q_loc Q ++ [mkQB k24 [k]]) (q_glob Q) ia (q_pend Q)).
Proof.
  intros s' k24 cnt sz ia k CNT POS NK QL' QG'.
  pose proof CP as CP0. destruct CP0 as (LN1 & LN2 & _ & _ & _ & BS & _).
  pose proof (k24_not_busy L _ X k24 cnt WF CNT POS NK) as (NB & KR & _).
  eapply (qcoupled_add1_sec L st s' X (xbatch X k24) Q _ mb ms n k [bbatch k24]); try exact CP.
  - cbn [q_loc]. rewrite QL', !length_app. cbn. lia.
  - cbn [q_glob]. rewrite QG'. exact LN2.
  - cbn [q_loc q_glob]. rewrite QL', QG'. rewrite !qentries_app by exact LN1. cbn [qentries combine b_chunks qb_ks app].
    apply Permutation_sym. rewrite <- ?app_assoc. cbn [app]. apply Permutation_middle.
  - cbn [q_loc q_glob map xb_slot bbatch]. rewrite <- app_assoc, !map_app. cbn [map qb_slot app]. apply Permutation_sym.
    apply Permutation_middle.
  - intros y. rewrite (In_xbatch X k24 y). unfold bbatch. split.
    + intros [[-> |H] S]; [cbn in S; discriminate| exact (conj H S)].
    + intros [H S]. split; [right; exact H| exact S].
  - intros y. rewrite (In_xbatch X k24 y). cbn [In]. split.
    + intros [[-> |H] S]; [right; left; reflexivity| left; exact (conj H S)].
    + intros [[H S]|[<-|[]]]; [split; [right; exact H| exact S]| split; [left; reflexivity| reflexivity]].
  - constructor; [| constructor]. cbn. split; [reflexivity|]. split; [reflexivity| lia].
  - intros y Hy Sy Cy Hin. cbn in Hin. destruct Hin as [E|[]]. apply NB.
    unfold busy_slots. rewrite E. apply in_map. apply List.filter_In. split; [exact Hy| rewrite Cy; apply Z.eqb_refl].
  - constructor; [intros []| constructor].
  - reflexivity.
Qed.
End QUpdatesS.
End CANSEC1.
(* [comment removed for export] *)
