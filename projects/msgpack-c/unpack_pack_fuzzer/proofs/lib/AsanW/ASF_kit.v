(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require PropExec MState Mem Cells Step Frame Arr ITree Nodes Decode.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require ExecF ITreeA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AImg AProto ABase ABytes ARep ARepFrame ALayout AHeapP ASecFacts ASec ASecFrame AKitQ ARepQ ARepQP ARepKit ARepExt AFreeModel AFreeRep AFrameD FsKit AFake_iface.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AExh AC6Frame.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require RunDraw.
Module ASF_kit.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ITreeA.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABytes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARep. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepFrame. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ALayout. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AHeapP. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ASecFacts. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ASec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ASecFrame. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKitQ. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepQ. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepQP. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepKit. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepExt. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFreeModel. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFreeRep. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFrameD. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.FsKit. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_iface.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AExh. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AC6Frame.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT} {ov : annOV} {gb : GcBit}.
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

Lemma live_in_achunks : forall st (p : aptr) ch, (a_live st) !! p = Some ch -> In ch (achunks st).
Proof.
  intros st p ch L. unfold achunks. apply in_or_app. left.
  pose proof (map_to_list_delete (a_live st) p ch L) as P.
  apply (Permutation_map snd) in P. cbn [map snd] in P. eapply Permutation_in; [exact P| left; reflexivity].
Qed.
Lemma live_sec_in : forall st (p : aptr) mb ms n, (a_live st) !! p = Some (CSec mb ms n) -> In (CSec mb ms n) (sec_chunks_of st).
Proof. intros st p mb ms n L. unfold sec_chunks_of. apply List.filter_In. split; [eapply live_in_achunks; exact L| reflexivity]. Qed.

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

Lemma sec_chunks_of_quar_sec : forall s s' mb ms n,
  a_live s' = a_live s ->
  Permutation (qfilt is_sec s') (CSec mb ms n :: qfilt is_sec s) ->
  Permutation (sec_chunks_of s') (CSec mb ms n :: sec_chunks_of s).
Proof.
  intros s s' mb ms n EL PQ. unfold sec_chunks_of, achunks. rewrite EL, !filter_is_sec_app. unfold qfilt in PQ.
  eapply Permutation_trans; [apply Permutation_app_head; exact PQ|]. apply Permutation_sym. apply Permutation_middle.
Qed.

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

Lemma no_busy_live_sec : forall L st X (p : aptr) mb ms n y,
  awf L st X -> (a_live st) !! p = Some (CSec mb ms n) -> In y (x_busy X) -> xb_st y <> BLive p.
Proof.
  intros L st X p mb ms n y WF LIVE Hy E. destruct WF as (_ & _ & _ & _ & _ & _ & _ & BUSY & _).
  destruct (BUSY y Hy) as [_ M]. rewrite E in M. destruct M as (_ & _ & _ & _ & _ & M6). rewrite LIVE in M6. discriminate.
Qed.

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

Lemma sec_not_live_after : forall L st cs (p : aptr) mb ms n s,
  asec_wf L st cs -> Permutation cs (sec_chunks_of st) ->
  (a_live st) !! p = Some (CSec mb ms n) -> a_live s = delete p (a_live st) ->
  ~ sec_live s (CSec mb ms n).
Proof.
  intros L st cs p mb ms n s WFS PC LIVE EL [q Hq]. rewrite EL in Hq.
  apply lookup_delete_Some in Hq. destruct Hq as [NE Hq].
  destruct WFS as (_ & _ & _ & _ & _ & _ & [ND _]).

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

Lemma sec_live_other : forall st (p : aptr) mb ms n s ch,
  (a_live st) !! p = Some (CSec mb ms n) -> a_live s = delete p (a_live st) -> ch <> CSec mb ms n ->
  (sec_live s ch <-> sec_live st ch).
Proof.
  intros st p mb ms n s ch LIVE EL NE. unfold sec_live. rewrite EL. split; intros [q Hq].
  - apply lookup_delete_Some in Hq. destruct Hq as [_ Hq]. exists q. exact Hq.
  - exists q. rewrite lookup_delete_ne; [exact Hq|]. intros ->. apply NE. pose proof (eq_trans (eq_sym Hq) LIVE) as XX. injection XX as <-. reflexivity.
Qed.

Lemma sec_wf1_facts' : forall L mb ms n, sec_wf1 L (CSec mb ms n) ->
     mb mod 4096 = 0 /\ ablk mb (mb + ms) /\ mb + ms <= ATOP /\ ms = sec_map_size n /\ 64512 < n <= AREQMAX
  /\ rz_size n = 2048 /\ 73728 <= ms <= 4293926912 /\ ms mod 4096 = 0 /\ needed_size n + 4096 <= ms /\ 0 <= needed_size n
  /\ sec_clear L mb ms /\ is_primary n = false /\ n + 6144 <= needed_size n + 4096.
Proof.
  intros L mb ms n W. pose proof W as W0. destruct W0 as (MAL & MLO & MCE & MSE & NB & NPR & SCL).
  pose proof (sec_facts n ltac:(lia) NPR) as (_ & RZ & _ & RS1 & _ & NS & MS & MSB & MSAL & MSR). rewrite <- MSE in MSB, MSAL, MSR.
  unfold AREQMAX in *.
  repeat (lazymatch goal with |- _ /\ _ => split end); first [assumption| reflexivity| lia].
Qed.

Lemma read_chunk_sec : forall cs L st X m (p : aptr) mb ms n,
  ASECc cs L st X m -> Permutation cs (sec_chunks_of st) -> (a_live st) !! p = Some (CSec mb ms n) ->
  let hm := mb + 6128 in
  exists order i b1 ctx uw,
     Permutation order cs /\ nth_error order i = Some (CSec mb ms n) /\ (i < length order)%nat
  /\ Z.of_nat (length order) = a_nsec st
  /\ Forall (sec_wf1 L) order /\ sec_disjoint order
  /\ u64arr asegs m (al_ptr_array L) (map (fun ch => Z_to_bv 64 (sec_mb ch)) order)
  /\ junk_at m (al_ptr_array L + 8 * a_nsec st) (8 * (a_nres st - a_nsec st))
  /\ (forall j ch, nth_error order j = Some ch -> exists lv : bool, (lv = true <-> sec_live st ch) /\ asec_chunk m ch (Z.of_nat j) lv)
  /\ asec_chunk m (CSec mb ms n) (Z.of_nat i) true
  /\ rw_cells asegs m mb [C8 (Z_to_bv 64 mb); C8 (Z_to_bv 64 ms); C8 (Z_to_bv 64 (needed_size n)); C8 (Z_to_bv 64 (Z.of_nat i))]
  /\ rw_cells asegs m hm [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 ctx)]
  /\ 0 <= b1 < 256 /\ Z.land b1 3 = 1 /\ 0 <= ctx < 2^31
  /\ rw_cells asegs m (hm + 16) [C8 uw] /\ junk_at m (hm + 24) (ms - SEC_UOFF - 8)
  /\ fill_at m (shad mb) 768 0xfa
  /\ rw_cells asegs m (shad (hm + 16)) [CB (Z.to_nat (shlen (rup n 8))) (block_shadow_bytes n)]
  /\ fill_at m (shad (hm + 16) + shlen (rup n 8)) (ms / 8 - 768 - shlen (rup n 8)) 0xfa.
Proof.
  intros cs L st X m p mb ms n (WFS & ARR & INST & PZ & SHZ & AXH) PC LIVE hm.
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

Lemma asec_chunk_frameD' : forall L W m m' mb ms n idx lv,
  munch W m m' -> sec_wf1 L (CSec mb ms n) ->
  (forall A k, mb + 32 <= A -> 0 < k -> A + k <= mb + ms -> disjoint_from W A k) ->
  (forall A k, shad mb <= A -> 0 < k -> A + k <= shad mb + ms / 8 -> disjoint_from W A k) ->
  rw_cells asegs m' mb [C8 (Z_to_bv 64 mb); C8 (Z_to_bv 64 ms); C8 (Z_to_bv 64 (needed_size n)); C8 (Z_to_bv 64 idx)] ->
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

Definition sec_same0 (st st' : astate) : Prop :=
     a_nsec st' = a_nsec st /\ a_nres st' = a_nres st /\ a_ptr_array st' = a_ptr_array st
  /\ (forall ch, is_sec ch = true -> (sec_live st' ch <-> sec_live st ch))
  /\ a_emb st' = a_emb st /\ a_exh st' = a_exh st.

Lemma asecc_frame : forall cs L W m m' st st' X X',
  ASECc cs L st X m -> munch W m m' -> wmono asegs m m' -> sec_untouched L W -> c6_untouched L W -> sec_same0 st st' ->
  ASECc cs L st' X' m'.
Proof.
  intros cs L W0 m m' st st' X X' (WFS & ARR & INST & PZ & SHZ & AXH) MU0 WM SU0 C60 (EN & ER & EP & EL & EEMB & EEXH).
  pose proof WFS as (ALO & WP & WR & WL & WB & WF1 & WD).
  pose proof (munch_filter_nonempty W0 m m' MU0) as MU. pose proof (sec_untouched_filter L W0 SU0) as SU. pose proof (nonempty_filter W0) as NE.
  set (W := List.filter nonempty W0) in MU, SU, NE.
  assert (ALLSEC : forall ch, In ch cs -> exists mb ms n, ch = CSec mb ms n /\ sec_wf1 L (CSec mb ms n)).
  { intros ch Hin. pose proof (proj1 (Forall_forall _ _) WF1 ch Hin) as W1. destruct ch as [c n|mb ms n]; [destruct W1|].
    exists mb, ms, n. split; [reflexivity| exact W1]. }
  split; [| split; [| split; [| split; [| split]]]].
  6: exact (aexh_frame cs L st st' m m' W0 AXH MU0 SU0 C60 EEMB EEXH).
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
    assert (SX : 0 <= shad x < 2^64) by (pose proof atop_range as ATR; rewrite shad_div; unfold ASHOFF, K_HIGH_MEM, AIMG_HI, KLS in *; clear -Hx ATR; Z.div_mod_to_equations; lia).
    rewrite <- (SHZ x Hx HF HC). apply MU. rewrite wa_unsigned by exact SX.
    eapply (disjoint_outside W (shad x) 1); [| clear; lia].
    apply (su_disjoint L); [exact SU| exact NE| clear; lia|]. intros a Ha K. apply (clear_free_shadow L ALO x Hx HF). replace (shad x) with a by (clear -Ha; lia). exact K.
Qed.

Definition depot_frameD_law (AD : alayout -> amem -> Prop) : Prop :=
  forall L m m' W, AD L m -> munch W m m' ->
    Forall (fun iv => forall a, fst iv <= a < snd iv ->
              ~ (0x1ab988 <= a < 0x5fb9d0) /\ ~ (al_nodes L <= a < al_nodes L + 1048576) /\ ~ (al_store L <= a < al_store L + 8388608)) W ->
    AD L m'.

Definition fake_frameD_law (AFK : alayout -> list ablock -> amem -> Prop) : Prop :=
  forall L LB m m' W, AFK L LB m -> munch W m m' -> disjoint_from W (al_t L + 72) 8 -> fake_untouched L W ->
    Forall (fun iv => snd iv <= al_t L + 48 \/ al_t L + 64 <= fst iv) W -> AFK L LB m'.

Lemma dc_at_frameD : forall W m m' A n, dc_at m A n -> munch W m m' -> (0 < n -> disjoint_from W A n) -> dc_at m' A n.
Proof. intros W m m' A n H MU D. exact (junk_frameD W m m' A n H MU D). Qed.

Lemma afake_frameD : fake_frameD_law AFAKE.
Proof.
  intros L LB m m' W (G & CE & (h0 & h1 & h2 & hs & HS) & LOG & NGC & DC1 & DC2 & FL & LV & TFSC) MU D7 UT UT2.
  pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11). unfold FAKESZ in *. pose proof (ablk_lin _ _ G2) as (GL1 & GL2 & GL3 & GL4).
  assert (DF : disjoint_from W (al_fake L) 11571200) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9); exact X1).
  assert (DS : disjoint_from W (shad (al_fake L)) (shlen 11571200)) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9); exact X2).
  assert (DD : disjoint_from W (al_dtls L) 4096) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9); exact X3).
  assert (D1 : disjoint_from W 0xd3358 8) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9); exact X4).
  assert (D2 : disjoint_from W 0x60cc78 16) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9); exact X5).
  assert (D3 : disjoint_from W 0x60cc88 8) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9); exact X6).
  assert (D4 : disjoint_from W 0x60cca8 8) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9); exact X7).
  assert (D5 : disjoint_from W 0x16b671 1) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9); exact X8).
  assert (D6 : disjoint_from W 0x169558 4) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9); exact X9).
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
  - split; [| eapply rw_cells_transportD; [exact TFSC| exact MU| cbn [cells_size csize Nat.add]; exact D7]].
    intros c F n Hin. destruct (LV c F n Hin) as (Hc & Hn & pos & Hp & HF & Hb). split; [exact Hc|]. split; [exact Hn|].
    exists pos. split; [exact Hp|]. split; [exact HF|]. pose proof (fk_flag_range L c pos Hc Hp).
    rewrite (munch_outside_range W m m' (al_fake L) 11571200) by (assumption || lia). exact Hb.
Qed.

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

End ASF_kit.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AMalloc_iface ADepot_iface ASecModel AModelFacts APrimFacts F_amalloc_arep.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AC6U.
Module ASecStore.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ITreeA.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABytes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARep. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepKit. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepFrame. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ALayout. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AHeapP. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKitQ. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AMalloc_iface. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ADepot_iface. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ASec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ASecFacts. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ASecFrame. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ASecModel. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AModelFacts. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.APrimFacts. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_amalloc_arep. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepExt.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AExh. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AC6U. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AC6Frame.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT} {ov : annOV}.
Lemma sec_chunk_in_ranges : forall st mb ms n, In (CSec mb ms n) (sec_chunks_of st) -> In (mb, mb + ms) (asec_ranges st).
Proof.
  intros st mb ms n H. unfold sec_chunks_of in H. apply List.filter_In in H. destruct H as [H _].
  unfold asec_ranges. apply in_or_app. left. apply in_flat_map. exists (CSec mb ms n). split; [exact H| left; reflexivity].
Qed.

Lemma avoids_all_In : forall a n l iv, avoids_all a n l = true -> In iv l -> a + n <= fst iv \/ snd iv <= a.
Proof.
  intros a n l iv H Hin. unfold avoids_all in H. rewrite forallb_forall in H. specialize (H iv Hin).
  unfold iv_clear in H. apply orb_prop in H. destruct H as [H|H]; apply Z.leb_le in H; lia.
Qed.

Lemma asec_wf_all : forall L st cs ch, asec_wf L st cs -> In ch cs -> exists mb ms n, ch = CSec mb ms n /\ sec_wf1 L (CSec mb ms n).
Proof.
  intros L st cs ch (_ & _ & _ & _ & _ & WF1 & _) Hin. pose proof (proj1 (Forall_forall _ _) WF1 ch Hin) as W1.
  destruct ch as [c n|mb ms n]; [destruct W1|]. exists mb, ms, n. split; [reflexivity| exact W1].
Qed.

Section Valid.
Variables (L : alayout) (RESV : list (Z * Z)) (st : astate) (n a : Z).
Let ms := sec_map_size n.
Hypothesis ALO : alayout_ok L.
Hypothesis N : 1 <= n <= AREQMAX.
Hypothesis PRIM : is_primary n = false.
Hypothesis FR : sfresh RESV st n a = true.
Hypothesis ROK : aresv_ok L RESV.

Lemma valid_geo : a mod 4096 = 0 /\ ablk a (a + ms) /\ a + ms <= ATOP /\ 0 < ms /\ ms = sec_map_size n.
Proof.
  destruct (sfresh_true_facts RESV st n a FR) as (_ & _ & AV & _ & POS & AL & TOPB & _).
  pose proof (sec_facts n N PRIM) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & MSB).
  destruct ROK as (R1 & R2 & _).
  pose proof (pcov_clear _ _ _ _ _ R1 AV ltac:(unfold AIMG_HI; clear; lia) ltac:(clear -MSB; lia)) as C1.
  pose proof (pcov_clear _ _ _ _ _ R2 AV ltac:(clear; lia) ltac:(clear -MSB; lia)) as C2.
  subst ms. split; [exact AL|]. split; [| split; [exact TOPB| split; [clear -MSB; lia| reflexivity]]].
  unfold ablk, KLS. unfold AIMG_HI in *. clear -C1 C2 POS TOPB MSB. lia.
Qed.

Lemma valid_hulls : Forall (fun iv => a + ms <= fst iv \/ snd iv <= a) (astartup_hulls L).
Proof.
  destruct (sfresh_true_facts RESV st n a FR) as (_ & _ & AV & _ & _ & _ & _ & _).
  pose proof valid_geo as (_ & _ & _ & MSP & _).
  destruct ROK as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15).
  unfold astartup_hulls. fold (al_res L) in R3. change (4096 * al_V L 323%nat) with (al_dtls L) in R10.
  repeat (apply Forall_cons; [cbn [fst snd]; eapply pcov_clear; [eassumption| exact AV| clear; lia| exact MSP] |]). apply Forall_nil.
Qed.

Lemma valid_clear : sec_clear L a ms.
Proof.
  pose proof valid_hulls as H. unfold astartup_hulls in H.
  repeat lazymatch type of H with Forall _ (_ :: _) => apply Forall_cons_iff in H; destruct H as [? H] | _ => idtac end.
  cbn [fst snd] in *. unfold sec_clear. repeat split; lia.
Qed.

Lemma valid_chunks : Forall (fun ch => a + ms <= sec_mb ch \/ sec_mb ch + sec_ms ch <= a) (sec_chunks_of st).
Proof.
  destruct (sfresh_true_facts RESV st n a FR) as (_ & _ & _ & AV & _ & _ & _ & _).
  apply Forall_forall. intros ch Hin. destruct ch as [c k|mb ms' k]; cbn [sec_mb sec_ms].
  - pose proof valid_geo as (_ & G & _). pose proof (ablk_lin _ _ G) as (_ & G0 & _). right. clear -G0. lia.
  - pose proof (avoids_all_In _ _ _ _ AV (sec_chunk_in_ranges st mb ms' k Hin)) as D. cbn [fst snd] in D. exact D.
Qed.

Lemma valid_buf : let '(d, cap, _) := a_emb st in cap = 0 \/ avoids_all d cap (sec_iv (CSec a ms n)) = true.
Proof.
  destruct (sfresh_true_facts RESV st n a FR) as (_ & _ & _ & AV & _ & _ & _ & _). fold ms in AV.
  destruct (a_emb st) as [[d cap] sz] eqn:EA. destruct (Z.eqb_spec cap 0) as [E0|NZ]; [left; exact E0| right].
  assert (Hin : In (d, d + cap) (asec_ranges st)).
  { unfold asec_ranges. apply in_or_app. right. unfold emb_iv. rewrite EA. destruct (Z.eqb_spec cap 0) as [E0|_]; [exact (False_ind _ (NZ E0))| left; reflexivity]. }
  pose proof (avoids_all_In _ _ _ _ AV Hin) as D. cbn [fst snd] in D.
  cbn [sec_iv]. unfold avoids_all. cbn [forallb]. unfold iv_clear. cbn [fst snd]. rewrite andb_true_r. apply orb_true_iff.
  destruct D as [D|D]; [right; apply Z.leb_le; lia| left; apply Z.leb_le; lia].
Qed.

Lemma valid_wf1 : sec_wf1 L (CSec a ms n).
Proof.
  pose proof valid_geo as (G1 & G2 & G3 & G4 & G5). pose proof (sec_facts n N PRIM) as (NB & _).
  cbn [sec_wf1]. split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. split; [exact G5|].
  split; [lia|]. split; [exact PRIM| exact valid_clear].
Qed.
End Valid.

Lemma wview_some : forall m (x : word) b, m x = Some b -> wview asegs m x = Some b.
Proof. intros m x b H. unfold wview. rewrite H. reflexivity. Qed.

Lemma ashz_azero : forall L cs m a ms,
  ashz L cs m ->
  a mod 8 = 0 -> ablk a (a + ms) -> a + ms <= ATOP -> 0 <= ms ->
  Forall (fun iv => a + ms <= fst iv \/ snd iv <= a) (astartup_hulls L) ->
  Forall (fun ch => a + ms <= sec_mb ch \/ sec_mb ch + sec_ms ch <= a) cs ->
  azero m (shad a) (ms / 8).
Proof.
  intros L cs m a ms SHZ A8 ALO AHI MS0 HH HC.
  assert (PT : forall i, 0 <= i < ms / 8 -> m (wa (shad a + i)) = Some (Z_to_bv 8 0)).
  { intros i Hi. replace (shad a + i) with (shad (a + 8 * i)) by (rewrite !shad_div; clear -A8; Z.div_mod_to_equations; lia).
    apply SHZ.
    - unfold ablk, KLS, K_HIGH_MEM in *. unfold AIMG_HI in *. clear -Hi ALO AHI A8. Z.div_mod_to_equations. lia.
    - eapply Forall_impl; [| exact HH]. cbn beta. intros iv Hiv. clear -Hi Hiv A8. Z.div_mod_to_equations. lia.
    - eapply Forall_impl; [| exact HC]. cbn beta. intros ch Hch. clear -Hi Hch A8. Z.div_mod_to_equations. lia. }
  assert (SR : 0 <= shad a /\ shad a + ms / 8 <= 2^64).
  { pose proof (ablk_lin _ _ ALO) as (AL1 & AL2 & AL3 & AL4). rewrite shad_div. unfold ASHOFF in *. clear -AL2 AL4 AHI MS0. Z.div_mod_to_equations. lia. }
  split; [exact PT|]. split; [lia|]. split; [lia|]. intros i Hi. rewrite (wview_some _ _ _ (PT i Hi)). discriminate.
Qed.

Lemma filter_is_sec_perm : forall (l l' : list achunk), Permutation l l' -> Permutation (List.filter is_sec l) (List.filter is_sec l').
Proof.
  intros l l' HP. induction HP; cbn; [constructor| | |].
  - destruct (is_sec x); [apply perm_skip|]; assumption.
  - destruct (is_sec x), (is_sec y); try apply perm_swap; try apply perm_skip; try apply Permutation_refl.
  - eapply Permutation_trans; eassumption.
Qed.

Lemma sec_chunks_of_insert_sec : forall st st' p mb ms n,
  (a_live st) !! p = None ->
  a_live st' = <[p := CSec mb ms n]> (a_live st) -> a_qloc st' = a_qloc st -> a_qglob st' = a_qglob st ->
  Permutation (sec_chunks_of st') (CSec mb ms n :: sec_chunks_of st).
Proof.
  intros st st' p mb ms n NONE E1 E2 E3. unfold sec_chunks_of, achunks. rewrite E1, E2, E3, !filter_is_sec_app.
  change (CSec mb ms n :: List.filter is_sec (map snd (map_to_list (a_live st))) ++ List.filter is_sec (flat_map b_chunks (a_qloc st ++ a_qglob st)))
    with ((CSec mb ms n :: List.filter is_sec (map snd (map_to_list (a_live st)))) ++ List.filter is_sec (flat_map b_chunks (a_qloc st ++ a_qglob st))).
  apply Permutation_app_tail.
  pose proof (map_to_list_insert (a_live st) p (CSec mb ms n) NONE) as P.
  apply (Permutation_map snd) in P. cbn [map snd] in P.
  eapply Permutation_trans; [apply filter_is_sec_perm; exact P|]. cbn. apply Permutation_refl.
Qed.

Lemma awf_fresh_none : forall L st X, awf L st X -> (a_live st) !! (a_next st) = None.
Proof.
  intros L st X WF. destruct WF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & FRESH & _).
  destruct ((a_live st) !! (a_next st)) as [ch|] eqn:E; [| reflexivity]. exfalso. pose proof (FRESH _ _ E) as F. clear -F. lia.
Qed.

Lemma awf_sec : forall L st X nres' a ms n, awf L st X -> awf L (st_sec st nres' a ms n) X.
Proof.
  intros L st X nres' a ms n WF.
  pose proof (awf_fresh_none L st X WF) as NONE.
  pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVE & FRESH & UNIQ).
  pose proof (st_sec_fields st nres' a ms n) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12).
  unfold awf. rewrite E1, E2, E7, E8.
  split; [exact SBE|]. split; [exact PAE|]. split; [exact SAL|]. split; [exact SLO|]. split; [exact SHI|].
  split. { intros c Hc. rewrite get_cls_st_sec, max_count_st_sec. unfold ndist. rewrite get_cls_st_sec. exact (PERC c Hc). }
  split. { intros c Hc. rewrite get_cls_st_sec. exact (OUTC c Hc). }
  split. { intros b Hb. destruct (BUSY b Hb) as [CLB M]. split; [exact CLB|]. destruct (xb_st b) as [p| |]; try exact M.
           destruct M as (M1 & M2 & M3 & M4 & M5 & M6). repeat (split; [assumption|]).
           rewrite lookup_insert_ne; [exact M6|]. intros E. assert (X0 : a_live st !! p = None) by (rewrite <- E; exact NONE). rewrite X0 in M6. discriminate. }
  split. { intros p c k Hp. destruct (N.eq_dec p (a_next st)) as [->|NE].
           - rewrite lookup_insert_eq in Hp. discriminate.
           - rewrite lookup_insert_ne in Hp by (intros E; apply NE; symmetry; exact E). exact (LIVE p c k Hp). }
  split. { intros p ch Hp. destruct (N.eq_dec p (a_next st)) as [->|NE]; [lia|].
           rewrite lookup_insert_ne in Hp by (intros E; apply NE; symmetry; exact E). pose proof (FRESH p ch Hp). lia. }
  exact UNIQ.
Qed.

Lemma ablocks_sec : forall L st X LB nres' a ms n,
  awf L st X -> ablocks L st X LB -> sec_wf1 L (CSec a ms n) ->
  ablocks L (st_sec st nres' a ms n) X (HB (a_next st) (a + SEC_UOFF) n :: LB).
Proof.
  intros L st X LB nres' a ms n WF (BH & BF & NDI & NDL) W1.
  pose proof (awf_fresh_none L st X WF) as NONE.
  destruct WF as (_ & _ & _ & _ & _ & _ & _ & BUSY & _ & FRESH & _).
  pose proof (st_sec_fields st nres' a ms n) as (_ & _ & _ & _ & _ & _ & E7 & _).
  assert (OLD : forall p A n', In (HB p A n') LB -> (p < a_next st)%N).
  { intros p A n' Hin. destruct (BH p A n' Hin) as [(b & Hb & Sb & _)|(mb & ms' & Lp & _)].
    - destruct (BUSY b Hb) as [_ M]. rewrite Sb in M. destruct M as (_ & _ & _ & _ & _ & M5). exact (FRESH _ _ M5).
    - exact (FRESH _ _ Lp). }
  split; [| split; [| split]].
  - intros p A n' [E|Hin].
    + injection E as <- <- <-. right. exists a, ms. rewrite E7, lookup_insert_eq. split; [reflexivity|]. split; [reflexivity| exact W1].
    + destruct (BH p A n' Hin) as [(b & Hb & R)|(mb & ms' & Lp & R)].
      * left. exists b. split; [exact Hb| exact R].
      * right. exists mb, ms'. split; [| exact R]. rewrite E7, lookup_insert_ne; [exact Lp|].
        intros E. pose proof (OLD _ _ _ Hin) as F. rewrite E in F. clear -F. lia.
  - intros cls A n' [E|Hin]; [discriminate| exact (BF cls A n' Hin)].
  - cbn. constructor; [| exact NDI]. intros Hin. unfold hb_ids in Hin. apply in_flat_map in Hin. destruct Hin as (b & Hb & Hp).
    destruct b as [[p|cls] A n']; cbn in Hp; [| destruct Hp]. destruct Hp as [E|[]]. subst p. pose proof (OLD _ _ _ Hb) as F. clear -F. lia.
  - constructor; [| exact NDL]. intros Hin. pose proof (OLD _ _ _ Hin) as F. clear -F. lia.
Qed.

Lemma arng_sec : forall L RNG RNG' st X nres' a ms n,
  awf L st X -> arng L RNG st -> fp_le RNG RNG' ->
  rng RNG' a ms -> rng RNG' (shad a) (ms / 8) -> rng RNG' (al_ptr_array L) (8 * nres') ->
  arng L RNG' (st_sec st nres' a ms n).
Proof.
  intros L RNG RNG' st X nres' a ms n WF AR LE R1 R2 R3.
  pose proof (arng_mono L RNG RNG' st LE AR) as (A1 & A2 & A3 & A4 & A5 & A6 & A6a & A6b & A6c & A7 & A8 & A9 & A10).
  pose proof (st_sec_fields st nres' a ms n) as (_ & _ & E3 & _ & _ & _ & E7 & _ & E9 & _ & E11 & _).
  unfold arng. rewrite E3. repeat (split; [assumption|]). split; [| exact A10].
  eapply RSEC_perm; [apply Permutation_sym; eapply sec_chunks_of_insert_sec; [eapply awf_fresh_none; exact WF| exact E7| exact E9| exact E11]|].
  constructor; [| exact A9]. cbn [sec_mb sec_ms]. split; [exact R1| exact R2].
Qed.

Lemma ASECc_perm : forall cs cs' L st X m, Permutation cs cs' -> ASECc cs L st X m -> ASECc cs' L st X m.
Proof.
  intros cs cs' L st X m P (WFS & ARR & INST & PZ & SHZ & AXH).
  split; [| split; [| split; [exact INST| split; [exact PZ| split]]]].
  4: { eapply AEXHc_sub; [| exact AXH]. intros ch Hch. eapply Permutation_in; [apply Permutation_sym; exact P| exact Hch]. }
  - destruct WFS as (ALO & WP & WR & WL & WB & WF1 & WD). unfold asec_wf.
    split; [exact ALO|]. split; [exact WP|]. split; [exact WR|]. split; [rewrite <- (Permutation_length P); exact WL|]. split; [exact WB|].
    split; [| eapply sec_disjoint_perm; [exact P| exact WD]].
    rewrite Forall_forall in WF1 |- *. intros ch Hin. apply WF1. eapply Permutation_in; [apply Permutation_sym; exact P| exact Hin].
  - destruct ARR as (order & PO & U64 & JK & PER). exists order. split; [eapply Permutation_trans; [exact PO| exact P]|].
    split; [exact U64| split; [exact JK| exact PER]].
  - intros x Hx HF HC. apply (SHZ x Hx HF). rewrite Forall_forall in HC |- *. intros ch Hin. apply HC.
    eapply Permutation_in; [exact P| exact Hin].
Qed.

Lemma asec_chunk_frameW : forall L W m m' mb ms n idx lv,
  munch W m m' -> wmono asegs m m' ->
  sec_wf1 L (CSec mb ms n) ->
  (forall A k, mb <= A -> A + k <= mb + ms -> 0 < k -> disjoint_from W A k) ->
  (forall A k, shad mb <= A -> A + k <= shad mb + ms / 8 -> 0 < k -> disjoint_from W A k) ->
  asec_chunk m (CSec mb ms n) idx lv -> asec_chunk m' (CSec mb ms n) idx lv.
Proof.
  intros L W m m' mb ms n idx lv MU WM WF1 DC DS CH.
  pose proof WF1 as WF0. cbn [sec_wf1] in WF0. destruct WF0 as (G1 & G2 & G3 & G4 & G5 & G6 & _).
  pose proof (sec_facts n ltac:(lia) G6) as (_ & _ & RSE & RSR & _ & NSE & _ & MSR & MSM & _). rewrite <- G4 in MSR, MSM.
  assert (GR : 0 <= granules n /\ shad (mb + SEC_UOFF) = shad mb + 768 /\ 768 + granules n <= ms / 8).
  { unfold granules, SEC_UOFF. rewrite !shad_div, shlen_div. clear -G1 G5 RSR NSE MSR MSM. Z.div_mod_to_equations. lia. }
  destruct GR as (GR1 & GR2 & GR3).
  cbn [asec_chunk] in CH |- *. destruct CH as (H1 & H2 & H3 & H4 & (b1 & ctx & H5 & B1 & B3 & CX) & H6 & S1 & S2 & S3).
  unfold SEC_UOFF in *.
  split; [eapply cells_frame; [exact H1| exact MU| exact WM| cbn; apply DC; clear -RSR NSE MSR G4 G5; lia]|].
  split; [eapply junk_frame; [exact H2| exact MU| exact WM| intros _; apply DC; clear -RSR NSE MSR G4 G5; lia]|].
  split; [eapply cells_frame; [exact H3| exact MU| exact WM| cbn; apply DC; clear -RSR NSE MSR G4 G5; lia]|].
  split; [eapply junk_frame; [exact H4| exact MU| exact WM| intros _; apply DC; clear -RSR NSE MSR G4 G5; lia]|].
  split. { exists b1, ctx. split; [| split; [exact B1| split; [exact B3| exact CX]]].
           eapply cells_frame; [exact H5| exact MU| exact WM| cbn; apply DC; clear -RSR NSE MSR G4 G5; lia]. }
  split; [eapply junk_frame; [exact H6| exact MU| exact WM| intros _; apply DC; clear -RSR NSE MSR G4 G5; lia]|].
  split; [eapply fill_frame; [exact S1| exact MU| exact WM| intros _; apply DS; clear -GR3 GR1; lia]|].
  assert (GRP : 0 < granules n) by (unfold granules; rewrite shlen_div; clear -G5; Z.div_mod_to_equations; lia).
  split; [eapply cells_frame; [exact S2| exact MU| exact WM| cbn; rewrite Nat.add_0_r, Z2Nat.id by exact GR1; rewrite GR2; apply DS; clear -GR3 GR1 GRP; lia]|].
  eapply fill_frame; [exact S3| exact MU| exact WM| intros POS; rewrite GR2; apply DS; clear -GR3 GR1 POS; lia].
Qed.

Lemma junk_zero_len : forall m A n, junk_at m A n -> n <= 0 -> forall m', junk_at m' A n.
Proof.
  intros m A n [bs H] Hn m'. exists bs.
  pose proof H as H0. destruct H0 as [[[L _] [B0 [B1 B]]] [W0 [W1 WR]]]. cbn in L, B1, W1.
  assert (bs = []) as -> by (destruct bs; [reflexivity| cbn in L; lia]).
  split; [split; [cbn; lia|]|]; unfold bytes_at, wr_at; cbn.
  - split; [lia|]. split; [lia|]. intros i Hi. lia.
  - split; [lia|]. split; [lia|]. intros i Hi. lia.
Qed.

Section Append.
Variables (L : alayout) (W : list (Z * Z)) (m m' : amem).
Hypothesis MU : munch W m m'.
Hypothesis WM : wmono asegs m m'.
Variables (st : astate) (X : aconc) (nres' a n id : Z).
Let ms := sec_map_size n.
Let cs := sec_chunks_of st.
Let nsec := a_nsec st.
Let nres := a_nres st.
Let PA := al_ptr_array L.
Let UB := a + 6144.
Hypothesis WF : awf L st X.
Hypothesis SEC : ASECc cs L st X m.
Hypothesis N : 1 <= n <= AREQMAX.
Hypothesis PRIM : is_primary n = false.
Hypothesis W1 : sec_wf1 L (CSec a ms n).
Hypothesis DJ : Forall (fun ch => a + ms <= sec_mb ch \/ sec_mb ch + sec_ms ch <= a) cs.
Hypothesis NR' : (nsec <> nres /\ nres' = nres)
              \/ (nsec = nres /\ nres' = nres + 16384
                  /\ rw_cells asegs m' (PA + 8 * nres + 8) [CB (Z.to_nat (131072 - 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (131072 - 8)))]).
Hypothesis NRB : nres' <= 1048576.

Hypothesis NEWBUF : let '(d, cap, _) := a_emb st in cap = 0 \/ avoids_all d cap (sec_iv (CSec a ms n)) = true.
Hypothesis WK : Forall (c6_kind (CSec a ms n :: cs) L st) W.

Hypothesis Wch : forall ch, In ch cs ->
     (forall A k, sec_mb ch <= A -> A + k <= sec_mb ch + sec_ms ch -> 0 < k -> disjoint_from W A k)
  /\ (forall A k, shad (sec_mb ch) <= A -> A + k <= shad (sec_mb ch) + sec_ms ch / 8 -> 0 < k -> disjoint_from W A k).
Hypothesis Wpa : 0 < nsec -> disjoint_from W PA (8 * nsec).
Hypothesis Wpj : nsec + 1 < nres -> disjoint_from W (PA + 8 * nsec + 8) (8 * (nres - nsec - 1)).
Hypothesis Wbase : disjoint_from W (AINSTANCE + 80) 8.
Hypothesis Wp0 : disjoint_from W (shad (al_space_beg L)) (shlen K_REGION).
Hypothesis Wshz : forall x, (AIMG_HI <= x < KLS \/ K_HIGH_MEM <= x < ATOP) -> (x < a \/ a + ms <= x) -> disjoint_from W (shad x) 1.

Hypothesis C_srt : rw_cells asegs m' (AINSTANCE + 128) [C1 (Z_to_bv 8 0)].
Hypothesis C_jst : junk_at m' (AINSTANCE + 136) 32.
Hypothesis C_jbs : junk_at m' (AINSTANCE + 168) 512.
Hypothesis C_mtx : rw_cells asegs m' (AINSTANCE + 680) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
Hypothesis C_jgl : junk_at m' (AINSTANCE + 704) 16.
Hypothesis C_slot : rw_cells asegs m' (PA + 8 * nsec) [C8 (Z_to_bv 64 a)].
Hypothesis C_hdr : rw_cells asegs m' a [C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 ms); C8 (Z_to_bv 64 (needed_size n)); C8 (Z_to_bv 64 nsec)].
Hypothesis C_pgj : junk_at m' (a + 32) (4096 - 32).
Hypothesis C_mag : rw_cells asegs m' (a + 4096) [C8 (Z_to_bv 64 0xCC6E96B9CC6E96B9); C8 (Z_to_bv 64 (UB + -16))].
Hypothesis C_lcj : junk_at m' (a + 4096 + 16) (2048 - 32).
Hypothesis C_ahd : rw_cells asegs m' (UB + -16) [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 17); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 id)].
Hypothesis IDR : 0 < id < 2^31.
Hypothesis C_usr : junk_at m' UB (ms - 6144).
Hypothesis C_shf : fill_at m' (shad a) 768 0xfa.
Hypothesis C_shu : rw_cells asegs m' (shad UB) [CB (Z.to_nat (granules n)) (block_shadow_bytes n)].
Hypothesis C_sht : fill_at m' (shad UB + granules n) (ms / 8 - 768 - granules n) 0xfa.

Lemma asec_chunk_new : asec_chunk m' (CSec a ms n) nsec true.
Proof.
  cbn [asec_chunk]. unfold SEC_UOFF, SEC_MAGIC. fold UB.
  replace (UB - 16) with (UB + -16) by (subst UB; lia).
  split; [exact C_hdr|]. split; [exact C_pgj|]. split; [exact C_mag|]. split; [exact C_lcj|].
  split. { exists 17, id. split; [exact C_ahd|]. split; [lia|]. split; [reflexivity| lia]. }
  split; [unfold SEC_UOFF; exact C_usr|]. split; [exact C_shf|]. split; [| exact C_sht].
  unfold sec_user_shadow. exact C_shu.
Qed.

Theorem asec_append : ASEC_of L (st_sec st nres' a ms n) X m'.
Proof.
  pose proof (awf_fresh_none L st X WF) as NONE.
  pose proof (st_sec_fields st nres' a ms n) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12).
  destruct SEC as (WFS & ARR & INST & PZ & SHZ & AXH).
  pose proof WFS as (ALO & WP & WR & WL & WB & WF1 & WD).
  pose proof W1 as W0. cbn [sec_wf1] in W0. destruct W0 as (G1 & G2 & G3 & G4 & G5 & G6 & GC).
  pose proof (sec_facts n N PRIM) as (NB & _ & RSE & RSR & _ & NSE & _ & MSR & MSM & MSB). fold ms in MSR, MSM, MSB.
  pose proof (ao_ptr L ALO) as OP. unfold aobj in OP. fold PA in OP.
  assert (NEWNOT : ~ In (CSec a ms n) cs).
  { intros Hin. pose proof (proj1 (Forall_forall _ _) DJ _ Hin) as D. cbn [sec_mb sec_ms] in D. clear -D MSB. lia. }
  assert (NSR : 0 <= nsec /\ nsec + 1 <= nres' /\ (nres' = nres \/ nres' = nres + 16384)).
  { subst nsec nres. destruct NR' as [(A1 & A2)|(A1 & A2 & _)]; clear -A1 A2 WB; lia. }
  destruct NSR as (NS0 & NS1 & NS2).
  unfold ASEC_of. eapply ASECc_perm; [apply Permutation_sym; eapply sec_chunks_of_insert_sec; [exact NONE| exact E7| exact E9| exact E11]|].
  fold cs. split; [| split; [| split; [| split; [| split]]]].
  6: {
       destruct AXH as (X1 & X2 & X3 & X4 & X5).
       assert (AX1 : AEXHc (CSec a ms n :: cs) L st m) by (repeat (split; [assumption|]); exact (emb_clrC_cons _ _ _ NEWBUF X5)).
       exact (aexhc_frameK _ L st (st_sec st nres' a ms n) m m' W ALO AX1 MU WK eq_refl eq_refl). }
  -
    unfold asec_wf. rewrite E2, E3, E4. split; [exact ALO|]. split; [exact WP|].
    split. { split; [| clear -NRB NS0 NS1; lia]. destruct WR as [WRM _]. destruct NS2 as [-> | ->]; [exact WRM|].
             subst nres. clear -WRM. Z.div_mod_to_equations. lia. }
    split; [cbn [length]; subst nsec; clear -WL; lia|]. split; [clear -NS0 NS1; subst nsec; lia|].
    split; [constructor; [exact W1| exact WF1]|].
    destruct WD as [ND PW]. split; [constructor; [exact NEWNOT| exact ND]|].
    intros ci cj [<-|Hi] [<-|Hj] NE; [exfalso; exact (NE eq_refl)| | |].
    + pose proof (proj1 (Forall_forall _ _) DJ _ Hj) as D. cbn [sec_mb sec_ms] in D |- *. clear -D. lia.
    + pose proof (proj1 (Forall_forall _ _) DJ _ Hi) as D. cbn [sec_mb sec_ms] in D |- *. clear -D. lia.
    + exact (PW ci cj Hi Hj NE).
  -
    destruct ARR as (order & PO & U64 & JK & PER). unfold asec_arr. rewrite E3, E4. fold PA. fold nsec.
    assert (LEN : Z.of_nat (length order) = nsec) by (rewrite (Permutation_length PO); exact WL).
    exists (order ++ [CSec a ms n]).
    split. { eapply Permutation_trans; [apply Permutation_app_comm|]. cbn [app]. apply perm_skip. exact PO. }
    split; [| split].
    + rewrite map_app. cbn [map sec_mb]. apply u64arr_snoc.
      * destruct order as [|o0 order'].
        { destruct U64 as [[B0 [B1 _]] _]. apply u64arr_nil; [clear -OP; lia| clear -OP; atop_facts; lia]. }
        eapply u64arr_frame; [exact U64| exact MU| exact WM|]. rewrite length_map. cbn [length] in LEN |- *.
        replace (8 * Z.of_nat (S (length order'))) with (8 * nsec) by (clear -LEN; lia). apply Wpa. clear -LEN; lia.
      * rewrite length_map. replace (PA + 8 * Z.of_nat (length order)) with (PA + 8 * nsec) by (clear -LEN; lia). exact C_slot.
    + destruct NR' as [(A1 & A2)|(A1 & A2 & ZC)].
      * rewrite A2. destruct (junk_split m (PA + 8 * nsec) 8 (8 * (nres - nsec - 1))
                      ltac:(replace (8 + 8 * (nres - nsec - 1)) with (8 * (nres - nsec)) by (clear; lia); exact JK) ltac:(clear; lia) ltac:(clear -A1 WB; subst nsec nres; lia))
          as [_ JR].
        replace (PA + 8 * (nsec + 1)) with (PA + 8 * nsec + 8) by (clear; lia).
        replace (8 * (nres - (nsec + 1))) with (8 * (nres - nsec - 1)) by (clear; lia).
        destruct (Z_lt_le_dec (nsec + 1) nres) as [LT|GE].
        { eapply junk_frame; [exact JR| exact MU| exact WM| intros _; apply Wpj; exact LT]. }
        eapply junk_zero_len; [exact JR| clear -GE; lia].
      * rewrite A2, A1. subst nres. replace (PA + 8 * (a_nres st + 1)) with (PA + 8 * a_nres st + 8) by (clear; lia).
        replace (8 * (a_nres st + 16384 - (a_nres st + 1))) with (131072 - 8) by (clear; lia). eexists. exact ZC.
    + intros i ch Hi.
      destruct (Nat.lt_ge_cases i (length order)) as [LT|GE].
      * rewrite nth_error_app1 in Hi by exact LT. destruct (PER i ch Hi) as (lv & LV & CH).
        assert (Hin : In ch cs) by (eapply Permutation_in; [exact PO| eapply nth_error_In; exact Hi]).
        destruct (asec_wf_all L st cs ch WFS Hin) as (mb & ms' & n' & -> & WF1c).
        exists lv. split.
        { rewrite LV. unfold sec_live. rewrite E7. split; intros [p Hp].
          - exists p. rewrite lookup_insert_ne; [exact Hp|]. intros E. subst p. rewrite NONE in Hp. discriminate.
          - destruct (N.eq_dec p (a_next st)) as [->|NE].
            + rewrite lookup_insert_eq in Hp. injection Hp as Ea Em En. exfalso. apply NEWNOT. rewrite <- Ea, <- Em, <- En in Hin. exact Hin.
            + exists p. rewrite lookup_insert_ne in Hp by (intros E; apply NE; symmetry; exact E). exact Hp. }
        destruct (Wch _ Hin) as [DC DS]. cbn [sec_mb sec_ms] in DC, DS.
        eapply asec_chunk_frameW; [exact MU| exact WM| exact WF1c| exact DC| exact DS| exact CH].
      * rewrite nth_error_app2 in Hi by exact GE.
        assert (EI : i = length order) by (destruct (i - length order)%nat as [|k] eqn:EK; [clear -GE EK; lia| cbn in Hi; destruct k; discriminate]).
        subst i. rewrite Nat.sub_diag in Hi. cbn in Hi. injection Hi as <-.
        exists true. split.
        { split; [intros _| reflexivity]. exists (a_next st). rewrite E7, lookup_insert_eq. reflexivity. }
        rewrite LEN. exact asec_chunk_new.
  -
    destruct INST as (I1 & _ & _ & _ & _ & _). unfold asec_inst. unfold AINSTANCE in *.
    split; [eapply cells_frame; [exact I1| exact MU| exact WM| cbn; exact Wbase]|].
    split; [exists (Z_to_bv 8 0); exact C_srt|]. split; [exact C_jst|]. split; [exact C_jbs|]. split; [| exact C_jgl].
    pose proof C_mtx as M4. rw_split M4 1%nat M0 M3. exact M3.
  -
    unfold aprim0 in *. eapply azero_frame; [exact PZ| exact MU| exact WM| intros _; exact Wp0].
  -
    intros x Hx HF HC. apply Forall_cons_iff in HC. destruct HC as [HCn HC]. cbn [sec_mb sec_ms] in HCn.
    assert (SX : 0 <= shad x < 2^64) by (rewrite shad_div; unfold ASHOFF, K_HIGH_MEM in *; unfold AIMG_HI, KLS in Hx; clear -Hx; Z.div_mod_to_equations; lia).
    rewrite <- (SHZ x Hx HF HC). apply MU. rewrite wa_unsigned by exact SX.
    eapply (disjoint_outside W (shad x) 1); [| clear; lia]. apply Wshz; [exact Hx| clear -HCn Hx; lia].
Qed.
End Append.

Definition WT (L : alayout) (sp a ms nsec nres nres' : Z) : list (Z * Z) :=
  [(sp - 4096, sp); (al_t L + 2800, al_t L + 3169); (AINSTANCE + 112, AINSTANCE + 720);
   (al_ptr_array L + 8 * nsec, al_ptr_array L + 8 * nsec + 8); (al_ptr_array L + 8 * nres, al_ptr_array L + 8 * nres');
   (a, a + ms); (shad a, shad a + ms / 8);
   (0x1ab988, 0x5fb9d0); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608)]%Z.

Definition wt_facts (L : alayout) (sp lo a ms nsec nres nres' : Z) : Prop :=
     alayout_ok L /\ ATOP <= lo /\ lo <= sp - 4096
  /\ ablk a (a + ms) /\ a + ms <= ATOP /\ a mod 4096 = 0 /\ ms mod 4096 = 0 /\ 0 < ms /\ sec_clear L a ms
  /\ 0 <= nsec /\ nsec + 1 <= nres' /\ 8 * nres' <= 8388608 /\ 0 <= nres <= nres'.

Local Lemma ablk_int : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6483968 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
Local Lemma aobj_int : forall a n, aobj a n -> 0x10000 <= n ->
  6483968 <= a /\ a + n <= ATOP /\ exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof.
  intros a n H Hn. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. destruct H as (H1 & H2 & H3 & H4 & H5).
  split; [lia|]. split; [lia|]. destruct H4; [exists 0 | exists 1]; lia.
Qed.
Local Lemma aobj4_int : forall a, aobj a 4096 ->
  4096 <= a /\ a + 4096 <= ATOP
  /\ (exists k, 0 <= k <= 1 /\ a + 4096 <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a)
  /\ (exists j, 0 <= j <= 1 /\ a + 4096 <= 65536 + j * 18446744073709551616 /\ 6483968 * j <= a).
Proof.
  intros a H. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. destruct H as (H1 & H2 & H3 & H4 & H5).
  split; [lia|]. split; [lia|]. split; [destruct H4; [exists 0 | exists 1]; lia | destruct H5 as [_ [H5|H5]]; [exists 0 | exists 1]; lia].
Qed.

Section KW.
Variables (L : alayout) (sp lo a ms nsec nres nres' : Z).
Hypothesis WTF : wt_facts L sp lo a ms nsec nres nres'.
Let W' := List.filter nonempty (WT L sp a ms nsec nres nres').

Local Ltac inWT Hiv := unfold WT in Hiv; cbn [In] in Hiv;
  destruct Hiv as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]; cbn [fst snd] in *.
Local Ltac facts :=
  lazymatch goal with |- _ =>
  pose proof WTF as (ALO & CEIL & LO & AHI0 & ACE & AAL & MSM & MSP & (C_t & C_c & C_r & C_p & C_n & C_s & C_f & C_d) & NS0 & NS1 & NS8 & NS9);
  pose proof (ao_t L ALO) as OT; pose proof (ao_ctx L ALO) as OC; pose proof (ao_res L ALO) as ORS; pose proof (ao_nodes L ALO) as ON;
  pose proof (ao_store L ALO) as OS; pose proof (ao_ptr L ALO) as OP; unfold aobj in OT, OC, ORS, ON, OS, OP;
  pose proof (aobj4_int _ (ao_t L ALO)) as (_ & _ & [kT OTs] & [jT OTi]); pose proof (aobj_int _ _ (ao_ctx L ALO) ltac:(clear; lia)) as (OCi & _ & [kC OCs]);
  pose proof (aobj_int _ _ (ao_nodes L ALO) ltac:(clear; lia)) as (ONi & _ & [kN ONs]); pose proof (aobj_int _ _ (ao_store L ALO) ltac:(clear; lia)) as (OSi & _ & [kS OSs]);
  pose proof (aobj_int _ _ (ao_ptr L ALO) ltac:(clear; lia)) as (OPi & _ & [kP OPs]); pose proof (ao_res_hi L ALO) as RHI;
  destruct (ablk_int _ _ AHI0) as [kA ABND]; pose proof (ablk_lin _ _ AHI0) as (AL1 & AL2 & _ & _); unfold AIMG_HI in AL1;
  pose proof (ad_t_res L ALO) as D_t_res; pose proof (ad_nodes_res L ALO) as D_n_res; pose proof (ad_store_res L ALO) as D_s_res;
  pose proof (ad_ptr_res L ALO) as D_p_res; pose proof (ad_t_ctx L ALO) as D_t_c; pose proof (ad_t_nodes L ALO) as D_t_n;
  pose proof (ad_t_store L ALO) as D_t_s; pose proof (ad_t_ptr L ALO) as D_t_p; pose proof (ad_ctx_nodes L ALO) as D_c_n;
  pose proof (ad_ctx_store L ALO) as D_c_s; pose proof (ad_ctx_ptr L ALO) as D_c_p;
  unfold adisj in D_t_res, D_n_res, D_s_res, D_p_res, D_t_c, D_t_n, D_t_s, D_t_p, D_c_n, D_c_s, D_c_p
  end.

Lemma WT_shad : 0x800bde00 <= shad a /\ shad a + ms / 8 = shad (a + ms) /\ shad (a + ms) <= 0x10007fef8000
                /\ (forall x, x < a -> shad x + 1 <= shad a) /\ (forall x, a + ms <= x -> shad (a + ms) <= shad x).
Proof.
  facts. rewrite !shad_div. unfold ASHOFF in *. split; [clear -AL1; Z.div_mod_to_equations; lia|].
  split; [clear -AAL MSM; Z.div_mod_to_equations; lia|]. split; [clear -ACE; Z.div_mod_to_equations; lia|].
  split; intros x Hx; rewrite shad_div; unfold ASHOFF; [clear -Hx AAL| clear -Hx]; Z.div_mod_to_equations; lia.
Qed.

Lemma KT_X : forall A k, 0 <= k ->
  (forall iv, In iv (WT L sp a ms nsec nres nres') -> fst iv < snd iv -> A + k <= fst iv \/ snd iv <= A) ->
  disjoint_from W' A k.
Proof.
  intros A k Hk H. subst W'. apply disjoint_from_Forall. apply Forall_forall. intros iv Hiv.
  apply List.filter_In in Hiv. destruct Hiv as [Hiv NEV]. unfold nonempty in NEV. apply Z.ltb_lt in NEV. exact (H iv Hiv NEV).
Qed.

Lemma KT_img : forall A k, 65536 <= A -> 0 <= k -> A + k <= AIMG_HI ->
  (A + k <= AINSTANCE + 112 \/ AINSTANCE + 720 <= A) -> (A + k <= 0x1ab988 \/ 0x5fb9d0 <= A) -> disjoint_from W' A k.
Proof.
  facts. pose proof WT_shad as (SA1 & SA2 & SA3 & _).
  intros A k H1 H2 H3 H4 H5. apply KT_X; [exact H2|]. intros iv Hiv NEV. inWT Hiv; unfold AIMG_HI, AINSTANCE in *;
    clear -H1 H2 H3 H4 H5 NEV CEIL LO OT OP AL1 SA1 ON OS NS0 NS9 OTs OTi ONs ONi OSs OSi OPs OPi; lia.
Qed.

Lemma KT_obj : forall A k, (A + k <= 65536 \/ 6483968 <= A) -> (A + k <= 2147446784 \/ 17594333495296 <= A) -> 0 <= k -> A + k <= ATOP ->
  (A + k <= al_t L + 2800 \/ al_t L + 3169 <= A) -> (A + k <= al_ptr_array L \/ al_ptr_array L + 8388608 <= A) ->
  (A + k <= a \/ a + ms <= A) -> (A + k <= al_nodes L \/ al_nodes L + 1048576 <= A) -> (A + k <= al_store L \/ al_store L + 8388608 <= A) ->
  disjoint_from W' A k.
Proof.
  facts. pose proof WT_shad as (SA1 & SA2 & SA3 & _).
  intros A k H0 H1 H2 H3 H4 H5 H6 H7 H8. apply KT_X; [exact H2|]. intros iv Hiv NEV. inWT Hiv; unfold AIMG_HI, AINSTANCE in *;
    clear -H0 H1 H2 H3 H4 H5 H6 H7 H8 NEV CEIL LO NS0 NS1 NS8 NS9 SA1 SA2 SA3; lia.
Qed.

Lemma KT_shad : forall A k, 2147446784 <= A -> 0 <= k -> A + k <= 17594333495296 ->
  (A + k <= shad a \/ shad (a + ms) <= A) -> disjoint_from W' A k.
Proof.
  facts. pose proof WT_shad as (SA1 & SA2 & SA3 & _).
  intros A k H1 H2 H3 H4. apply KT_X; [exact H2|]. intros iv Hiv NEV. inWT Hiv; unfold AIMG_HI, AINSTANCE in *;
    clear -H1 H2 H3 H4 NEV CEIL LO OT OP ABND ON OS SA2 NS0 NS1 NS8 NS9 OTs OTi ONs ONi OSs OSi OPs OPi; lia.
Qed.

Lemma KT_t : forall A k, al_t L <= A -> 0 <= k -> A + k <= al_t L + 2800 -> disjoint_from W' A k.
Proof. facts. intros A k H1 H2 H3. apply KT_obj; atop_facts; clear -H1 H2 H3 OT D_t_p C_t D_t_n D_t_s OTs OTi; lia. Qed.

Lemma KT_ctx : forall A k, al_ctx L <= A -> 0 <= k -> A + k <= al_ctx L + 65536 -> disjoint_from W' A k.
Proof. facts. intros A k H1 H2 H3. apply KT_obj; atop_facts; clear -H1 H2 H3 OC OT D_t_c D_c_p C_c D_c_n D_c_s OTs OTi OCs OCi; lia. Qed.

Lemma KT_res : forall A k, al_res L <= A -> 0 <= k -> A + k <= al_res L + 137439023104 -> disjoint_from W' A k.
Proof. facts. intros A k H1 H2 H3. apply KT_obj; atop_facts; clear -H1 H2 H3 ORS RHI OT D_t_res D_p_res C_r D_n_res D_s_res OTs OTi; lia. Qed.

Lemma KT_res_geo : 2201439137792 <= shad (al_res L) /\ shad (al_res L) + shlen 137439023104 = shad (al_res L + 137439023104)
                   /\ shad (al_res L + 137439023104) <= 0x10007fef8000
                   /\ (shad (al_res L + 137439023104) <= shad a \/ shad (a + ms) <= shad (al_res L)).
Proof. facts. rewrite !shad_div, shlen_div. unfold ASHOFF in *. clear -ORS RHI C_r AAL. Z.div_mod_to_equations. lia. Qed.

Lemma KT_res_sh : forall A k, shad (al_res L) <= A -> 0 <= k -> A + k <= shad (al_res L + 137439023104) -> disjoint_from W' A k.
Proof. pose proof KT_res_geo as (SR1 & SR2 & SR3 & SR4). intros A k H1 H2 H3. apply KT_shad; clear -H1 H2 H3 SR1 SR3 SR4; lia. Qed.

Lemma WT_kinds : forall cs st n, sec_wf1 L (CSec a ms n) -> Forall (c6_kind (CSec a ms n :: cs) L st) W'.
Proof.
  intros cs st n VW. facts. pose proof WT_shad as (SA1 & SA2 & SA3 & _).
  apply Forall_forall. intros iv Hin. unfold W' in Hin. apply List.filter_In in Hin. destruct Hin as [Hin _].
  unfold c6_kind. intros NEV. inWT Hin.
  - left. unfold AC6U.c6_std. left. clear -CEIL LO. lia.
  - left. unfold AC6U.c6_std. right; left. clear. lia.
  - left. unfold AC6U.c6_std. do 5 right; left. unfold AINSTANCE. clear. lia.
  - left. unfold AC6U.c6_std. do 12 right. clear -NS0 NS1 NS8 NS9. lia.
  - left. unfold AC6U.c6_std. do 12 right. clear -NS0 NS1 NS8 NS9. lia.
  - right; right; left. exists (CSec a ms n). split; [left; reflexivity|]. split; [exact VW|]. cbn [sec_mb sec_ms]. clear. lia.
  - left. unfold AC6U.c6_std. do 4 right; left. clear -SA1 SA2 SA3. lia.
  - left. unfold AC6U.c6_std. do 7 right; left. clear. lia.
  - left. unfold AC6U.c6_std. do 8 right; left. clear. lia.
  - left. unfold AC6U.c6_std. do 9 right; left. clear. lia.
Qed.

Lemma KT_rt : forall m m', munch W' m m' -> wmono asegs m m' -> arep_rt L m -> arep_rt L m'.
Proof.
  intros m m' MU WM RT. eapply arep_rt_frame; [exact MU | exact WM | exact RT |]. unfold rt_hulls, ATP88, ATSD.
  repeat (apply Forall_cons; [cbn [fst snd]; first [apply KT_img; clear; unfold AIMG_HI, AINSTANCE; lia | apply KT_ctx; clear; lia] |]). apply Forall_nil.
Qed.
Lemma KT_rt2 : forall m m', munch W' m m' -> wmono asegs m m' -> arep_rt2 m -> arep_rt2 m'.
Proof. intros m m' MU WM RT2. eapply arep_rt2_frame; [exact MU | exact WM | exact RT2 | | |]; apply KT_img; clear; unfold AIMG_HI, AINSTANCE; lia. Qed.
Lemma KT_rt3 : forall m m', munch W' m m' -> wmono asegs m m' -> arep_rt3 m -> arep_rt3 m'.
Proof.
  intros m m' MU WM RT3. eapply arep_rt3_frame; [exact MU | exact WM | exact RT3 |]. unfold rt3_hulls.
  repeat (apply Forall_cons; [cbn [fst snd]; apply KT_img; clear; unfold AIMG_HI, AINSTANCE; lia |]). apply Forall_nil.
Qed.
Lemma KT_relro : forall m m', munch W' m m' -> arelro m -> arelro m'.
Proof. intros m m' MU HRO. eapply arelro_frame; [exact MU | exact HRO | apply KT_img; clear; unfold ARELRO_LO, ARELRO_HI, AIMG_HI, AINSTANCE; lia]. Qed.
End KW.

Section Store.
Variable DI : ADepotIface.
Variables (AQ : alayout -> astate -> aconc -> amem -> Prop) (AFK : alayout -> list ablock -> amem -> Prop).
Let AHS : aholes := AH DI AQ ASEC_of AFK.
Hypothesis HL : ahole_laws AHS.
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI) CI.
Hypothesis CI_OK2 : Forall (fun iv => snd iv <= AINSTANCE \/ AINSTANCE + 728 <= fst iv) CI.

Theorem store_sec : forall (L : alayout) (RNG RNG' : footprint) (sp lo : Z) (m m' : amem) (st : astate) (X : aconc) (LB : list ablock)
    (n a nres' id : Z) (sj' : list word) (RESV : list (Z * Z)),
  let nsec := a_nsec st in let nres := a_nres st in let PA := al_ptr_array L in let ms := sec_map_size n in
  let UB := a + 6144 in let t := al_t L in
  alayout_ok L -> arng L RNG st -> AREP AHS L st X m -> ablocks L st X LB -> AFK L LB m ->
  1 <= n <= AREQMAX -> is_primary n = false ->
  sfresh RESV st n a = true -> aresv_ok L RESV ->
  ATOP <= lo -> lo <= sp - 4096 -> sp <= 2^47 ->
  fp_le RNG RNG' -> rng RNG' a ms -> rng RNG' (shad a) (ms / 8) ->
  ((nsec <> nres /\ nres' = nres)
   \/ (nsec = nres /\ nres' = nres + 16384
       /\ rw_cells asegs m' (PA + 8 * nres + 8) [CB (Z.to_nat (131072 - 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (131072 - 8)))])) ->
  nres' <= 1048576 -> rng RNG' PA (8 * nres') ->
  munch (WT L sp a ms nsec nres nres') m m' -> wmono asegs m m' ->

  u64arr asegs m' (t + 2800) sj' -> length sj' = 46%nat -> rw_cells asegs m' (t + 3168) [C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m' (AINSTANCE + 112) [C8 (Z_to_bv 64 nres'); C8 (Z_to_bv 64 (nsec + 1))] ->
  rw_cells asegs m' (AINSTANCE + 128) [C1 (Z_to_bv 8 0)] -> junk_at m' (AINSTANCE + 136) 32 -> junk_at m' (AINSTANCE + 168) 512 ->
  rw_cells asegs m' (AINSTANCE + 680) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  junk_at m' (AINSTANCE + 704) 16 ->
  rw_cells asegs m' (PA + 8 * nsec) [C8 (Z_to_bv 64 a)] ->
  rw_cells asegs m' a [C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 ms); C8 (Z_to_bv 64 (needed_size n)); C8 (Z_to_bv 64 nsec)] ->
  junk_at m' (a + 32) (4096 - 32) ->
  rw_cells asegs m' (a + 4096) [C8 (Z_to_bv 64 0xCC6E96B9CC6E96B9); C8 (Z_to_bv 64 (UB + -16))] ->
  junk_at m' (a + 4096 + 16) (2048 - 32) ->
  rw_cells asegs m' (UB + -16) [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 17); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 id)] ->
  0 < id < 2^31 ->
  junk_at m' UB (ms - 6144) ->
  fill_at m' (shad a) 768 0xfa ->
  rw_cells asegs m' (shad UB) [CB (Z.to_nat (granules n)) (block_shadow_bytes n)] ->
  fill_at m' (shad UB + granules n) (ms / 8 - 768 - granules n) 0xfa ->
  ADEPOT DI L m' ->
     aheap_pres CI LB sp m m'
  /\ AHEAP_P AHS L RNG' (st_sec st nres' a ms n) (HB (a_next st) UB n :: LB) m'.
Proof.
  intros until RESV. cbv zeta.
  intros ALO ARNG AR BL HFK N PRIM FRSH ROK CEIL LO SP47 FPLE RA RSA NR' NRB RPA' MU0 WM
         STATS LSJ UNW I112 I128 J136 J168 I680 J704 SLOT HDR PGJ MAG LCJ AHD IDR USR SHF SHU SHT DEP.
  set (ms := sec_map_size n) in *.

  pose proof (valid_geo L RESV st n a N PRIM FRSH ROK) as (AAL & AHI0 & ACE & MSP & _). fold ms in ACE, MSP.
  pose proof (valid_clear L RESV st n a N PRIM FRSH ROK) as VC. fold ms in VC.
  pose proof (valid_hulls L RESV st n a N PRIM FRSH ROK) as VH. fold ms in VH.
  pose proof (valid_chunks L RESV st n a N PRIM FRSH ROK) as VK. fold ms in VK.
  pose proof (valid_wf1 L RESV st n a N PRIM FRSH ROK) as VW. fold ms in VW.
  pose proof (sec_facts n N PRIM) as (NB & _ & RSE & RSR & _ & NSE & _ & MSR & MSM & MSB). fold ms in MSR, MSM, MSB.
  destruct VC as (C_t & C_c & C_r & C_p & C_n & C_s & C_f & C_d).
  unfold K_HIGH_MEM in AHI0.
  pose proof (munch_filter_nonempty _ m m' MU0) as MU. clear MU0. set (W' := List.filter nonempty (WT L sp a ms (a_nsec st) (a_nres st) nres')) in *.
  assert (NE : Forall (fun iv => fst iv < snd iv) W') by (apply nonempty_filter).

  pose proof (alayout_space L ALO) as (SP1 & SP2 & SP3 & SP4).
  pose proof (ao_t L ALO) as OT. pose proof (ao_ctx L ALO) as OC. pose proof (ao_res L ALO) as ORS. pose proof (ao_nodes L ALO) as ON. pose proof (ao_store L ALO) as OS.
  pose proof (ao_fake L ALO) as OFK. pose proof (ao_ptr L ALO) as OP. pose proof (ao_dtls L ALO) as OD.
  unfold aobj in OT, OC, ORS, ON, OS, OFK, OP, OD. pose proof (ao_space L ALO) as RSP.
  pose proof (aobj4_int _ (ao_t L ALO)) as (_ & _ & [kT OTs] & [jT OTi]). pose proof (aobj_int _ _ (ao_ctx L ALO) ltac:(clear; lia)) as (OCi & _ & [kC OCs]).
  pose proof (aobj_int _ _ (ao_nodes L ALO) ltac:(clear; lia)) as (ONi & _ & [kN ONs]). pose proof (aobj_int _ _ (ao_store L ALO) ltac:(clear; lia)) as (OSi & _ & [kS OSs]).
  pose proof (aobj_int _ _ (ao_ptr L ALO) ltac:(clear; lia)) as (OPi & _ & [kP OPs]). pose proof (aobj_int _ _ (ao_fake L ALO) ltac:(clear; lia)) as (OFKi & _ & [kF OFKs]).
  pose proof (aobj4_int _ (ao_dtls L ALO)) as (_ & _ & [kD ODs] & [jD ODi]). pose proof (ao_res_hi L ALO) as RHI.
  destruct (ablk_int _ _ AHI0) as [kA ABND]. pose proof (ablk_lin _ _ AHI0) as (AL1 & AL2 & _ & _). unfold AIMG_HI in AL1.
  pose proof (ad_t_res L ALO) as D_t_res. pose proof (ad_ctx_res L ALO) as D_c_res. pose proof (ad_nodes_res L ALO) as D_n_res. pose proof (ad_store_res L ALO) as D_s_res.
  pose proof (ad_fake_res L ALO) as D_f_res. pose proof (ad_ptr_res L ALO) as D_p_res. pose proof (ad_t_ctx L ALO) as D_t_c.
  pose proof (ad_t_nodes L ALO) as D_t_n. pose proof (ad_t_store L ALO) as D_t_s. pose proof (ad_t_fake L ALO) as D_t_f. pose proof (ad_t_ptr L ALO) as D_t_p.
  pose proof (ad_ctx_nodes L ALO) as D_c_n. pose proof (ad_ctx_store L ALO) as D_c_s. pose proof (ad_ctx_fake L ALO) as D_c_f. pose proof (ad_ctx_ptr L ALO) as D_c_p.
  pose proof (ad_nodes_fake L ALO) as D_n_f. pose proof (ad_nodes_ptr L ALO) as D_n_p. pose proof (ad_store_fake L ALO) as D_s_f. pose proof (ad_store_ptr L ALO) as D_s_p.
  pose proof (ad_fake_ptr L ALO) as D_f_p. pose proof (ad_dtls_res L ALO) as D_d_res. pose proof (ad_t_dtls L ALO) as D_t_d. pose proof (ad_dtls_ptr L ALO) as D_d_p.
  pose proof (ad_nodes_dtls L ALO) as D_n_d. pose proof (ad_store_dtls L ALO) as D_s_d. pose proof (ad_fake_dtls L ALO) as D_f_d.
  unfold adisj in D_t_res, D_c_res, D_n_res, D_s_res, D_f_res, D_p_res, D_t_c, D_t_n, D_t_s, D_t_f, D_t_p, D_c_n, D_c_s, D_c_f, D_c_p,
                   D_n_f, D_n_p, D_s_f, D_s_p, D_f_p, D_d_res, D_t_d, D_d_p, D_n_d, D_s_d, D_f_d.

  pose proof AR as AR0. destruct AR0 as (WF & RT & INST & THR & CLS & HQ & HS & HD & HRO & RT2 & AVL & RT3).
  pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVE & FRESH & UNIQ).
  pose proof HS as HS0. unfold AHS, AH in HS0. cbn [ah_sec] in HS0. unfold ASEC_of in HS0.
  pose proof HS0 as (WFS & ARR & INST2 & PZ & SHZ & AXH). pose proof WFS as (_ & WP & WR & WL & WB & WF1 & WD).
  assert (NSR : 0 <= a_nsec st /\ a_nsec st + 1 <= nres' /\ 8 * nres' <= 8388608 /\ a_nres st <= nres').
  { destruct NR' as [(A1 & A2)|(A1 & A2 & _)]; clear -A1 A2 WB NRB WR; lia. }
  destruct NSR as (NS0 & NS1 & NS8 & NS9).

  assert (WTF : wt_facts L sp lo a ms (a_nsec st) (a_nres st) nres').
  { unfold wt_facts. repeat lazymatch goal with |- _ /\ _ => split end; try assumption.
    - unfold sec_clear. repeat (split; [assumption|]). assumption.
    - clear -WB; lia. }
  pose proof (WT_shad L sp lo a ms _ _ _ WTF) as (SA1 & SA2 & SA3 & SAlt & SAge).
  pose proof (KT_X L sp a ms (a_nsec st) (a_nres st) nres') as KX. pose proof (KT_img L sp lo a ms _ _ _ WTF) as Kimg.
  pose proof (KT_obj L sp lo a ms _ _ _ WTF) as Kobj. pose proof (KT_shad L sp lo a ms _ _ _ WTF) as Kshad.
pose proof (KT_t L sp lo a ms _ _ _ WTF) as Kt.
  pose proof (KT_ctx L sp lo a ms _ _ _ WTF) as Kctx. pose proof (KT_res L sp lo a ms _ _ _ WTF) as Kres.
  pose proof (KT_res_sh L sp lo a ms _ _ _ WTF) as Kres_sh. pose proof (KT_res_geo L sp lo a ms _ _ _ WTF) as (SR1 & SR2 & SR3 & SR4).
  fold W' in KX, Kimg, Kobj, Kshad, Kt, Kctx, Kres, Kres_sh.
  Local Ltac inWT Hiv := unfold WT in Hiv; cbn [In] in Hiv;
    destruct Hiv as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]; cbn [fst snd] in *.

  assert (BB : forall b, In b (x_busy X) -> al_res L <= xb_alloc L b /\ xb_alloc L b + size_of_class (xb_class b) <= al_res L + 137439023104).
  { intros b Hb. destruct (BUSY b Hb) as [CLB _].
    destruct (PERC (xb_class b) CLB) as (Q1 & Q2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & QR).
    pose proof (size_of_class_facts (xb_class b) CLB) as [QS _].
    assert (KB : 0 <= xb_slot b < ndist st (xb_class b)).
    { apply QR. apply in_app_iff. right. apply in_app_iff. right. unfold busy_slots. apply in_map_iff. exists b. split; [reflexivity|].
      apply filter_In. split; [exact Hb| apply Z.eqb_refl]. }
    pose proof (slot_in_region L st (xb_class b) (xb_slot b) ltac:(clear -QS; lia) (proj1 Q1) KB) as (P5 & P4 & P0).
    unfold xb_alloc, aregion, K_REGION, K_FREEARR_OFF, K_NUM_CLASSES in *. clear -P5 P4 Q1 Q2 CLB RSP. lia. }
  pose proof (st_sec_fields st nres' a ms n) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12).
  set (st2 := st_sec st nres' a ms n) in *.

  assert (AR' : AREP AHS L st2 X m').
  { split; [apply awf_sec; exact WF|].
    split. { eapply arep_rt_frame; [exact MU | exact WM | exact RT |]. unfold rt_hulls, ATP88, ATSD.
             repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI, AINSTANCE; lia | apply Kctx; clear; lia] |]). apply Forall_nil. }
    split. {
      destruct INST as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9). unfold ainstance. subst st2. rewrite E3, E4.
      split; [eapply cells_frame; [exact I1| exact MU| exact WM| cbn; apply Kimg; clear; unfold AIMG_HI, AINSTANCE; lia]|].
      split; [eapply cells_frame; [exact I2| exact MU| exact WM| cbn; apply Kimg; clear; unfold AIMG_HI, AINSTANCE; lia]|].
      split; [eapply cells_frame; [exact I3| exact MU| exact WM| cbn; apply Kimg; clear; unfold AIMG_HI, AINSTANCE; lia]|].
      split; [eapply cells_frame; [exact I4| exact MU| exact WM| cbn; apply Kimg; clear; unfold AIMG_HI, AINSTANCE; lia]|].
      split; [exact I112|].
      split; [pose proof I680 as M4; rw_split M4 1%nat M0 M3; exact M0|].
      split; [eapply cells_frame; [exact I7| exact MU| exact WM| cbn; apply Kimg; clear; unfold AIMG_HI, AINSTANCE; lia]|].
      split; [eapply cells_frame; [exact I8| exact MU| exact WM| cbn; apply Kimg; clear; unfold AIMG_HI, AINSTANCE; lia]|].
      eapply cells_frame; [exact I9| exact MU| exact WM| cbn; apply Kimg; clear; unfold AIMG_HI, AINSTANCE; lia]. }
    split. {
      destruct THR as (T0 & T40 & CACHES & CSTATS & _ & _). unfold athread.
      split; [eapply cells_frame; [exact T0 | exact MU | exact WM | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; apply Kt; clear; lia]|].
      split; [eapply cells_frame; [exact T40 | exact MU | exact WM | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; apply Kt; clear; lia]|].
      split. { intros c Hc. eapply acache_cells_frame; [exact MU | exact WM | exact (CACHES c Hc) | subst st2; reflexivity | subst st2; reflexivity | reflexivity |].
               unfold acache_addr. unfold K_NUM_CLASSES in Hc. apply Kt; clear -Hc; lia. }
      split; [eapply junk_frame; [exact CSTATS | exact MU | exact WM | intros _; apply Kt; clear; lia]|].
      split; [exists sj'; split; [exact STATS| exact LSJ]| exact UNW]. }
    split. {
      intros c Hc. destruct (CLS c Hc) as (REG & FARR & SLOTS & SHADOW).
      destruct (PERC c Hc) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & QLENF & QLENC & QCNTB & QND & QRANGE).
      pose proof (size_of_class_facts c Hc) as [QS QS16]. pose proof (aregion_mod L c SAL) as RM. unfold K_NUM_CLASSES in Hc.
      assert (RI : al_res L <= aregion L c /\ aregion L c + K_REGION <= al_space_beg L + K_SPACE_SIZE
                   /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104).
      { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc RSP. lia. }
      destruct RI as (RI1 & RI2 & RI3). unfold K_REGION, K_SPACE_SIZE in RI2, RI3. change (2^37) with 137438953472 in RI2, RI3.
      split; [| split; [| split]].
      - eapply aregion_cells_frame; [exact MU | exact WM | exact REG | subst st2; reflexivity | subst st2; reflexivity | subst st2; reflexivity | subst st2; reflexivity |].
        apply Kres; unfold aregion_info, ARI_STRIDE, K_SPACE_SIZE; change (2^37) with 137438953472; clear -Hc RSP; lia.
      - eapply afreearray_frame; [exact MU | exact WM | exact FARR | subst st2; reflexivity | subst st2; reflexivity | reflexivity | exact QLENF | exact Q5 | | clear -Q6; lia |].
        + apply Kres; unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX in *; [clear -RI1; lia | clear -Q5 Q6; lia | clear -RI2 RI3 Q6; lia].
        + apply Kres_sh; [apply shad_mono; unfold afreearr, K_FREEARR_OFF; clear -RI1; lia | apply shlen_nonneg; clear -Q5 Q6; lia |].
          rewrite <- shad_add_shlen by (unfold afreearr, K_FREEARR_OFF; clear -RM; Z.div_mod_to_equations; lia). apply shad_mono.
          unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX in *. clear -RI2 RI3 Q6. lia.
      - eapply (aslots_update L W' m m' MU WM st st2 X X c (-1)); [exact SLOTS | subst st2; reflexivity | subst st2; reflexivity | subst st2; reflexivity | | | intros Hk; exfalso; clear -Hk; lia].
        + intros k Hk _. pose proof (slot_in_region L st c k ltac:(clear -QS; lia) (proj1 Q1) Hk) as (P5 & P4 & P0).
          split; [reflexivity|]. split.
          * apply Kres; [clear -P5 RI1; lia | clear -QS; lia | clear -P4 Q1 Q2 RI2 RI3; unfold K_FREEARR_OFF in *; lia].
          * intros b Hb. pose proof Hb as Hb'. unfold busy_of in Hb'. apply find_some in Hb'. destruct Hb' as [HIn HP].
            apply andb_true_iff in HP. destruct HP as [HP1 HP2]. apply Z.eqb_eq in HP1. apply Z.eqb_eq in HP2.
            split; [exact HP1|]. split; [exact HP2|]. exact (awf_fits L st X b WF HIn).
        + intros POS. apply Kres; [clear -Q1 RI1; lia | clear -POS; lia | clear -Q1 Q2 RI2 RI3; unfold K_FREEARR_OFF in *; lia].
      - eapply (aslot_shadow_update L W' m m' MU WM st st2 X X c (-1)); [exact SHADOW | subst st2; reflexivity | subst st2; reflexivity | subst st2; reflexivity | | | intros Hk; exfalso; clear -Hk; lia | apply shlen_nonneg; clear -QS; lia].
        + intros k Hk _. pose proof (slot_in_region L st c k ltac:(clear -QS; lia) (proj1 Q1) Hk) as (P5 & P4 & P0).
          pose proof (slot_aligned L c k SAL ltac:(unfold K_NUM_CLASSES; clear -Hc; lia)) as AL.
          split; [reflexivity|]. apply Kres_sh; [apply shad_mono; clear -P5 RI1; lia | rewrite shlen_div; clear -QS QS16; Z.div_mod_to_equations; lia |].
          rewrite <- shad_add_shlen by (clear -AL; Z.div_mod_to_equations; lia). apply shad_mono. clear -P4 Q1 Q2 RI2 RI3. unfold K_FREEARR_OFF in *. lia.
        + intros POS. apply Kres_sh; [apply shad_mono; clear -Q1 RI1; lia | clear -POS; lia |].
          rewrite <- shad_add_shlen by (pose proof (mod16_of_class _ _ Q3 QS16 ltac:(clear -QS; lia)) as AM; clear -AM RM; Z.div_mod_to_equations; lia).
          apply shad_mono. clear -Q1 Q2 RI2 RI3. unfold K_FREEARR_OFF in *. lia. }
    split. {
      eapply (hq_frame _ HL L st st2 X X m m' W'); [exact HQ | exact MU | exact WM | |].
      - unfold quar_untouched. apply Forall_forall. intros iv Hin.
        unfold W' in Hin. apply List.filter_In in Hin. destruct Hin as [Hin NEV]. unfold nonempty in NEV. apply Z.ltb_lt in NEV.
        inWT Hin. all: unfold AINSTANCE in *.
        all: split; [clear -NEV CEIL LO OT OP AHI0 SA1 SA2 SA3 ON OS C_t D_t_p D_t_n D_t_s NS0 NS1 NS8 NS9 WB ABND AL1 OTs OTi ONs ONi OSs OSi OPs OPi; lia|].
        all: split; [clear -NEV CEIL LO OT OP AHI0 SA1 SA2 SA3 ON OS NS0 NS1 NS8 NS9 WB ABND AL1 OTs OTi ONs ONi OSs OSi OPs OPi; lia|].
        all: split; [clear -NEV CEIL LO OT OP AHI0 SA1 SA2 SA3 ON OS NS0 NS1 NS8 NS9 WB ABND AL1 OTs OTi ONs ONi OSs OSi OPs OPi; lia|].
        all: split; [clear -NEV CEIL LO OT OP AHI0 SA1 SA2 SA3 ON OS NS0 NS1 NS8 NS9 WB ABND AL1 OTs OTi ONs ONi OSs OSi OPs OPi; lia|].
        all: intros b Hb; destruct (BB b Hb) as [B1 B2]; destruct (xb_st b); [exact I| |];
          clear -NEV B1 B2 CEIL LO OT OP ORS AHI0 SA1 SA2 SA3 SR1 ON OS D_t_res D_p_res C_r D_n_res D_s_res NS0 NS1 NS8 NS9 WB ABND AL1 RHI OTs OTi ONs ONi OSs OSi OPs OPi; lia.
      - unfold quar_same. subst st2. rewrite E9, E10, E11, E12, E1. repeat (split; [reflexivity|]).
        split; intros b Hb; destruct (xb_st b); first [exact I | exact Hb]. }
    split. {
      unfold AHS, AH. cbn [ah_sec]. subst st2.
      pose proof (valid_buf RESV st n a FRSH) as VB. fold ms in VB.
      pose proof (WT_kinds L sp lo a ms _ _ _ WTF (sec_chunks_of st) st n VW) as VWK. fold W' in VWK.
      eapply (asec_append L W' m m' MU WM st X nres' a n id WF HS0 N PRIM VW VK NR' NRB VB VWK).
      - intros ch Hin. destruct (asec_wf_all L st _ ch WFS Hin) as (mb & ms' & n' & -> & W1c). cbn [sec_mb sec_ms].
        pose proof W1c as W0. cbn [sec_wf1] in W0. destruct W0 as (G1 & G2 & G3 & G4 & G5 & G6 & (Ct & Cc & Cr & Cp & Cn & Cs & Cf & Cd)).
        pose proof (proj1 (Forall_forall _ _) VK _ Hin) as D. cbn [sec_mb sec_ms] in D.
        pose proof (sec_facts n' ltac:(clear -G5; lia) G6) as (_ & _ & _ & _ & _ & _ & _ & _ & MSM' & MSB'). rewrite <- G4 in MSM', MSB'.
        destruct (ablk_int _ _ G2) as [kB GB].
        assert (SHc : 0x800bde00 <= shad mb /\ shad mb + ms' / 8 = shad (mb + ms') /\ shad (mb + ms') <= 0x10007fef8000
                      /\ (shad (mb + ms') <= shad a \/ shad (a + ms) <= shad mb)).
        { rewrite !shad_div. unfold ASHOFF, K_HIGH_MEM in *. clear -G1 GB G3 MSM' D AAL MSM. Z.div_mod_to_equations. lia. }
        destruct SHc as (SC1 & SC2 & SC3 & SC4). unfold K_HIGH_MEM in *.
        split; intros A k H1 H2 H3.
        + apply Kobj; clear -H1 H2 H3 GB G3 Ct Cp Cn Cs D; lia.
        + apply Kshad; clear -H1 H2 H3 SC1 SC2 SC3 SC4; lia.
      - intros POS. apply KX; [clear -POS; lia|]. intros iv Hiv NEV. inWT Hiv; unfold AIMG_HI, AINSTANCE in *;
          clear -POS NEV CEIL LO OT OP AHI0 ON OS SA2 SA3 D_t_p C_p D_n_p D_s_p NS0 NS1 NS8 NS9 WB ABND AL1 SA1 OTs OTi ONs ONi OSs OSi OPs OPi; lia.
      - intros LT. apply KX; [clear -LT NS0; lia|]. intros iv Hiv NEV. inWT Hiv; unfold AIMG_HI, AINSTANCE in *;
          clear -LT NEV CEIL LO OT OP AHI0 ON OS SA2 SA3 D_t_p C_p D_n_p D_s_p NS0 NS1 NS8 NS9 WB ABND AL1 SA1 OTs OTi ONs ONi OSs OSi OPs OPi; lia.
      - apply Kimg; clear; unfold AIMG_HI, AINSTANCE; lia.
      - replace (shlen K_REGION) with 536870912 by reflexivity.
        apply Kres_sh; [apply shad_mono; clear -RSP; lia| clear; lia|].
        rewrite !shad_div. clear -RSP. Z.div_mod_to_equations. lia.
      - intros x Hx Hxa. unfold K_HIGH_MEM, KLS in Hx. unfold AIMG_HI in Hx.
        assert (SX : 2147446784 <= shad x /\ shad x + 1 <= 17594333495296) by (rewrite shad_div; unfold ASHOFF; clear -Hx; Z.div_mod_to_equations; lia).
        apply Kshad; [clear -SX; lia| clear; lia| clear -SX; lia|].
        destruct Hxa as [Hxa|Hxa]; [left; apply SAlt; exact Hxa| right; apply SAge; exact Hxa].
      - exact I128. - exact J136. - exact J168. - exact I680. - exact J704. - exact SLOT. - exact HDR. - exact PGJ. - exact MAG. - exact LCJ.
      - exact AHD. - exact IDR. - exact USR. - exact SHF. - exact SHU. - exact SHT. }
    split; [exact DEP|].
    split; [eapply arelro_frame; [exact MU | exact HRO | apply Kimg; clear; unfold ARELRO_LO, ARELRO_HI, AIMG_HI, AINSTANCE; lia]|].
    split; [eapply arep_rt2_frame; [exact MU | exact WM | exact RT2 | | |]; apply Kimg; clear; unfold AIMG_HI, AINSTANCE; lia|].
    split; [| eapply arep_rt3_frame; [exact MU | exact WM | exact RT3 |]; unfold rt3_hulls;
              repeat (apply Forall_cons; [cbn [fst snd]; apply Kimg; clear; unfold AIMG_HI, AINSTANCE; lia |]); apply Forall_nil].
    intros c Hc. destruct (PERC c Hc) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & _). unfold K_NUM_CLASSES in Hc.
    assert (RI : al_res L <= aregion L c /\ aregion L c + K_REGION <= al_space_beg L + K_SPACE_SIZE
                 /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104).
    { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc RSP. lia. }
    destruct RI as (RI1 & RI2 & RI3). unfold K_REGION, K_SPACE_SIZE in RI2, RI3. change (2^37) with 137438953472 in RI2, RI3.
    eapply (ashadow_avail_frame L W' m m' MU WM st); [exact (AVL c ltac:(unfold K_NUM_CLASSES; clear -Hc; lia)) | subst st2; reflexivity | subst st2; reflexivity | |].
    - intros POS. apply Kres_sh; [apply shad_mono; unfold aregion in *; clear -Q1 RI1; lia | clear -POS; lia |].
      rewrite <- shad_add_shlen by (pose proof (aregion_mod L c SAL) as RM; clear -RM Q4; unfold K_USER_MAP in *; Z.div_mod_to_equations; lia).
      apply shad_mono. unfold K_FREEARR_OFF, K_REGION in *. clear -Q1 Q2 RI2 RI3. lia.
    - intros POS. apply Kres_sh; [apply shad_mono; unfold afreearr, K_FREEARR_OFF, aregion in *; clear -Q5 Q6 RI1; lia | clear -POS; lia |].
      rewrite <- shad_add_shlen by (pose proof (aregion_mod L c SAL) as RM; unfold afreearr, K_FREEARR_OFF; clear -RM Q7; unfold K_FREEARR_MAP in *; Z.div_mod_to_equations; lia).
      apply shad_mono. unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -Q5 Q6 RI2 RI3. lia. }

  assert (SHFK : 0x800bde00 <= shad (al_fake L) /\ shad (al_fake L) + shlen 11571200 = shad (al_fake L + 11571200)
                 /\ shad (al_fake L + 11571200) <= 0x10007fef8000
                 /\ (shad (a + ms) <= shad (al_fake L) \/ shad (al_fake L + 11571200) <= shad a)).
  { rewrite !shad_div, shlen_div. unfold ASHOFF in *. clear -OFK C_f AAL OFKs OFKi. Z.div_mod_to_equations. lia. }
  destruct SHFK as (SF1 & SF2 & SF3 & SF4).
  assert (FKD : forall cls FA sz, In (mkABlock (ABFake cls) FA sz) LB -> al_fake L <= FA /\ 0 <= sz /\ FA + sz <= al_fake L + 11571200)
    by (intros cls FA sz Hin; exact (proj1 (proj2 BL) cls FA sz Hin)).
  split.
  -
    intros x Hx CL. split; [| intros Hw; apply WM; exact Hw]. apply MU. rewrite wa_unsigned by exact Hx.
    destruct CL as [STa | [CIa | [BLK | SH]]].
    + eapply (disjoint_outside W' x 1); [| clear; lia]. apply KX; [clear; lia|]. intros iv Hiv NEV. inWT Hiv; unfold AIMG_HI, AINSTANCE in *;
        clear -STa NEV CEIL LO OT OP AHI0 ACE ON OS SA2 SA3 NS0 NS1 NS8 NS9 WB SP47 ABND AL1 SA1 OTs OTi ONs ONi OSs OSi OPs OPi; lia.
    + destruct CIa as (iv & Hiv & R). pose proof (proj1 (Forall_forall _ _) CI_OK iv Hiv) as (Q1 & Q2 & Q3).
      pose proof (proj1 (Forall_forall _ _) CI_OK2 iv Hiv) as Q4. cbn [fst snd] in *.
      eapply disjoint_outside; [eapply (Kimg x 1); unfold AIMG_HI, AINSTANCE in *; clear -R Q1 Q2 Q3 Q4; lia | clear; lia].
    + destruct BLK as (b & Hb & R). destruct b as [[p|cls] A n']; cbn [ab_addr ab_size] in R.
      * destruct (proj1 BL p A n' Hb) as [(xb & Hxb & Sb & Ub & Nb)|(mb0 & ms0 & Lp & EUA & Gs)].
        -- destruct (BB xb Hxb) as [Bb1 Bb2].
           pose proof (awf_fits L st X xb WF Hxb) as FIT. unfold xb_fits in FIT. rewrite Sb in FIT. unfold xb_user in Ub. subst A n'.
           eapply disjoint_outside; [eapply (Kres x 1) | clear; lia]; clear -R Bb1 Bb2 FIT; lia.
        --
           assert (Hin : In (CSec mb0 ms0 n') (sec_chunks_of st)).
           { unfold sec_chunks_of, achunks. apply List.filter_In. split; [| reflexivity]. apply in_app_iff. left.
             apply in_map_iff. exists (p, CSec mb0 ms0 n'). split; [reflexivity|]. apply list_elem_of_In. apply elem_of_map_to_list. exact Lp. }
           pose proof (proj1 (Forall_forall _ _) VK _ Hin) as D. cbn [sec_mb sec_ms] in D.
           cbn [sec_wf1] in Gs. destruct Gs as (Gs1 & Gs2 & Gs3 & Gs4 & Gs5 & Gs6 & (Ct & Cc & Cr & Cp & Cn & Cs & Cf & Cd)).
           pose proof (sec_facts n' ltac:(clear -Gs5; lia) Gs6) as SFc. subst A. unfold SEC_UOFF, K_HIGH_MEM in *.
           destruct (ablk_int _ _ Gs2) as [kB GB].
           eapply disjoint_outside; [eapply (Kobj x 1) | clear; lia]; clear -R GB Gs3 Gs4 Gs5 SFc Ct Cp Cn Cs D; lia.
      * destruct (FKD cls A n' Hb) as (K1 & K2 & K3). atop_facts.
        eapply disjoint_outside; [eapply (Kobj x 1) | clear; lia]; clear -R K1 K3 OFK D_t_f D_f_p C_f D_n_f D_s_f OFKs OFKi; lia.
    + destruct SH as (x' & Hx' & ->).
      destruct Hx' as [STa | [CIa | FK]].
      * assert (SX : shad (a + ms) <= shad x' /\ shad x' + 1 <= 17594333495296).
        { split; [apply SAge; atop_facts; clear -STa ACE; lia|]. rewrite shad_div. unfold ASHOFF. clear -STa. Z.div_mod_to_equations. lia. }
        eapply disjoint_outside; [eapply (Kshad (shad x') 1); clear -SX SA1 SA2 MSB; lia | clear; lia].
      * destruct CIa as (iv & Hiv & R). pose proof (proj1 (Forall_forall _ _) CI_OK iv Hiv) as (Q1 & Q2 & Q3). cbn [fst snd] in *.
        assert (SX : 2147446784 <= shad x' /\ shad x' + 1 <= 0x800bde00) by (rewrite shad_div; unfold ASHOFF, AIMG_HI in *; clear -R Q1 Q3; Z.div_mod_to_equations; lia).
        eapply disjoint_outside; [eapply (Kshad (shad x') 1); clear -SX SA1; lia | clear; lia].
      * destruct FK as (cls & FA & sz & Hin & R). destruct (FKD cls FA sz Hin) as (K1 & K2 & K3).
        assert (SX : shad (al_fake L) <= shad x' /\ shad x' + 1 <= shad (al_fake L + 11571200)).
        { rewrite !shad_div. clear -R K1 K3 OFK OFKs OFKi. Z.div_mod_to_equations. lia. }
        eapply disjoint_outside; [eapply (Kshad (shad x') 1) | clear; lia]; clear -SX SF1 SF3 SF4; lia.
  -
    split; [exact ALO|].
    split; [eapply (arng_sec L RNG RNG' st X); [exact WF| exact ARNG| exact FPLE| exact RA| exact RSA| exact RPA']|].
    split; [exists X; split; [exact AR'| replace (a + 6144) with (a + SEC_UOFF) by reflexivity; apply ablocks_sec; [exact WF| exact BL| exact VW]]|].
    unfold AHS, AH. cbn [ah_fake].
    eapply (hf_blocks _ HL L LB); [eapply (hf_frame _ HL L LB m m'); [exact HFK | exact MU | exact WM | apply Kt; clear; lia |] |].
    + unfold fake_untouched. apply Forall_forall. intros iv Hin.
      unfold W' in Hin. apply List.filter_In in Hin. destruct Hin as [Hin NEV]. unfold nonempty in NEV. apply Z.ltb_lt in NEV.
      inWT Hin. all: unfold AINSTANCE in *.
      all: clear -NEV CEIL LO OT OP OFK OD AHI0 ACE SA1 SA2 SA3 SF1 SF2 SF3 SF4 ON OS D_t_f D_t_d D_f_p D_d_p C_f C_d D_n_f D_s_f D_n_d D_s_d NS0 NS1 NS8 NS9 WB ABND AL1 OTs OTi ONs ONi OSs OSi OPs OPi OFKs OFKi ODs ODi.

      all: first [ lazymatch goal with
                   | |- context [al_t _] => clear D_f_p D_d_p C_f C_d D_n_f D_s_f D_n_d D_s_d
                   | |- context [al_ptr_array _] => clear D_t_f D_t_d C_f C_d D_n_f D_s_f D_n_d D_s_d
                   | |- context [al_nodes _] => clear D_t_f D_t_d D_f_p D_d_p C_f C_d D_s_f D_s_d
                   | |- context [al_store _] => clear D_t_f D_t_d D_f_p D_d_p C_f C_d D_n_f D_n_d
                   | |- _ => clear D_t_f D_t_d D_f_p D_d_p D_n_f D_s_f D_n_d D_s_d
                   end; repeat (split; [lia|]); lia
                 | repeat (split; [lia|]); lia ].
    + intros c F n'. split; [intros H; cbn [In] in H; destruct H as [H|H]; [discriminate H| exact H]| intros H; cbn [In]; right; exact H].
Qed.
End Store.
End CANSEC1.
End ASecStore.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require BImg.
Module TwinB.
Import stdpp.gmap.

Module ASF_kit.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ITreeA.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW.BImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABytes.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARep.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepFrame.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ALayout.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AHeapP.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ASecFacts.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ASec.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ASecFrame.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKitQ.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepQ.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepQP.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepKit.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepExt.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFreeModel.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFreeRep.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFrameD.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.FsKit.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_iface.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AExh.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AC6Frame.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT} {ov : annOV} {gb : GcBit}.
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

Lemma live_in_achunks : forall st (p : aptr) ch, (a_live st) !! p = Some ch -> In ch (achunks st).
Proof.
  intros st p ch L. unfold achunks. apply in_or_app. left.
  pose proof (map_to_list_delete (a_live st) p ch L) as P.
  apply (Permutation_map snd) in P. cbn [map snd] in P. eapply Permutation_in; [exact P| left; reflexivity].
Qed.
Lemma live_sec_in : forall st (p : aptr) mb ms n, (a_live st) !! p = Some (CSec mb ms n) -> In (CSec mb ms n) (sec_chunks_of st).
Proof. intros st p mb ms n L. unfold sec_chunks_of. apply List.filter_In. split; [eapply live_in_achunks; exact L| reflexivity]. Qed.

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

Lemma sec_chunks_of_quar_sec : forall s s' mb ms n,
  a_live s' = a_live s ->
  Permutation (qfilt is_sec s') (CSec mb ms n :: qfilt is_sec s) ->
  Permutation (sec_chunks_of s') (CSec mb ms n :: sec_chunks_of s).
Proof.
  intros s s' mb ms n EL PQ. unfold sec_chunks_of, achunks. rewrite EL, !filter_is_sec_app. unfold qfilt in PQ.
  eapply Permutation_trans; [apply Permutation_app_head; exact PQ|]. apply Permutation_sym. apply Permutation_middle.
Qed.

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

Lemma no_busy_live_sec : forall L st X (p : aptr) mb ms n y,
  awf L st X -> (a_live st) !! p = Some (CSec mb ms n) -> In y (x_busy X) -> xb_st y <> BLive p.
Proof.
  intros L st X p mb ms n y WF LIVE Hy E. destruct WF as (_ & _ & _ & _ & _ & _ & _ & BUSY & _).
  destruct (BUSY y Hy) as [_ M]. rewrite E in M. destruct M as (_ & _ & _ & _ & _ & M6). rewrite LIVE in M6. discriminate.
Qed.

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

Lemma sec_not_live_after : forall L st cs (p : aptr) mb ms n s,
  asec_wf L st cs -> Permutation cs (sec_chunks_of st) ->
  (a_live st) !! p = Some (CSec mb ms n) -> a_live s = delete p (a_live st) ->
  ~ sec_live s (CSec mb ms n).
Proof.
  intros L st cs p mb ms n s WFS PC LIVE EL [q Hq]. rewrite EL in Hq.
  apply lookup_delete_Some in Hq. destruct Hq as [NE Hq].
  destruct WFS as (_ & _ & _ & _ & _ & _ & [ND _]).

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

Lemma sec_live_other : forall st (p : aptr) mb ms n s ch,
  (a_live st) !! p = Some (CSec mb ms n) -> a_live s = delete p (a_live st) -> ch <> CSec mb ms n ->
  (sec_live s ch <-> sec_live st ch).
Proof.
  intros st p mb ms n s ch LIVE EL NE. unfold sec_live. rewrite EL. split; intros [q Hq].
  - apply lookup_delete_Some in Hq. destruct Hq as [_ Hq]. exists q. exact Hq.
  - exists q. rewrite lookup_delete_ne; [exact Hq|]. intros ->. apply NE. pose proof (eq_trans (eq_sym Hq) LIVE) as XX. injection XX as <-. reflexivity.
Qed.

Lemma sec_wf1_facts' : forall L mb ms n, sec_wf1 L (CSec mb ms n) ->
     mb mod 4096 = 0 /\ ablk mb (mb + ms) /\ mb + ms <= ATOP /\ ms = sec_map_size n /\ 64512 < n <= AREQMAX
  /\ rz_size n = 2048 /\ 73728 <= ms <= 4293926912 /\ ms mod 4096 = 0 /\ needed_size n + 4096 <= ms /\ 0 <= needed_size n
  /\ sec_clear L mb ms /\ is_primary n = false /\ n + 6144 <= needed_size n + 4096.
Proof.
  intros L mb ms n W. pose proof W as W0. destruct W0 as (MAL & MLO & MCE & MSE & NB & NPR & SCL).
  pose proof (sec_facts n ltac:(lia) NPR) as (_ & RZ & _ & RS1 & _ & NS & MS & MSB & MSAL & MSR). rewrite <- MSE in MSB, MSAL, MSR.
  unfold AREQMAX in *.
  repeat (lazymatch goal with |- _ /\ _ => split end); first [assumption| reflexivity| lia].
Qed.

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
  intros cs L st X m p mb ms n (WFS & ARR & INST & PZ & SHZ & AXH) PC LIVE hm.
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

Definition sec_same0 (st st' : astate) : Prop :=
     a_nsec st' = a_nsec st /\ a_nres st' = a_nres st /\ a_ptr_array st' = a_ptr_array st
  /\ (forall ch, is_sec ch = true -> (sec_live st' ch <-> sec_live st ch))
  /\ a_emb st' = a_emb st /\ a_exh st' = a_exh st.

Lemma asecc_frame : forall cs L W m m' st st' X X',
  ASECc cs L st X m -> munch W m m' -> wmono bsegs m m' -> sec_untouched L W -> c6_untouched L W -> sec_same0 st st' ->
  ASECc cs L st' X' m'.
Proof.
  intros cs L W0 m m' st st' X X' (WFS & ARR & INST & PZ & SHZ & AXH) MU0 WM SU0 C60 (EN & ER & EP & EL & EEMB & EEXH).
  pose proof WFS as (ALO & WP & WR & WL & WB & WF1 & WD).
  pose proof (munch_filter_nonempty W0 m m' MU0) as MU. pose proof (sec_untouched_filter L W0 SU0) as SU. pose proof (nonempty_filter W0) as NE.
  set (W := List.filter nonempty W0) in MU, SU, NE.
  assert (ALLSEC : forall ch, In ch cs -> exists mb ms n, ch = CSec mb ms n /\ sec_wf1 L (CSec mb ms n)).
  { intros ch Hin. pose proof (proj1 (Forall_forall _ _) WF1 ch Hin) as W1. destruct ch as [c n|mb ms n]; [destruct W1|].
    exists mb, ms, n. split; [reflexivity| exact W1]. }
  split; [| split; [| split; [| split; [| split]]]].
  6: exact (aexh_frame cs L st st' m m' W0 AXH MU0 SU0 C60 EEMB EEXH).
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
    assert (SX : 0 <= shad x < 2^64) by (pose proof atop_range as ATR; rewrite shad_div; unfold ASHOFF, K_HIGH_MEM, AIMG_HI, KLS in *; clear -Hx ATR; Z.div_mod_to_equations; lia).
    rewrite <- (SHZ x Hx HF HC). apply MU. rewrite wa_unsigned by exact SX.
    eapply (disjoint_outside W (shad x) 1); [| clear; lia].
    apply (su_disjoint L); [exact SU| exact NE| clear; lia|]. intros a Ha K. apply (clear_free_shadow L ALO x Hx HF). replace (shad x) with a by (clear -Ha; lia). exact K.
Qed.

Definition depot_frameD_law (AD : alayout -> amem -> Prop) : Prop :=
  forall L m m' W, AD L m -> munch W m m' ->
    Forall (fun iv => forall a, fst iv <= a < snd iv ->
              ~ (0x1adb48 <= a < 0x5fdb90) /\ ~ (al_nodes L <= a < al_nodes L + 1048576) /\ ~ (al_store L <= a < al_store L + 8388608)) W ->
    AD L m'.

Definition fake_frameD_law (AFK : alayout -> list ablock -> amem -> Prop) : Prop :=
  forall L LB m m' W, AFK L LB m -> munch W m m' -> disjoint_from W (al_t L + 72) 8 -> fake_untouched L W ->
    Forall (fun iv => snd iv <= al_t L + 48 \/ al_t L + 64 <= fst iv) W -> AFK L LB m'.

Lemma dc_at_frameD : forall W m m' A n, dc_at m A n -> munch W m m' -> (0 < n -> disjoint_from W A n) -> dc_at m' A n.
Proof. intros W m m' A n H MU D. exact (junk_frameD W m m' A n H MU D). Qed.

Lemma afake_frameD : fake_frameD_law AFAKE.
Proof.
  intros L LB m m' W (G & CE & (h0 & h1 & h2 & hs & HS) & LOG & NGC & DC1 & DC2 & FL & LV & TFSC) MU D7 UT UT2.
  pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11). unfold FAKESZ in *. pose proof (ablk_lin _ _ G2) as (GL1 & GL2 & GL3 & GL4).
  assert (DF : disjoint_from W (al_fake L) 11571200) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9); exact X1).
  assert (DS : disjoint_from W (shad (al_fake L)) (shlen 11571200)) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9); exact X2).
  assert (DD : disjoint_from W (al_dtls L) 4096) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9); exact X3).
  assert (D1 : disjoint_from W 0xd5470 8) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9); exact X4).
  assert (D2 : disjoint_from W 0x60ee38 16) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9); exact X5).
  assert (D3 : disjoint_from W 0x60ee48 8) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9); exact X6).
  assert (D4 : disjoint_from W 0x60ee68 8) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9); exact X7).
  assert (D5 : disjoint_from W 0x16d831 1) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9); exact X8).
  assert (D6 : disjoint_from W 0x16b718 4) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9); exact X9).
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
  - split; [| eapply rw_cells_transportD; [exact TFSC| exact MU| cbn [cells_size csize Nat.add]; exact D7]].
    intros c F n Hin. destruct (LV c F n Hin) as (Hc & Hn & pos & Hp & HF & Hb). split; [exact Hc|]. split; [exact Hn|].
    exists pos. split; [exact Hp|]. split; [exact HF|]. pose proof (fk_flag_range L c pos Hc Hp).
    rewrite (munch_outside_range W m m' (al_fake L) 11571200) by (assumption || lia). exact Hb.
Qed.

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

End ASF_kit.

Module ASecStore.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ITreeA.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW.BImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABytes.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARep.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepKit.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepFrame.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ALayout.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AHeapP.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKitQ.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AMalloc_iface.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ADepot_iface.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ASec.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ASecFacts.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ASecFrame.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ASecModel.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AModelFacts.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.APrimFacts.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_amalloc_arep.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepExt.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AExh.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AC6U.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AC6Frame.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT} {ov : annOV}.
Lemma sec_chunk_in_ranges : forall st mb ms n, In (CSec mb ms n) (sec_chunks_of st) -> In (mb, mb + ms) (asec_ranges st).
Proof.
  intros st mb ms n H. unfold sec_chunks_of in H. apply List.filter_In in H. destruct H as [H _].
  unfold asec_ranges. apply in_or_app. left. apply in_flat_map. exists (CSec mb ms n). split; [exact H| left; reflexivity].
Qed.

Lemma avoids_all_In : forall a n l iv, avoids_all a n l = true -> In iv l -> a + n <= fst iv \/ snd iv <= a.
Proof.
  intros a n l iv H Hin. unfold avoids_all in H. rewrite forallb_forall in H. specialize (H iv Hin).
  unfold iv_clear in H. apply orb_prop in H. destruct H as [H|H]; apply Z.leb_le in H; lia.
Qed.

Lemma asec_wf_all : forall L st cs ch, asec_wf L st cs -> In ch cs -> exists mb ms n, ch = CSec mb ms n /\ sec_wf1 L (CSec mb ms n).
Proof.
  intros L st cs ch (_ & _ & _ & _ & _ & WF1 & _) Hin. pose proof (proj1 (Forall_forall _ _) WF1 ch Hin) as W1.
  destruct ch as [c n|mb ms n]; [destruct W1|]. exists mb, ms, n. split; [reflexivity| exact W1].
Qed.

Section Valid.
Variables (L : alayout) (RESV : list (Z * Z)) (st : astate) (n a : Z).
Let ms := sec_map_size n.
Hypothesis ALO : alayout_ok L.
Hypothesis N : 1 <= n <= AREQMAX.
Hypothesis PRIM : is_primary n = false.
Hypothesis FR : sfresh RESV st n a = true.
Hypothesis ROK : aresv_ok L RESV.

Lemma valid_geo : a mod 4096 = 0 /\ ablk a (a + ms) /\ a + ms <= ATOP /\ 0 < ms /\ ms = sec_map_size n.
Proof.
  destruct (sfresh_true_facts RESV st n a FR) as (_ & _ & AV & _ & POS & AL & TOPB & _).
  pose proof (sec_facts n N PRIM) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & MSB).
  destruct ROK as (R1 & R2 & _).
  pose proof (pcov_clear _ _ _ _ _ R1 AV ltac:(unfold AIMG_HI; clear; lia) ltac:(clear -MSB; lia)) as C1.
  pose proof (pcov_clear _ _ _ _ _ R2 AV ltac:(clear; lia) ltac:(clear -MSB; lia)) as C2.
  subst ms. split; [exact AL|]. split; [| split; [exact TOPB| split; [clear -MSB; lia| reflexivity]]].
  unfold ablk, KLS. unfold AIMG_HI in *. clear -C1 C2 POS TOPB MSB. lia.
Qed.

Lemma valid_hulls : Forall (fun iv => a + ms <= fst iv \/ snd iv <= a) (astartup_hulls L).
Proof.
  destruct (sfresh_true_facts RESV st n a FR) as (_ & _ & AV & _ & _ & _ & _ & _).
  pose proof valid_geo as (_ & _ & _ & MSP & _).
  destruct ROK as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15).
  unfold astartup_hulls. fold (al_res L) in R3. change (4096 * al_V L 323%nat) with (al_dtls L) in R10.
  repeat (apply Forall_cons; [cbn [fst snd]; eapply pcov_clear; [eassumption| exact AV| clear; lia| exact MSP] |]). apply Forall_nil.
Qed.

Lemma valid_clear : sec_clear L a ms.
Proof.
  pose proof valid_hulls as H. unfold astartup_hulls in H.
  repeat lazymatch type of H with Forall _ (_ :: _) => apply Forall_cons_iff in H; destruct H as [? H] | _ => idtac end.
  cbn [fst snd] in *. unfold sec_clear. repeat split; lia.
Qed.

Lemma valid_chunks : Forall (fun ch => a + ms <= sec_mb ch \/ sec_mb ch + sec_ms ch <= a) (sec_chunks_of st).
Proof.
  destruct (sfresh_true_facts RESV st n a FR) as (_ & _ & _ & AV & _ & _ & _ & _).
  apply Forall_forall. intros ch Hin. destruct ch as [c k|mb ms' k]; cbn [sec_mb sec_ms].
  - pose proof valid_geo as (_ & G & _). pose proof (ablk_lin _ _ G) as (_ & G0 & _). right. clear -G0. lia.
  - pose proof (avoids_all_In _ _ _ _ AV (sec_chunk_in_ranges st mb ms' k Hin)) as D. cbn [fst snd] in D. exact D.
Qed.

Lemma valid_buf : let '(d, cap, _) := a_emb st in cap = 0 \/ avoids_all d cap (sec_iv (CSec a ms n)) = true.
Proof.
  destruct (sfresh_true_facts RESV st n a FR) as (_ & _ & _ & AV & _ & _ & _ & _). fold ms in AV.
  destruct (a_emb st) as [[d cap] sz] eqn:EA. destruct (Z.eqb_spec cap 0) as [E0|NZ]; [left; exact E0| right].
  assert (Hin : In (d, d + cap) (asec_ranges st)).
  { unfold asec_ranges. apply in_or_app. right. unfold emb_iv. rewrite EA. destruct (Z.eqb_spec cap 0) as [E0|_]; [exact (False_ind _ (NZ E0))| left; reflexivity]. }
  pose proof (avoids_all_In _ _ _ _ AV Hin) as D. cbn [fst snd] in D.
  cbn [sec_iv]. unfold avoids_all. cbn [forallb]. unfold iv_clear. cbn [fst snd]. rewrite andb_true_r. apply orb_true_iff.
  destruct D as [D|D]; [right; apply Z.leb_le; lia| left; apply Z.leb_le; lia].
Qed.

Lemma valid_wf1 : sec_wf1 L (CSec a ms n).
Proof.
  pose proof valid_geo as (G1 & G2 & G3 & G4 & G5). pose proof (sec_facts n N PRIM) as (NB & _).
  cbn [sec_wf1]. split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. split; [exact G5|].
  split; [lia|]. split; [exact PRIM| exact valid_clear].
Qed.
End Valid.

Lemma wview_some : forall m (x : word) b, m x = Some b -> wview bsegs m x = Some b.
Proof. intros m x b H. unfold wview. rewrite H. reflexivity. Qed.

Lemma ashz_azero : forall L cs m a ms,
  ashz L cs m ->
  a mod 8 = 0 -> ablk a (a + ms) -> a + ms <= ATOP -> 0 <= ms ->
  Forall (fun iv => a + ms <= fst iv \/ snd iv <= a) (astartup_hulls L) ->
  Forall (fun ch => a + ms <= sec_mb ch \/ sec_mb ch + sec_ms ch <= a) cs ->
  azero m (shad a) (ms / 8).
Proof.
  intros L cs m a ms SHZ A8 ALO AHI MS0 HH HC.
  assert (PT : forall i, 0 <= i < ms / 8 -> m (wa (shad a + i)) = Some (Z_to_bv 8 0)).
  { intros i Hi. replace (shad a + i) with (shad (a + 8 * i)) by (rewrite !shad_div; clear -A8; Z.div_mod_to_equations; lia).
    apply SHZ.
    - unfold ablk, KLS, K_HIGH_MEM in *. unfold AIMG_HI in *. clear -Hi ALO AHI A8. Z.div_mod_to_equations. lia.
    - eapply Forall_impl; [| exact HH]. cbn beta. intros iv Hiv. clear -Hi Hiv A8. Z.div_mod_to_equations. lia.
    - eapply Forall_impl; [| exact HC]. cbn beta. intros ch Hch. clear -Hi Hch A8. Z.div_mod_to_equations. lia. }
  assert (SR : 0 <= shad a /\ shad a + ms / 8 <= 2^64).
  { pose proof (ablk_lin _ _ ALO) as (AL1 & AL2 & AL3 & AL4). rewrite shad_div. unfold ASHOFF in *. clear -AL2 AL4 AHI MS0. Z.div_mod_to_equations. lia. }
  split; [exact PT|]. split; [lia|]. split; [lia|]. intros i Hi. rewrite (wview_some _ _ _ (PT i Hi)). discriminate.
Qed.

Lemma filter_is_sec_perm : forall (l l' : list achunk), Permutation l l' -> Permutation (List.filter is_sec l) (List.filter is_sec l').
Proof.
  intros l l' HP. induction HP; cbn; [constructor| | |].
  - destruct (is_sec x); [apply perm_skip|]; assumption.
  - destruct (is_sec x), (is_sec y); try apply perm_swap; try apply perm_skip; try apply Permutation_refl.
  - eapply Permutation_trans; eassumption.
Qed.

Lemma sec_chunks_of_insert_sec : forall st st' p mb ms n,
  (a_live st) !! p = None ->
  a_live st' = <[p := CSec mb ms n]> (a_live st) -> a_qloc st' = a_qloc st -> a_qglob st' = a_qglob st ->
  Permutation (sec_chunks_of st') (CSec mb ms n :: sec_chunks_of st).
Proof.
  intros st st' p mb ms n NONE E1 E2 E3. unfold sec_chunks_of, achunks. rewrite E1, E2, E3, !filter_is_sec_app.
  change (CSec mb ms n :: List.filter is_sec (map snd (map_to_list (a_live st))) ++ List.filter is_sec (flat_map b_chunks (a_qloc st ++ a_qglob st)))
    with ((CSec mb ms n :: List.filter is_sec (map snd (map_to_list (a_live st)))) ++ List.filter is_sec (flat_map b_chunks (a_qloc st ++ a_qglob st))).
  apply Permutation_app_tail.
  pose proof (map_to_list_insert (a_live st) p (CSec mb ms n) NONE) as P.
  apply (Permutation_map snd) in P. cbn [map snd] in P.
  eapply Permutation_trans; [apply filter_is_sec_perm; exact P|]. cbn. apply Permutation_refl.
Qed.

Lemma awf_fresh_none : forall L st X, awf L st X -> (a_live st) !! (a_next st) = None.
Proof.
  intros L st X WF. destruct WF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & FRESH & _).
  destruct ((a_live st) !! (a_next st)) as [ch|] eqn:E; [| reflexivity]. exfalso. pose proof (FRESH _ _ E) as F. clear -F. lia.
Qed.

Lemma awf_sec : forall L st X nres' a ms n, awf L st X -> awf L (st_sec st nres' a ms n) X.
Proof.
  intros L st X nres' a ms n WF.
  pose proof (awf_fresh_none L st X WF) as NONE.
  pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVE & FRESH & UNIQ).
  pose proof (st_sec_fields st nres' a ms n) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12).
  unfold awf. rewrite E1, E2, E7, E8.
  split; [exact SBE|]. split; [exact PAE|]. split; [exact SAL|]. split; [exact SLO|]. split; [exact SHI|].
  split. { intros c Hc. rewrite get_cls_st_sec, max_count_st_sec. unfold ndist. rewrite get_cls_st_sec. exact (PERC c Hc). }
  split. { intros c Hc. rewrite get_cls_st_sec. exact (OUTC c Hc). }
  split. { intros b Hb. destruct (BUSY b Hb) as [CLB M]. split; [exact CLB|]. destruct (xb_st b) as [p| |]; try exact M.
           destruct M as (M1 & M2 & M3 & M4 & M5 & M6). repeat (split; [assumption|]).
           rewrite lookup_insert_ne; [exact M6|]. intros E. assert (X0 : a_live st !! p = None) by (rewrite <- E; exact NONE). rewrite X0 in M6. discriminate. }
  split. { intros p c k Hp. destruct (N.eq_dec p (a_next st)) as [->|NE].
           - rewrite lookup_insert_eq in Hp. discriminate.
           - rewrite lookup_insert_ne in Hp by (intros E; apply NE; symmetry; exact E). exact (LIVE p c k Hp). }
  split. { intros p ch Hp. destruct (N.eq_dec p (a_next st)) as [->|NE]; [lia|].
           rewrite lookup_insert_ne in Hp by (intros E; apply NE; symmetry; exact E). pose proof (FRESH p ch Hp). lia. }
  exact UNIQ.
Qed.

Lemma ablocks_sec : forall L st X LB nres' a ms n,
  awf L st X -> ablocks L st X LB -> sec_wf1 L (CSec a ms n) ->
  ablocks L (st_sec st nres' a ms n) X (HB (a_next st) (a + SEC_UOFF) n :: LB).
Proof.
  intros L st X LB nres' a ms n WF (BH & BF & NDI & NDL) W1.
  pose proof (awf_fresh_none L st X WF) as NONE.
  destruct WF as (_ & _ & _ & _ & _ & _ & _ & BUSY & _ & FRESH & _).
  pose proof (st_sec_fields st nres' a ms n) as (_ & _ & _ & _ & _ & _ & E7 & _).
  assert (OLD : forall p A n', In (HB p A n') LB -> (p < a_next st)%N).
  { intros p A n' Hin. destruct (BH p A n' Hin) as [(b & Hb & Sb & _)|(mb & ms' & Lp & _)].
    - destruct (BUSY b Hb) as [_ M]. rewrite Sb in M. destruct M as (_ & _ & _ & _ & _ & M5). exact (FRESH _ _ M5).
    - exact (FRESH _ _ Lp). }
  split; [| split; [| split]].
  - intros p A n' [E|Hin].
    + injection E as <- <- <-. right. exists a, ms. rewrite E7, lookup_insert_eq. split; [reflexivity|]. split; [reflexivity| exact W1].
    + destruct (BH p A n' Hin) as [(b & Hb & R)|(mb & ms' & Lp & R)].
      * left. exists b. split; [exact Hb| exact R].
      * right. exists mb, ms'. split; [| exact R]. rewrite E7, lookup_insert_ne; [exact Lp|].
        intros E. pose proof (OLD _ _ _ Hin) as F. rewrite E in F. clear -F. lia.
  - intros cls A n' [E|Hin]; [discriminate| exact (BF cls A n' Hin)].
  - cbn. constructor; [| exact NDI]. intros Hin. unfold hb_ids in Hin. apply in_flat_map in Hin. destruct Hin as (b & Hb & Hp).
    destruct b as [[p|cls] A n']; cbn in Hp; [| destruct Hp]. destruct Hp as [E|[]]. subst p. pose proof (OLD _ _ _ Hb) as F. clear -F. lia.
  - constructor; [| exact NDL]. intros Hin. pose proof (OLD _ _ _ Hin) as F. clear -F. lia.
Qed.

Lemma arng_sec : forall L RNG RNG' st X nres' a ms n,
  awf L st X -> arng L RNG st -> fp_le RNG RNG' ->
  rng RNG' a ms -> rng RNG' (shad a) (ms / 8) -> rng RNG' (al_ptr_array L) (8 * nres') ->
  arng L RNG' (st_sec st nres' a ms n).
Proof.
  intros L RNG RNG' st X nres' a ms n WF AR LE R1 R2 R3.
  pose proof (arng_mono L RNG RNG' st LE AR) as (A1 & A2 & A3 & A4 & A5 & A6 & A6a & A6b & A6c & A7 & A8 & A9 & A10).
  pose proof (st_sec_fields st nres' a ms n) as (_ & _ & E3 & _ & _ & _ & E7 & _ & E9 & _ & E11 & _).
  unfold arng. rewrite E3. repeat (split; [assumption|]). split; [| exact A10].
  eapply RSEC_perm; [apply Permutation_sym; eapply sec_chunks_of_insert_sec; [eapply awf_fresh_none; exact WF| exact E7| exact E9| exact E11]|].
  constructor; [| exact A9]. cbn [sec_mb sec_ms]. split; [exact R1| exact R2].
Qed.

Lemma ASECc_perm : forall cs cs' L st X m, Permutation cs cs' -> ASECc cs L st X m -> ASECc cs' L st X m.
Proof.
  intros cs cs' L st X m P (WFS & ARR & INST & PZ & SHZ & AXH).
  split; [| split; [| split; [exact INST| split; [exact PZ| split]]]].
  4: { eapply AEXHc_sub; [| exact AXH]. intros ch Hch. eapply Permutation_in; [apply Permutation_sym; exact P| exact Hch]. }
  - destruct WFS as (ALO & WP & WR & WL & WB & WF1 & WD). unfold asec_wf.
    split; [exact ALO|]. split; [exact WP|]. split; [exact WR|]. split; [rewrite <- (Permutation_length P); exact WL|]. split; [exact WB|].
    split; [| eapply sec_disjoint_perm; [exact P| exact WD]].
    rewrite Forall_forall in WF1 |- *. intros ch Hin. apply WF1. eapply Permutation_in; [apply Permutation_sym; exact P| exact Hin].
  - destruct ARR as (order & PO & U64 & JK & PER). exists order. split; [eapply Permutation_trans; [exact PO| exact P]|].
    split; [exact U64| split; [exact JK| exact PER]].
  - intros x Hx HF HC. apply (SHZ x Hx HF). rewrite Forall_forall in HC |- *. intros ch Hin. apply HC.
    eapply Permutation_in; [exact P| exact Hin].
Qed.

Lemma asec_chunk_frameW : forall L W m m' mb ms n idx lv,
  munch W m m' -> wmono bsegs m m' ->
  sec_wf1 L (CSec mb ms n) ->
  (forall A k, mb <= A -> A + k <= mb + ms -> 0 < k -> disjoint_from W A k) ->
  (forall A k, shad mb <= A -> A + k <= shad mb + ms / 8 -> 0 < k -> disjoint_from W A k) ->
  asec_chunk m (CSec mb ms n) idx lv -> asec_chunk m' (CSec mb ms n) idx lv.
Proof.
  intros L W m m' mb ms n idx lv MU WM WF1 DC DS CH.
  pose proof WF1 as WF0. cbn [sec_wf1] in WF0. destruct WF0 as (G1 & G2 & G3 & G4 & G5 & G6 & _).
  pose proof (sec_facts n ltac:(lia) G6) as (_ & _ & RSE & RSR & _ & NSE & _ & MSR & MSM & _). rewrite <- G4 in MSR, MSM.
  assert (GR : 0 <= granules n /\ shad (mb + SEC_UOFF) = shad mb + 768 /\ 768 + granules n <= ms / 8).
  { unfold granules, SEC_UOFF. rewrite !shad_div, shlen_div. clear -G1 G5 RSR NSE MSR MSM. Z.div_mod_to_equations. lia. }
  destruct GR as (GR1 & GR2 & GR3).
  cbn [asec_chunk] in CH |- *. destruct CH as (H1 & H2 & H3 & H4 & (b1 & ctx & H5 & B1 & B3 & CX) & H6 & S1 & S2 & S3).
  unfold SEC_UOFF in *.
  split; [eapply cells_frame; [exact H1| exact MU| exact WM| cbn; apply DC; clear -RSR NSE MSR G4 G5; lia]|].
  split; [eapply junk_frame; [exact H2| exact MU| exact WM| intros _; apply DC; clear -RSR NSE MSR G4 G5; lia]|].
  split; [eapply cells_frame; [exact H3| exact MU| exact WM| cbn; apply DC; clear -RSR NSE MSR G4 G5; lia]|].
  split; [eapply junk_frame; [exact H4| exact MU| exact WM| intros _; apply DC; clear -RSR NSE MSR G4 G5; lia]|].
  split. { exists b1, ctx. split; [| split; [exact B1| split; [exact B3| exact CX]]].
           eapply cells_frame; [exact H5| exact MU| exact WM| cbn; apply DC; clear -RSR NSE MSR G4 G5; lia]. }
  split; [eapply junk_frame; [exact H6| exact MU| exact WM| intros _; apply DC; clear -RSR NSE MSR G4 G5; lia]|].
  split; [eapply fill_frame; [exact S1| exact MU| exact WM| intros _; apply DS; clear -GR3 GR1; lia]|].
  assert (GRP : 0 < granules n) by (unfold granules; rewrite shlen_div; clear -G5; Z.div_mod_to_equations; lia).
  split; [eapply cells_frame; [exact S2| exact MU| exact WM| cbn; rewrite Nat.add_0_r, Z2Nat.id by exact GR1; rewrite GR2; apply DS; clear -GR3 GR1 GRP; lia]|].
  eapply fill_frame; [exact S3| exact MU| exact WM| intros POS; rewrite GR2; apply DS; clear -GR3 GR1 POS; lia].
Qed.

Lemma junk_zero_len : forall m A n, junk_at m A n -> n <= 0 -> forall m', junk_at m' A n.
Proof.
  intros m A n [bs H] Hn m'. exists bs.
  pose proof H as H0. destruct H0 as [[[L _] [B0 [B1 B]]] [W0 [W1 WR]]]. cbn in L, B1, W1.
  assert (bs = []) as -> by (destruct bs; [reflexivity| cbn in L; lia]).
  split; [split; [cbn; lia|]|]; unfold bytes_at, wr_at; cbn.
  - split; [lia|]. split; [lia|]. intros i Hi. lia.
  - split; [lia|]. split; [lia|]. intros i Hi. lia.
Qed.

Section Append.
Variables (L : alayout) (W : list (Z * Z)) (m m' : amem).
Hypothesis MU : munch W m m'.
Hypothesis WM : wmono bsegs m m'.
Variables (st : astate) (X : aconc) (nres' a n id : Z).
Let ms := sec_map_size n.
Let cs := sec_chunks_of st.
Let nsec := a_nsec st.
Let nres := a_nres st.
Let PA := al_ptr_array L.
Let UB := a + 6144.
Hypothesis WF : awf L st X.
Hypothesis SEC : ASECc cs L st X m.
Hypothesis N : 1 <= n <= AREQMAX.
Hypothesis PRIM : is_primary n = false.
Hypothesis W1 : sec_wf1 L (CSec a ms n).
Hypothesis DJ : Forall (fun ch => a + ms <= sec_mb ch \/ sec_mb ch + sec_ms ch <= a) cs.
Hypothesis NR' : (nsec <> nres /\ nres' = nres)
              \/ (nsec = nres /\ nres' = nres + 16384
                  /\ rw_cells bsegs m' (PA + 8 * nres + 8) [CB (Z.to_nat (131072 - 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (131072 - 8)))]).
Hypothesis NRB : nres' <= 1048576.

Hypothesis NEWBUF : let '(d, cap, _) := a_emb st in cap = 0 \/ avoids_all d cap (sec_iv (CSec a ms n)) = true.
Hypothesis WK : Forall (c6_kind (CSec a ms n :: cs) L st) W.

Hypothesis Wch : forall ch, In ch cs ->
     (forall A k, sec_mb ch <= A -> A + k <= sec_mb ch + sec_ms ch -> 0 < k -> disjoint_from W A k)
  /\ (forall A k, shad (sec_mb ch) <= A -> A + k <= shad (sec_mb ch) + sec_ms ch / 8 -> 0 < k -> disjoint_from W A k).
Hypothesis Wpa : 0 < nsec -> disjoint_from W PA (8 * nsec).
Hypothesis Wpj : nsec + 1 < nres -> disjoint_from W (PA + 8 * nsec + 8) (8 * (nres - nsec - 1)).
Hypothesis Wbase : disjoint_from W (AINSTANCE + 80) 8.
Hypothesis Wp0 : disjoint_from W (shad (al_space_beg L)) (shlen K_REGION).
Hypothesis Wshz : forall x, (AIMG_HI <= x < KLS \/ K_HIGH_MEM <= x < ATOP) -> (x < a \/ a + ms <= x) -> disjoint_from W (shad x) 1.

Hypothesis C_srt : rw_cells bsegs m' (AINSTANCE + 128) [C1 (Z_to_bv 8 0)].
Hypothesis C_jst : junk_at m' (AINSTANCE + 136) 32.
Hypothesis C_jbs : junk_at m' (AINSTANCE + 168) 512.
Hypothesis C_mtx : rw_cells bsegs m' (AINSTANCE + 680) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
Hypothesis C_jgl : junk_at m' (AINSTANCE + 704) 16.
Hypothesis C_slot : rw_cells bsegs m' (PA + 8 * nsec) [C8 (Z_to_bv 64 a)].
Hypothesis C_hdr : rw_cells bsegs m' a [C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 ms); C8 (Z_to_bv 64 (needed_size n)); C8 (Z_to_bv 64 nsec)].
Hypothesis C_pgj : junk_at m' (a + 32) (4096 - 32).
Hypothesis C_mag : rw_cells bsegs m' (a + 4096) [C8 (Z_to_bv 64 0xCC6E96B9CC6E96B9); C8 (Z_to_bv 64 (UB + -16))].
Hypothesis C_lcj : junk_at m' (a + 4096 + 16) (2048 - 32).
Hypothesis C_ahd : rw_cells bsegs m' (UB + -16) [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 17); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 id)].
Hypothesis IDR : 0 < id < 2^31.
Hypothesis C_usr : junk_at m' UB (ms - 6144).
Hypothesis C_shf : fill_at m' (shad a) 768 0xfa.
Hypothesis C_shu : rw_cells bsegs m' (shad UB) [CB (Z.to_nat (granules n)) (block_shadow_bytes n)].
Hypothesis C_sht : fill_at m' (shad UB + granules n) (ms / 8 - 768 - granules n) 0xfa.

Lemma asec_chunk_new : asec_chunk m' (CSec a ms n) nsec true.
Proof.
  cbn [asec_chunk]. unfold SEC_UOFF, SEC_MAGIC. fold UB.
  replace (UB - 16) with (UB + -16) by (subst UB; lia).
  split; [exact C_hdr|]. split; [exact C_pgj|]. split; [exact C_mag|]. split; [exact C_lcj|].
  split. { exists 17, id. split; [exact C_ahd|]. split; [lia|]. split; [reflexivity| lia]. }
  split; [unfold SEC_UOFF; exact C_usr|]. split; [exact C_shf|]. split; [| exact C_sht].
  unfold sec_user_shadow. exact C_shu.
Qed.

Theorem asec_append : ASEC_of L (st_sec st nres' a ms n) X m'.
Proof.
  pose proof (awf_fresh_none L st X WF) as NONE.
  pose proof (st_sec_fields st nres' a ms n) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12).
  destruct SEC as (WFS & ARR & INST & PZ & SHZ & AXH).
  pose proof WFS as (ALO & WP & WR & WL & WB & WF1 & WD).
  pose proof W1 as W0. cbn [sec_wf1] in W0. destruct W0 as (G1 & G2 & G3 & G4 & G5 & G6 & GC).
  pose proof (sec_facts n N PRIM) as (NB & _ & RSE & RSR & _ & NSE & _ & MSR & MSM & MSB). fold ms in MSR, MSM, MSB.
  pose proof (ao_ptr L ALO) as OP. unfold aobj in OP. fold PA in OP.
  assert (NEWNOT : ~ In (CSec a ms n) cs).
  { intros Hin. pose proof (proj1 (Forall_forall _ _) DJ _ Hin) as D. cbn [sec_mb sec_ms] in D. clear -D MSB. lia. }
  assert (NSR : 0 <= nsec /\ nsec + 1 <= nres' /\ (nres' = nres \/ nres' = nres + 16384)).
  { subst nsec nres. destruct NR' as [(A1 & A2)|(A1 & A2 & _)]; clear -A1 A2 WB; lia. }
  destruct NSR as (NS0 & NS1 & NS2).
  unfold ASEC_of. eapply ASECc_perm; [apply Permutation_sym; eapply sec_chunks_of_insert_sec; [exact NONE| exact E7| exact E9| exact E11]|].
  fold cs. split; [| split; [| split; [| split; [| split]]]].
  6: {
       destruct AXH as (X1 & X2 & X3 & X4 & X5).
       assert (AX1 : AEXHc (CSec a ms n :: cs) L st m) by (repeat (split; [assumption|]); exact (emb_clrC_cons _ _ _ NEWBUF X5)).
       exact (aexhc_frameK _ L st (st_sec st nres' a ms n) m m' W ALO AX1 MU WK eq_refl eq_refl). }
  -
    unfold asec_wf. rewrite E2, E3, E4. split; [exact ALO|]. split; [exact WP|].
    split. { split; [| clear -NRB NS0 NS1; lia]. destruct WR as [WRM _]. destruct NS2 as [-> | ->]; [exact WRM|].
             subst nres. clear -WRM. Z.div_mod_to_equations. lia. }
    split; [cbn [length]; subst nsec; clear -WL; lia|]. split; [clear -NS0 NS1; subst nsec; lia|].
    split; [constructor; [exact W1| exact WF1]|].
    destruct WD as [ND PW]. split; [constructor; [exact NEWNOT| exact ND]|].
    intros ci cj [<-|Hi] [<-|Hj] NE; [exfalso; exact (NE eq_refl)| | |].
    + pose proof (proj1 (Forall_forall _ _) DJ _ Hj) as D. cbn [sec_mb sec_ms] in D |- *. clear -D. lia.
    + pose proof (proj1 (Forall_forall _ _) DJ _ Hi) as D. cbn [sec_mb sec_ms] in D |- *. clear -D. lia.
    + exact (PW ci cj Hi Hj NE).
  -
    destruct ARR as (order & PO & U64 & JK & PER). unfold asec_arr. rewrite E3, E4. fold PA. fold nsec.
    assert (LEN : Z.of_nat (length order) = nsec) by (rewrite (Permutation_length PO); exact WL).
    exists (order ++ [CSec a ms n]).
    split. { eapply Permutation_trans; [apply Permutation_app_comm|]. cbn [app]. apply perm_skip. exact PO. }
    split; [| split].
    + rewrite map_app. cbn [map sec_mb]. apply u64arr_snoc.
      * destruct order as [|o0 order'].
        { destruct U64 as [[B0 [B1 _]] _]. apply u64arr_nil; [clear -OP; lia| clear -OP; atop_facts; lia]. }
        eapply u64arr_frame; [exact U64| exact MU| exact WM|]. rewrite length_map. cbn [length] in LEN |- *.
        replace (8 * Z.of_nat (S (length order'))) with (8 * nsec) by (clear -LEN; lia). apply Wpa. clear -LEN; lia.
      * rewrite length_map. replace (PA + 8 * Z.of_nat (length order)) with (PA + 8 * nsec) by (clear -LEN; lia). exact C_slot.
    + destruct NR' as [(A1 & A2)|(A1 & A2 & ZC)].
      * rewrite A2. destruct (junk_split m (PA + 8 * nsec) 8 (8 * (nres - nsec - 1))
                      ltac:(replace (8 + 8 * (nres - nsec - 1)) with (8 * (nres - nsec)) by (clear; lia); exact JK) ltac:(clear; lia) ltac:(clear -A1 WB; subst nsec nres; lia))
          as [_ JR].
        replace (PA + 8 * (nsec + 1)) with (PA + 8 * nsec + 8) by (clear; lia).
        replace (8 * (nres - (nsec + 1))) with (8 * (nres - nsec - 1)) by (clear; lia).
        destruct (Z_lt_le_dec (nsec + 1) nres) as [LT|GE].
        { eapply junk_frame; [exact JR| exact MU| exact WM| intros _; apply Wpj; exact LT]. }
        eapply junk_zero_len; [exact JR| clear -GE; lia].
      * rewrite A2, A1. subst nres. replace (PA + 8 * (a_nres st + 1)) with (PA + 8 * a_nres st + 8) by (clear; lia).
        replace (8 * (a_nres st + 16384 - (a_nres st + 1))) with (131072 - 8) by (clear; lia). eexists. exact ZC.
    + intros i ch Hi.
      destruct (Nat.lt_ge_cases i (length order)) as [LT|GE].
      * rewrite nth_error_app1 in Hi by exact LT. destruct (PER i ch Hi) as (lv & LV & CH).
        assert (Hin : In ch cs) by (eapply Permutation_in; [exact PO| eapply nth_error_In; exact Hi]).
        destruct (asec_wf_all L st cs ch WFS Hin) as (mb & ms' & n' & -> & WF1c).
        exists lv. split.
        { rewrite LV. unfold sec_live. rewrite E7. split; intros [p Hp].
          - exists p. rewrite lookup_insert_ne; [exact Hp|]. intros E. subst p. rewrite NONE in Hp. discriminate.
          - destruct (N.eq_dec p (a_next st)) as [->|NE].
            + rewrite lookup_insert_eq in Hp. injection Hp as Ea Em En. exfalso. apply NEWNOT. rewrite <- Ea, <- Em, <- En in Hin. exact Hin.
            + exists p. rewrite lookup_insert_ne in Hp by (intros E; apply NE; symmetry; exact E). exact Hp. }
        destruct (Wch _ Hin) as [DC DS]. cbn [sec_mb sec_ms] in DC, DS.
        eapply asec_chunk_frameW; [exact MU| exact WM| exact WF1c| exact DC| exact DS| exact CH].
      * rewrite nth_error_app2 in Hi by exact GE.
        assert (EI : i = length order) by (destruct (i - length order)%nat as [|k] eqn:EK; [clear -GE EK; lia| cbn in Hi; destruct k; discriminate]).
        subst i. rewrite Nat.sub_diag in Hi. cbn in Hi. injection Hi as <-.
        exists true. split.
        { split; [intros _| reflexivity]. exists (a_next st). rewrite E7, lookup_insert_eq. reflexivity. }
        rewrite LEN. exact asec_chunk_new.
  -
    destruct INST as (I1 & _ & _ & _ & _ & _). unfold asec_inst. unfold AINSTANCE in *.
    split; [eapply cells_frame; [exact I1| exact MU| exact WM| cbn; exact Wbase]|].
    split; [exists (Z_to_bv 8 0); exact C_srt|]. split; [exact C_jst|]. split; [exact C_jbs|]. split; [| exact C_jgl].
    pose proof C_mtx as M4. rw_split M4 1%nat M0 M3. exact M3.
  -
    unfold aprim0 in *. eapply azero_frame; [exact PZ| exact MU| exact WM| intros _; exact Wp0].
  -
    intros x Hx HF HC. apply Forall_cons_iff in HC. destruct HC as [HCn HC]. cbn [sec_mb sec_ms] in HCn.
    assert (SX : 0 <= shad x < 2^64) by (rewrite shad_div; unfold ASHOFF, K_HIGH_MEM in *; unfold AIMG_HI, KLS in Hx; clear -Hx; Z.div_mod_to_equations; lia).
    rewrite <- (SHZ x Hx HF HC). apply MU. rewrite wa_unsigned by exact SX.
    eapply (disjoint_outside W (shad x) 1); [| clear; lia]. apply Wshz; [exact Hx| clear -HCn Hx; lia].
Qed.
End Append.

Definition WT (L : alayout) (sp a ms nsec nres nres' : Z) : list (Z * Z) :=
  [(sp - 4096, sp); (al_t L + 2800, al_t L + 3169); (AINSTANCE + 112, AINSTANCE + 720);
   (al_ptr_array L + 8 * nsec, al_ptr_array L + 8 * nsec + 8); (al_ptr_array L + 8 * nres, al_ptr_array L + 8 * nres');
   (a, a + ms); (shad a, shad a + ms / 8);
   (0x1adb48, 0x5fdb90); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608)]%Z.

Definition wt_facts (L : alayout) (sp lo a ms nsec nres nres' : Z) : Prop :=
     alayout_ok L /\ ATOP <= lo /\ lo <= sp - 4096
  /\ ablk a (a + ms) /\ a + ms <= ATOP /\ a mod 4096 = 0 /\ ms mod 4096 = 0 /\ 0 < ms /\ sec_clear L a ms
  /\ 0 <= nsec /\ nsec + 1 <= nres' /\ 8 * nres' <= 8388608 /\ 0 <= nres <= nres'.

Local Lemma ablk_int : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6492160 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
Local Lemma aobj_int : forall a n, aobj a n -> 0x10000 <= n ->
  6492160 <= a /\ a + n <= ATOP /\ exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof.
  intros a n H Hn. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. destruct H as (H1 & H2 & H3 & H4 & H5).
  split; [lia|]. split; [lia|]. destruct H4; [exists 0 | exists 1]; lia.
Qed.
Local Lemma aobj4_int : forall a, aobj a 4096 ->
  4096 <= a /\ a + 4096 <= ATOP
  /\ (exists k, 0 <= k <= 1 /\ a + 4096 <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a)
  /\ (exists j, 0 <= j <= 1 /\ a + 4096 <= 65536 + j * 18446744073709551616 /\ 6492160 * j <= a).
Proof.
  intros a H. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. destruct H as (H1 & H2 & H3 & H4 & H5).
  split; [lia|]. split; [lia|]. split; [destruct H4; [exists 0 | exists 1]; lia | destruct H5 as [_ [H5|H5]]; [exists 0 | exists 1]; lia].
Qed.

Section KW.
Variables (L : alayout) (sp lo a ms nsec nres nres' : Z).
Hypothesis WTF : wt_facts L sp lo a ms nsec nres nres'.
Let W' := List.filter nonempty (WT L sp a ms nsec nres nres').

Local Ltac inWT Hiv := unfold WT in Hiv; cbn [In] in Hiv;
  destruct Hiv as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]; cbn [fst snd] in *.
Local Ltac facts :=
  lazymatch goal with |- _ =>
  pose proof WTF as (ALO & CEIL & LO & AHI0 & ACE & AAL & MSM & MSP & (C_t & C_c & C_r & C_p & C_n & C_s & C_f & C_d) & NS0 & NS1 & NS8 & NS9);
  pose proof (ao_t L ALO) as OT; pose proof (ao_ctx L ALO) as OC; pose proof (ao_res L ALO) as ORS; pose proof (ao_nodes L ALO) as ON;
  pose proof (ao_store L ALO) as OS; pose proof (ao_ptr L ALO) as OP; unfold aobj in OT, OC, ORS, ON, OS, OP;
  pose proof (aobj4_int _ (ao_t L ALO)) as (_ & _ & [kT OTs] & [jT OTi]); pose proof (aobj_int _ _ (ao_ctx L ALO) ltac:(clear; lia)) as (OCi & _ & [kC OCs]);
  pose proof (aobj_int _ _ (ao_nodes L ALO) ltac:(clear; lia)) as (ONi & _ & [kN ONs]); pose proof (aobj_int _ _ (ao_store L ALO) ltac:(clear; lia)) as (OSi & _ & [kS OSs]);
  pose proof (aobj_int _ _ (ao_ptr L ALO) ltac:(clear; lia)) as (OPi & _ & [kP OPs]); pose proof (ao_res_hi L ALO) as RHI;
  destruct (ablk_int _ _ AHI0) as [kA ABND]; pose proof (ablk_lin _ _ AHI0) as (AL1 & AL2 & _ & _); unfold AIMG_HI in AL1;
  pose proof (ad_t_res L ALO) as D_t_res; pose proof (ad_nodes_res L ALO) as D_n_res; pose proof (ad_store_res L ALO) as D_s_res;
  pose proof (ad_ptr_res L ALO) as D_p_res; pose proof (ad_t_ctx L ALO) as D_t_c; pose proof (ad_t_nodes L ALO) as D_t_n;
  pose proof (ad_t_store L ALO) as D_t_s; pose proof (ad_t_ptr L ALO) as D_t_p; pose proof (ad_ctx_nodes L ALO) as D_c_n;
  pose proof (ad_ctx_store L ALO) as D_c_s; pose proof (ad_ctx_ptr L ALO) as D_c_p;
  unfold adisj in D_t_res, D_n_res, D_s_res, D_p_res, D_t_c, D_t_n, D_t_s, D_t_p, D_c_n, D_c_s, D_c_p
  end.

Lemma WT_shad : 0x800be200 <= shad a /\ shad a + ms / 8 = shad (a + ms) /\ shad (a + ms) <= 0x10007fef8000
                /\ (forall x, x < a -> shad x + 1 <= shad a) /\ (forall x, a + ms <= x -> shad (a + ms) <= shad x).
Proof.
  facts. rewrite !shad_div. unfold ASHOFF in *. split; [clear -AL1; Z.div_mod_to_equations; lia|].
  split; [clear -AAL MSM; Z.div_mod_to_equations; lia|]. split; [clear -ACE; Z.div_mod_to_equations; lia|].
  split; intros x Hx; rewrite shad_div; unfold ASHOFF; [clear -Hx AAL| clear -Hx]; Z.div_mod_to_equations; lia.
Qed.

Lemma KT_X : forall A k, 0 <= k ->
  (forall iv, In iv (WT L sp a ms nsec nres nres') -> fst iv < snd iv -> A + k <= fst iv \/ snd iv <= A) ->
  disjoint_from W' A k.
Proof.
  intros A k Hk H. subst W'. apply disjoint_from_Forall. apply Forall_forall. intros iv Hiv.
  apply List.filter_In in Hiv. destruct Hiv as [Hiv NEV]. unfold nonempty in NEV. apply Z.ltb_lt in NEV. exact (H iv Hiv NEV).
Qed.

Lemma KT_img : forall A k, 65536 <= A -> 0 <= k -> A + k <= AIMG_HI ->
  (A + k <= AINSTANCE + 112 \/ AINSTANCE + 720 <= A) -> (A + k <= 0x1adb48 \/ 0x5fdb90 <= A) -> disjoint_from W' A k.
Proof.
  facts. pose proof WT_shad as (SA1 & SA2 & SA3 & _).
  intros A k H1 H2 H3 H4 H5. apply KT_X; [exact H2|]. intros iv Hiv NEV. inWT Hiv; unfold AIMG_HI, AINSTANCE in *;
    clear -H1 H2 H3 H4 H5 NEV CEIL LO OT OP AL1 SA1 ON OS NS0 NS9 OTs OTi ONs ONi OSs OSi OPs OPi; lia.
Qed.

Lemma KT_obj : forall A k, (A + k <= 65536 \/ 6492160 <= A) -> (A + k <= 2147446784 \/ 17594333495296 <= A) -> 0 <= k -> A + k <= ATOP ->
  (A + k <= al_t L + 2800 \/ al_t L + 3169 <= A) -> (A + k <= al_ptr_array L \/ al_ptr_array L + 8388608 <= A) ->
  (A + k <= a \/ a + ms <= A) -> (A + k <= al_nodes L \/ al_nodes L + 1048576 <= A) -> (A + k <= al_store L \/ al_store L + 8388608 <= A) ->
  disjoint_from W' A k.
Proof.
  facts. pose proof WT_shad as (SA1 & SA2 & SA3 & _).
  intros A k H0 H1 H2 H3 H4 H5 H6 H7 H8. apply KT_X; [exact H2|]. intros iv Hiv NEV. inWT Hiv; unfold AIMG_HI, AINSTANCE in *;
    clear -H0 H1 H2 H3 H4 H5 H6 H7 H8 NEV CEIL LO NS0 NS1 NS8 NS9 SA1 SA2 SA3; lia.
Qed.

Lemma KT_shad : forall A k, 2147446784 <= A -> 0 <= k -> A + k <= 17594333495296 ->
  (A + k <= shad a \/ shad (a + ms) <= A) -> disjoint_from W' A k.
Proof.
  facts. pose proof WT_shad as (SA1 & SA2 & SA3 & _).
  intros A k H1 H2 H3 H4. apply KT_X; [exact H2|]. intros iv Hiv NEV. inWT Hiv; unfold AIMG_HI, AINSTANCE in *;
    clear -H1 H2 H3 H4 NEV CEIL LO OT OP ABND ON OS SA2 NS0 NS1 NS8 NS9 OTs OTi ONs ONi OSs OSi OPs OPi; lia.
Qed.

Lemma KT_t : forall A k, al_t L <= A -> 0 <= k -> A + k <= al_t L + 2800 -> disjoint_from W' A k.
Proof. facts. intros A k H1 H2 H3. apply KT_obj; atop_facts; clear -H1 H2 H3 OT D_t_p C_t D_t_n D_t_s OTs OTi; lia. Qed.

Lemma KT_ctx : forall A k, al_ctx L <= A -> 0 <= k -> A + k <= al_ctx L + 65536 -> disjoint_from W' A k.
Proof. facts. intros A k H1 H2 H3. apply KT_obj; atop_facts; clear -H1 H2 H3 OC OT D_t_c D_c_p C_c D_c_n D_c_s OTs OTi OCs OCi; lia. Qed.

Lemma KT_res : forall A k, al_res L <= A -> 0 <= k -> A + k <= al_res L + 137439023104 -> disjoint_from W' A k.
Proof. facts. intros A k H1 H2 H3. apply KT_obj; atop_facts; clear -H1 H2 H3 ORS RHI OT D_t_res D_p_res C_r D_n_res D_s_res OTs OTi; lia. Qed.

Lemma KT_res_geo : 2201439137792 <= shad (al_res L) /\ shad (al_res L) + shlen 137439023104 = shad (al_res L + 137439023104)
                   /\ shad (al_res L + 137439023104) <= 0x10007fef8000
                   /\ (shad (al_res L + 137439023104) <= shad a \/ shad (a + ms) <= shad (al_res L)).
Proof. facts. rewrite !shad_div, shlen_div. unfold ASHOFF in *. clear -ORS RHI C_r AAL. Z.div_mod_to_equations. lia. Qed.

Lemma KT_res_sh : forall A k, shad (al_res L) <= A -> 0 <= k -> A + k <= shad (al_res L + 137439023104) -> disjoint_from W' A k.
Proof. pose proof KT_res_geo as (SR1 & SR2 & SR3 & SR4). intros A k H1 H2 H3. apply KT_shad; clear -H1 H2 H3 SR1 SR3 SR4; lia. Qed.

Lemma WT_kinds : forall cs st n, sec_wf1 L (CSec a ms n) -> Forall (c6_kind (CSec a ms n :: cs) L st) W'.
Proof.
  intros cs st n VW. facts. pose proof WT_shad as (SA1 & SA2 & SA3 & _).
  apply Forall_forall. intros iv Hin. unfold W' in Hin. apply List.filter_In in Hin. destruct Hin as [Hin _].
  unfold c6_kind. intros NEV. inWT Hin.
  - left. unfold AC6U.TwinB.c6_std. left. clear -CEIL LO. lia.
  - left. unfold AC6U.TwinB.c6_std. right; left. clear. lia.
  - left. unfold AC6U.TwinB.c6_std. do 5 right; left. unfold AINSTANCE. clear. lia.
  - left. unfold AC6U.TwinB.c6_std. do 12 right. clear -NS0 NS1 NS8 NS9. lia.
  - left. unfold AC6U.TwinB.c6_std. do 12 right. clear -NS0 NS1 NS8 NS9. lia.
  - right; right; left. exists (CSec a ms n). split; [left; reflexivity|]. split; [exact VW|]. cbn [sec_mb sec_ms]. clear. lia.
  - left. unfold AC6U.TwinB.c6_std. do 4 right; left. clear -SA1 SA2 SA3. lia.
  - left. unfold AC6U.TwinB.c6_std. do 7 right; left. clear. lia.
  - left. unfold AC6U.TwinB.c6_std. do 8 right; left. clear. lia.
  - left. unfold AC6U.TwinB.c6_std. do 9 right; left. clear. lia.
Qed.

Lemma KT_rt : forall m m', munch W' m m' -> wmono bsegs m m' -> arep_rt L m -> arep_rt L m'.
Proof.
  intros m m' MU WM RT. eapply arep_rt_frame; [exact MU | exact WM | exact RT |]. unfold rt_hulls, ATP88, ATSD.
  repeat (apply Forall_cons; [cbn [fst snd]; first [apply KT_img; clear; unfold AIMG_HI, AINSTANCE; lia | apply KT_ctx; clear; lia] |]). apply Forall_nil.
Qed.
Lemma KT_rt2 : forall m m', munch W' m m' -> wmono bsegs m m' -> arep_rt2 m -> arep_rt2 m'.
Proof. intros m m' MU WM RT2. eapply arep_rt2_frame; [exact MU | exact WM | exact RT2 | | |]; apply KT_img; clear; unfold AIMG_HI, AINSTANCE; lia. Qed.
Lemma KT_rt3 : forall m m', munch W' m m' -> wmono bsegs m m' -> arep_rt3 m -> arep_rt3 m'.
Proof.
  intros m m' MU WM RT3. eapply arep_rt3_frame; [exact MU | exact WM | exact RT3 |]. unfold rt3_hulls.
  repeat (apply Forall_cons; [cbn [fst snd]; apply KT_img; clear; unfold AIMG_HI, AINSTANCE; lia |]). apply Forall_nil.
Qed.
Lemma KT_relro : forall m m', munch W' m m' -> arelro m -> arelro m'.
Proof. intros m m' MU HRO. eapply arelro_frame; [exact MU | exact HRO | apply KT_img; clear; unfold ARELRO_LO, ARELRO_HI, AIMG_HI, AINSTANCE; lia]. Qed.
End KW.

Section Store.
Variable DI : ADepotIface.
Variables (AQ : alayout -> astate -> aconc -> amem -> Prop) (AFK : alayout -> list ablock -> amem -> Prop).
Let AHS : aholes := AH DI AQ ASEC_of AFK.
Hypothesis HL : ahole_laws AHS.
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI) CI.
Hypothesis CI_OK2 : Forall (fun iv => snd iv <= AINSTANCE \/ AINSTANCE + 728 <= fst iv) CI.

Theorem store_sec : forall (L : alayout) (RNG RNG' : footprint) (sp lo : Z) (m m' : amem) (st : astate) (X : aconc) (LB : list ablock)
    (n a nres' id : Z) (sj' : list word) (RESV : list (Z * Z)),
  let nsec := a_nsec st in let nres := a_nres st in let PA := al_ptr_array L in let ms := sec_map_size n in
  let UB := a + 6144 in let t := al_t L in
  alayout_ok L -> arng L RNG st -> AREP AHS L st X m -> ablocks L st X LB -> AFK L LB m ->
  1 <= n <= AREQMAX -> is_primary n = false ->
  sfresh RESV st n a = true -> aresv_ok L RESV ->
  ATOP <= lo -> lo <= sp - 4096 -> sp <= 2^47 ->
  fp_le RNG RNG' -> rng RNG' a ms -> rng RNG' (shad a) (ms / 8) ->
  ((nsec <> nres /\ nres' = nres)
   \/ (nsec = nres /\ nres' = nres + 16384
       /\ rw_cells bsegs m' (PA + 8 * nres + 8) [CB (Z.to_nat (131072 - 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (131072 - 8)))])) ->
  nres' <= 1048576 -> rng RNG' PA (8 * nres') ->
  munch (WT L sp a ms nsec nres nres') m m' -> wmono bsegs m m' ->

  u64arr bsegs m' (t + 2800) sj' -> length sj' = 46%nat -> rw_cells bsegs m' (t + 3168) [C1 (Z_to_bv 8 0)] ->
  rw_cells bsegs m' (AINSTANCE + 112) [C8 (Z_to_bv 64 nres'); C8 (Z_to_bv 64 (nsec + 1))] ->
  rw_cells bsegs m' (AINSTANCE + 128) [C1 (Z_to_bv 8 0)] -> junk_at m' (AINSTANCE + 136) 32 -> junk_at m' (AINSTANCE + 168) 512 ->
  rw_cells bsegs m' (AINSTANCE + 680) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  junk_at m' (AINSTANCE + 704) 16 ->
  rw_cells bsegs m' (PA + 8 * nsec) [C8 (Z_to_bv 64 a)] ->
  rw_cells bsegs m' a [C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 ms); C8 (Z_to_bv 64 (needed_size n)); C8 (Z_to_bv 64 nsec)] ->
  junk_at m' (a + 32) (4096 - 32) ->
  rw_cells bsegs m' (a + 4096) [C8 (Z_to_bv 64 0xCC6E96B9CC6E96B9); C8 (Z_to_bv 64 (UB + -16))] ->
  junk_at m' (a + 4096 + 16) (2048 - 32) ->
  rw_cells bsegs m' (UB + -16) [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 17); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 id)] ->
  0 < id < 2^31 ->
  junk_at m' UB (ms - 6144) ->
  fill_at m' (shad a) 768 0xfa ->
  rw_cells bsegs m' (shad UB) [CB (Z.to_nat (granules n)) (block_shadow_bytes n)] ->
  fill_at m' (shad UB + granules n) (ms / 8 - 768 - granules n) 0xfa ->
  ADEPOT DI L m' ->
     aheap_pres CI LB sp m m'
  /\ AHEAP_P AHS L RNG' (st_sec st nres' a ms n) (HB (a_next st) UB n :: LB) m'.
Proof.
  intros until RESV. cbv zeta.
  intros ALO ARNG AR BL HFK N PRIM FRSH ROK CEIL LO SP47 FPLE RA RSA NR' NRB RPA' MU0 WM
         STATS LSJ UNW I112 I128 J136 J168 I680 J704 SLOT HDR PGJ MAG LCJ AHD IDR USR SHF SHU SHT DEP.
  set (ms := sec_map_size n) in *.

  pose proof (valid_geo L RESV st n a N PRIM FRSH ROK) as (AAL & AHI0 & ACE & MSP & _). fold ms in ACE, MSP.
  pose proof (valid_clear L RESV st n a N PRIM FRSH ROK) as VC. fold ms in VC.
  pose proof (valid_hulls L RESV st n a N PRIM FRSH ROK) as VH. fold ms in VH.
  pose proof (valid_chunks L RESV st n a N PRIM FRSH ROK) as VK. fold ms in VK.
  pose proof (valid_wf1 L RESV st n a N PRIM FRSH ROK) as VW. fold ms in VW.
  pose proof (sec_facts n N PRIM) as (NB & _ & RSE & RSR & _ & NSE & _ & MSR & MSM & MSB). fold ms in MSR, MSM, MSB.
  destruct VC as (C_t & C_c & C_r & C_p & C_n & C_s & C_f & C_d).
  unfold K_HIGH_MEM in AHI0.
  pose proof (munch_filter_nonempty _ m m' MU0) as MU. clear MU0. set (W' := List.filter nonempty (WT L sp a ms (a_nsec st) (a_nres st) nres')) in *.
  assert (NE : Forall (fun iv => fst iv < snd iv) W') by (apply nonempty_filter).

  pose proof (alayout_space L ALO) as (SP1 & SP2 & SP3 & SP4).
  pose proof (ao_t L ALO) as OT. pose proof (ao_ctx L ALO) as OC. pose proof (ao_res L ALO) as ORS. pose proof (ao_nodes L ALO) as ON. pose proof (ao_store L ALO) as OS.
  pose proof (ao_fake L ALO) as OFK. pose proof (ao_ptr L ALO) as OP. pose proof (ao_dtls L ALO) as OD.
  unfold aobj in OT, OC, ORS, ON, OS, OFK, OP, OD. pose proof (ao_space L ALO) as RSP.
  pose proof (aobj4_int _ (ao_t L ALO)) as (_ & _ & [kT OTs] & [jT OTi]). pose proof (aobj_int _ _ (ao_ctx L ALO) ltac:(clear; lia)) as (OCi & _ & [kC OCs]).
  pose proof (aobj_int _ _ (ao_nodes L ALO) ltac:(clear; lia)) as (ONi & _ & [kN ONs]). pose proof (aobj_int _ _ (ao_store L ALO) ltac:(clear; lia)) as (OSi & _ & [kS OSs]).
  pose proof (aobj_int _ _ (ao_ptr L ALO) ltac:(clear; lia)) as (OPi & _ & [kP OPs]). pose proof (aobj_int _ _ (ao_fake L ALO) ltac:(clear; lia)) as (OFKi & _ & [kF OFKs]).
  pose proof (aobj4_int _ (ao_dtls L ALO)) as (_ & _ & [kD ODs] & [jD ODi]). pose proof (ao_res_hi L ALO) as RHI.
  destruct (ablk_int _ _ AHI0) as [kA ABND]. pose proof (ablk_lin _ _ AHI0) as (AL1 & AL2 & _ & _). unfold AIMG_HI in AL1.
  pose proof (ad_t_res L ALO) as D_t_res. pose proof (ad_ctx_res L ALO) as D_c_res. pose proof (ad_nodes_res L ALO) as D_n_res. pose proof (ad_store_res L ALO) as D_s_res.
  pose proof (ad_fake_res L ALO) as D_f_res. pose proof (ad_ptr_res L ALO) as D_p_res. pose proof (ad_t_ctx L ALO) as D_t_c.
  pose proof (ad_t_nodes L ALO) as D_t_n. pose proof (ad_t_store L ALO) as D_t_s. pose proof (ad_t_fake L ALO) as D_t_f. pose proof (ad_t_ptr L ALO) as D_t_p.
  pose proof (ad_ctx_nodes L ALO) as D_c_n. pose proof (ad_ctx_store L ALO) as D_c_s. pose proof (ad_ctx_fake L ALO) as D_c_f. pose proof (ad_ctx_ptr L ALO) as D_c_p.
  pose proof (ad_nodes_fake L ALO) as D_n_f. pose proof (ad_nodes_ptr L ALO) as D_n_p. pose proof (ad_store_fake L ALO) as D_s_f. pose proof (ad_store_ptr L ALO) as D_s_p.
  pose proof (ad_fake_ptr L ALO) as D_f_p. pose proof (ad_dtls_res L ALO) as D_d_res. pose proof (ad_t_dtls L ALO) as D_t_d. pose proof (ad_dtls_ptr L ALO) as D_d_p.
  pose proof (ad_nodes_dtls L ALO) as D_n_d. pose proof (ad_store_dtls L ALO) as D_s_d. pose proof (ad_fake_dtls L ALO) as D_f_d.
  unfold adisj in D_t_res, D_c_res, D_n_res, D_s_res, D_f_res, D_p_res, D_t_c, D_t_n, D_t_s, D_t_f, D_t_p, D_c_n, D_c_s, D_c_f, D_c_p,
                   D_n_f, D_n_p, D_s_f, D_s_p, D_f_p, D_d_res, D_t_d, D_d_p, D_n_d, D_s_d, D_f_d.

  pose proof AR as AR0. destruct AR0 as (WF & RT & INST & THR & CLS & HQ & HS & HD & HRO & RT2 & AVL & RT3).
  pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVE & FRESH & UNIQ).
  pose proof HS as HS0. unfold AHS, AH in HS0. cbn [ah_sec] in HS0. unfold ASEC_of in HS0.
  pose proof HS0 as (WFS & ARR & INST2 & PZ & SHZ & AXH). pose proof WFS as (_ & WP & WR & WL & WB & WF1 & WD).
  assert (NSR : 0 <= a_nsec st /\ a_nsec st + 1 <= nres' /\ 8 * nres' <= 8388608 /\ a_nres st <= nres').
  { destruct NR' as [(A1 & A2)|(A1 & A2 & _)]; clear -A1 A2 WB NRB WR; lia. }
  destruct NSR as (NS0 & NS1 & NS8 & NS9).

  assert (WTF : wt_facts L sp lo a ms (a_nsec st) (a_nres st) nres').
  { unfold wt_facts. repeat lazymatch goal with |- _ /\ _ => split end; try assumption.
    - unfold sec_clear. repeat (split; [assumption|]). assumption.
    - clear -WB; lia. }
  pose proof (WT_shad L sp lo a ms _ _ _ WTF) as (SA1 & SA2 & SA3 & SAlt & SAge).
  pose proof (KT_X L sp a ms (a_nsec st) (a_nres st) nres') as KX. pose proof (KT_img L sp lo a ms _ _ _ WTF) as Kimg.
  pose proof (KT_obj L sp lo a ms _ _ _ WTF) as Kobj. pose proof (KT_shad L sp lo a ms _ _ _ WTF) as Kshad.
pose proof (KT_t L sp lo a ms _ _ _ WTF) as Kt.
  pose proof (KT_ctx L sp lo a ms _ _ _ WTF) as Kctx. pose proof (KT_res L sp lo a ms _ _ _ WTF) as Kres.
  pose proof (KT_res_sh L sp lo a ms _ _ _ WTF) as Kres_sh. pose proof (KT_res_geo L sp lo a ms _ _ _ WTF) as (SR1 & SR2 & SR3 & SR4).
  fold W' in KX, Kimg, Kobj, Kshad, Kt, Kctx, Kres, Kres_sh.
  Local Ltac inWT Hiv := unfold WT in Hiv; cbn [In] in Hiv;
    destruct Hiv as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]; cbn [fst snd] in *.

  assert (BB : forall b, In b (x_busy X) -> al_res L <= xb_alloc L b /\ xb_alloc L b + size_of_class (xb_class b) <= al_res L + 137439023104).
  { intros b Hb. destruct (BUSY b Hb) as [CLB _].
    destruct (PERC (xb_class b) CLB) as (Q1 & Q2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & QR).
    pose proof (size_of_class_facts (xb_class b) CLB) as [QS _].
    assert (KB : 0 <= xb_slot b < ndist st (xb_class b)).
    { apply QR. apply in_app_iff. right. apply in_app_iff. right. unfold busy_slots. apply in_map_iff. exists b. split; [reflexivity|].
      apply filter_In. split; [exact Hb| apply Z.eqb_refl]. }
    pose proof (slot_in_region L st (xb_class b) (xb_slot b) ltac:(clear -QS; lia) (proj1 Q1) KB) as (P5 & P4 & P0).
    unfold xb_alloc, aregion, K_REGION, K_FREEARR_OFF, K_NUM_CLASSES in *. clear -P5 P4 Q1 Q2 CLB RSP. lia. }
  pose proof (st_sec_fields st nres' a ms n) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12).
  set (st2 := st_sec st nres' a ms n) in *.

  assert (AR' : AREP AHS L st2 X m').
  { split; [apply awf_sec; exact WF|].
    split. { eapply arep_rt_frame; [exact MU | exact WM | exact RT |]. unfold rt_hulls, ATP88, ATSD.
             repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI, AINSTANCE; lia | apply Kctx; clear; lia] |]). apply Forall_nil. }
    split. {
      destruct INST as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9). unfold ainstance. subst st2. rewrite E3, E4.
      split; [eapply cells_frame; [exact I1| exact MU| exact WM| cbn; apply Kimg; clear; unfold AIMG_HI, AINSTANCE; lia]|].
      split; [eapply cells_frame; [exact I2| exact MU| exact WM| cbn; apply Kimg; clear; unfold AIMG_HI, AINSTANCE; lia]|].
      split; [eapply cells_frame; [exact I3| exact MU| exact WM| cbn; apply Kimg; clear; unfold AIMG_HI, AINSTANCE; lia]|].
      split; [eapply cells_frame; [exact I4| exact MU| exact WM| cbn; apply Kimg; clear; unfold AIMG_HI, AINSTANCE; lia]|].
      split; [exact I112|].
      split; [pose proof I680 as M4; rw_split M4 1%nat M0 M3; exact M0|].
      split; [eapply cells_frame; [exact I7| exact MU| exact WM| cbn; apply Kimg; clear; unfold AIMG_HI, AINSTANCE; lia]|].
      split; [eapply cells_frame; [exact I8| exact MU| exact WM| cbn; apply Kimg; clear; unfold AIMG_HI, AINSTANCE; lia]|].
      eapply cells_frame; [exact I9| exact MU| exact WM| cbn; apply Kimg; clear; unfold AIMG_HI, AINSTANCE; lia]. }
    split. {
      destruct THR as (T0 & T40 & CACHES & CSTATS & _ & _). unfold athread.
      split; [eapply cells_frame; [exact T0 | exact MU | exact WM | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; apply Kt; clear; lia]|].
      split; [eapply cells_frame; [exact T40 | exact MU | exact WM | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; apply Kt; clear; lia]|].
      split. { intros c Hc. eapply acache_cells_frame; [exact MU | exact WM | exact (CACHES c Hc) | subst st2; reflexivity | subst st2; reflexivity | reflexivity |].
               unfold acache_addr. unfold K_NUM_CLASSES in Hc. apply Kt; clear -Hc; lia. }
      split; [eapply junk_frame; [exact CSTATS | exact MU | exact WM | intros _; apply Kt; clear; lia]|].
      split; [exists sj'; split; [exact STATS| exact LSJ]| exact UNW]. }
    split. {
      intros c Hc. destruct (CLS c Hc) as (REG & FARR & SLOTS & SHADOW).
      destruct (PERC c Hc) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & QLENF & QLENC & QCNTB & QND & QRANGE).
      pose proof (size_of_class_facts c Hc) as [QS QS16]. pose proof (aregion_mod L c SAL) as RM. unfold K_NUM_CLASSES in Hc.
      assert (RI : al_res L <= aregion L c /\ aregion L c + K_REGION <= al_space_beg L + K_SPACE_SIZE
                   /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104).
      { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc RSP. lia. }
      destruct RI as (RI1 & RI2 & RI3). unfold K_REGION, K_SPACE_SIZE in RI2, RI3. change (2^37) with 137438953472 in RI2, RI3.
      split; [| split; [| split]].
      - eapply aregion_cells_frame; [exact MU | exact WM | exact REG | subst st2; reflexivity | subst st2; reflexivity | subst st2; reflexivity | subst st2; reflexivity |].
        apply Kres; unfold aregion_info, ARI_STRIDE, K_SPACE_SIZE; change (2^37) with 137438953472; clear -Hc RSP; lia.
      - eapply afreearray_frame; [exact MU | exact WM | exact FARR | subst st2; reflexivity | subst st2; reflexivity | reflexivity | exact QLENF | exact Q5 | | clear -Q6; lia |].
        + apply Kres; unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX in *; [clear -RI1; lia | clear -Q5 Q6; lia | clear -RI2 RI3 Q6; lia].
        + apply Kres_sh; [apply shad_mono; unfold afreearr, K_FREEARR_OFF; clear -RI1; lia | apply shlen_nonneg; clear -Q5 Q6; lia |].
          rewrite <- shad_add_shlen by (unfold afreearr, K_FREEARR_OFF; clear -RM; Z.div_mod_to_equations; lia). apply shad_mono.
          unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX in *. clear -RI2 RI3 Q6. lia.
      - eapply (aslots_update L W' m m' MU WM st st2 X X c (-1)); [exact SLOTS | subst st2; reflexivity | subst st2; reflexivity | subst st2; reflexivity | | | intros Hk; exfalso; clear -Hk; lia].
        + intros k Hk _. pose proof (slot_in_region L st c k ltac:(clear -QS; lia) (proj1 Q1) Hk) as (P5 & P4 & P0).
          split; [reflexivity|]. split.
          * apply Kres; [clear -P5 RI1; lia | clear -QS; lia | clear -P4 Q1 Q2 RI2 RI3; unfold K_FREEARR_OFF in *; lia].
          * intros b Hb. pose proof Hb as Hb'. unfold busy_of in Hb'. apply find_some in Hb'. destruct Hb' as [HIn HP].
            apply andb_true_iff in HP. destruct HP as [HP1 HP2]. apply Z.eqb_eq in HP1. apply Z.eqb_eq in HP2.
            split; [exact HP1|]. split; [exact HP2|]. exact (awf_fits L st X b WF HIn).
        + intros POS. apply Kres; [clear -Q1 RI1; lia | clear -POS; lia | clear -Q1 Q2 RI2 RI3; unfold K_FREEARR_OFF in *; lia].
      - eapply (aslot_shadow_update L W' m m' MU WM st st2 X X c (-1)); [exact SHADOW | subst st2; reflexivity | subst st2; reflexivity | subst st2; reflexivity | | | intros Hk; exfalso; clear -Hk; lia | apply shlen_nonneg; clear -QS; lia].
        + intros k Hk _. pose proof (slot_in_region L st c k ltac:(clear -QS; lia) (proj1 Q1) Hk) as (P5 & P4 & P0).
          pose proof (slot_aligned L c k SAL ltac:(unfold K_NUM_CLASSES; clear -Hc; lia)) as AL.
          split; [reflexivity|]. apply Kres_sh; [apply shad_mono; clear -P5 RI1; lia | rewrite shlen_div; clear -QS QS16; Z.div_mod_to_equations; lia |].
          rewrite <- shad_add_shlen by (clear -AL; Z.div_mod_to_equations; lia). apply shad_mono. clear -P4 Q1 Q2 RI2 RI3. unfold K_FREEARR_OFF in *. lia.
        + intros POS. apply Kres_sh; [apply shad_mono; clear -Q1 RI1; lia | clear -POS; lia |].
          rewrite <- shad_add_shlen by (pose proof (mod16_of_class _ _ Q3 QS16 ltac:(clear -QS; lia)) as AM; clear -AM RM; Z.div_mod_to_equations; lia).
          apply shad_mono. clear -Q1 Q2 RI2 RI3. unfold K_FREEARR_OFF in *. lia. }
    split. {
      eapply (hq_frame _ HL L st st2 X X m m' W'); [exact HQ | exact MU | exact WM | |].
      - unfold quar_untouched. apply Forall_forall. intros iv Hin.
        unfold W' in Hin. apply List.filter_In in Hin. destruct Hin as [Hin NEV]. unfold nonempty in NEV. apply Z.ltb_lt in NEV.
        inWT Hin. all: unfold AINSTANCE in *.
        all: split; [clear -NEV CEIL LO OT OP AHI0 SA1 SA2 SA3 ON OS C_t D_t_p D_t_n D_t_s NS0 NS1 NS8 NS9 WB ABND AL1 OTs OTi ONs ONi OSs OSi OPs OPi; lia|].
        all: split; [clear -NEV CEIL LO OT OP AHI0 SA1 SA2 SA3 ON OS NS0 NS1 NS8 NS9 WB ABND AL1 OTs OTi ONs ONi OSs OSi OPs OPi; lia|].
        all: split; [clear -NEV CEIL LO OT OP AHI0 SA1 SA2 SA3 ON OS NS0 NS1 NS8 NS9 WB ABND AL1 OTs OTi ONs ONi OSs OSi OPs OPi; lia|].
        all: split; [clear -NEV CEIL LO OT OP AHI0 SA1 SA2 SA3 ON OS NS0 NS1 NS8 NS9 WB ABND AL1 OTs OTi ONs ONi OSs OSi OPs OPi; lia|].
        all: intros b Hb; destruct (BB b Hb) as [B1 B2]; destruct (xb_st b); [exact I| |];
          clear -NEV B1 B2 CEIL LO OT OP ORS AHI0 SA1 SA2 SA3 SR1 ON OS D_t_res D_p_res C_r D_n_res D_s_res NS0 NS1 NS8 NS9 WB ABND AL1 RHI OTs OTi ONs ONi OSs OSi OPs OPi; lia.
      - unfold quar_same. subst st2. rewrite E9, E10, E11, E12, E1. repeat (split; [reflexivity|]).
        split; intros b Hb; destruct (xb_st b); first [exact I | exact Hb]. }
    split. {
      unfold AHS, AH. cbn [ah_sec]. subst st2.
      pose proof (valid_buf RESV st n a FRSH) as VB. fold ms in VB.
      pose proof (WT_kinds L sp lo a ms _ _ _ WTF (sec_chunks_of st) st n VW) as VWK. fold W' in VWK.
      eapply (asec_append L W' m m' MU WM st X nres' a n id WF HS0 N PRIM VW VK NR' NRB VB VWK).
      - intros ch Hin. destruct (asec_wf_all L st _ ch WFS Hin) as (mb & ms' & n' & -> & W1c). cbn [sec_mb sec_ms].
        pose proof W1c as W0. cbn [sec_wf1] in W0. destruct W0 as (G1 & G2 & G3 & G4 & G5 & G6 & (Ct & Cc & Cr & Cp & Cn & Cs & Cf & Cd)).
        pose proof (proj1 (Forall_forall _ _) VK _ Hin) as D. cbn [sec_mb sec_ms] in D.
        pose proof (sec_facts n' ltac:(clear -G5; lia) G6) as (_ & _ & _ & _ & _ & _ & _ & _ & MSM' & MSB'). rewrite <- G4 in MSM', MSB'.
        destruct (ablk_int _ _ G2) as [kB GB].
        assert (SHc : 0x800be200 <= shad mb /\ shad mb + ms' / 8 = shad (mb + ms') /\ shad (mb + ms') <= 0x10007fef8000
                      /\ (shad (mb + ms') <= shad a \/ shad (a + ms) <= shad mb)).
        { rewrite !shad_div. unfold ASHOFF, K_HIGH_MEM in *. clear -G1 GB G3 MSM' D AAL MSM. Z.div_mod_to_equations. lia. }
        destruct SHc as (SC1 & SC2 & SC3 & SC4). unfold K_HIGH_MEM in *.
        split; intros A k H1 H2 H3.
        + apply Kobj; clear -H1 H2 H3 GB G3 Ct Cp Cn Cs D; lia.
        + apply Kshad; clear -H1 H2 H3 SC1 SC2 SC3 SC4; lia.
      - intros POS. apply KX; [clear -POS; lia|]. intros iv Hiv NEV. inWT Hiv; unfold AIMG_HI, AINSTANCE in *;
          clear -POS NEV CEIL LO OT OP AHI0 ON OS SA2 SA3 D_t_p C_p D_n_p D_s_p NS0 NS1 NS8 NS9 WB ABND AL1 SA1 OTs OTi ONs ONi OSs OSi OPs OPi; lia.
      - intros LT. apply KX; [clear -LT NS0; lia|]. intros iv Hiv NEV. inWT Hiv; unfold AIMG_HI, AINSTANCE in *;
          clear -LT NEV CEIL LO OT OP AHI0 ON OS SA2 SA3 D_t_p C_p D_n_p D_s_p NS0 NS1 NS8 NS9 WB ABND AL1 SA1 OTs OTi ONs ONi OSs OSi OPs OPi; lia.
      - apply Kimg; clear; unfold AIMG_HI, AINSTANCE; lia.
      - replace (shlen K_REGION) with 536870912 by reflexivity.
        apply Kres_sh; [apply shad_mono; clear -RSP; lia| clear; lia|].
        rewrite !shad_div. clear -RSP. Z.div_mod_to_equations. lia.
      - intros x Hx Hxa. unfold K_HIGH_MEM, KLS in Hx. unfold AIMG_HI in Hx.
        assert (SX : 2147446784 <= shad x /\ shad x + 1 <= 17594333495296) by (rewrite shad_div; unfold ASHOFF; clear -Hx; Z.div_mod_to_equations; lia).
        apply Kshad; [clear -SX; lia| clear; lia| clear -SX; lia|].
        destruct Hxa as [Hxa|Hxa]; [left; apply SAlt; exact Hxa| right; apply SAge; exact Hxa].
      - exact I128. - exact J136. - exact J168. - exact I680. - exact J704. - exact SLOT. - exact HDR. - exact PGJ. - exact MAG. - exact LCJ.
      - exact AHD. - exact IDR. - exact USR. - exact SHF. - exact SHU. - exact SHT. }
    split; [exact DEP|].
    split; [eapply arelro_frame; [exact MU | exact HRO | apply Kimg; clear; unfold ARELRO_LO, ARELRO_HI, AIMG_HI, AINSTANCE; lia]|].
    split; [eapply arep_rt2_frame; [exact MU | exact WM | exact RT2 | | |]; apply Kimg; clear; unfold AIMG_HI, AINSTANCE; lia|].
    split; [| eapply arep_rt3_frame; [exact MU | exact WM | exact RT3 |]; unfold rt3_hulls;
              repeat (apply Forall_cons; [cbn [fst snd]; apply Kimg; clear; unfold AIMG_HI, AINSTANCE; lia |]); apply Forall_nil].
    intros c Hc. destruct (PERC c Hc) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & _). unfold K_NUM_CLASSES in Hc.
    assert (RI : al_res L <= aregion L c /\ aregion L c + K_REGION <= al_space_beg L + K_SPACE_SIZE
                 /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104).
    { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc RSP. lia. }
    destruct RI as (RI1 & RI2 & RI3). unfold K_REGION, K_SPACE_SIZE in RI2, RI3. change (2^37) with 137438953472 in RI2, RI3.
    eapply (ashadow_avail_frame L W' m m' MU WM st); [exact (AVL c ltac:(unfold K_NUM_CLASSES; clear -Hc; lia)) | subst st2; reflexivity | subst st2; reflexivity | |].
    - intros POS. apply Kres_sh; [apply shad_mono; unfold aregion in *; clear -Q1 RI1; lia | clear -POS; lia |].
      rewrite <- shad_add_shlen by (pose proof (aregion_mod L c SAL) as RM; clear -RM Q4; unfold K_USER_MAP in *; Z.div_mod_to_equations; lia).
      apply shad_mono. unfold K_FREEARR_OFF, K_REGION in *. clear -Q1 Q2 RI2 RI3. lia.
    - intros POS. apply Kres_sh; [apply shad_mono; unfold afreearr, K_FREEARR_OFF, aregion in *; clear -Q5 Q6 RI1; lia | clear -POS; lia |].
      rewrite <- shad_add_shlen by (pose proof (aregion_mod L c SAL) as RM; unfold afreearr, K_FREEARR_OFF; clear -RM Q7; unfold K_FREEARR_MAP in *; Z.div_mod_to_equations; lia).
      apply shad_mono. unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -Q5 Q6 RI2 RI3. lia. }

  assert (SHFK : 0x800be200 <= shad (al_fake L) /\ shad (al_fake L) + shlen 11571200 = shad (al_fake L + 11571200)
                 /\ shad (al_fake L + 11571200) <= 0x10007fef8000
                 /\ (shad (a + ms) <= shad (al_fake L) \/ shad (al_fake L + 11571200) <= shad a)).
  { rewrite !shad_div, shlen_div. unfold ASHOFF in *. clear -OFK C_f AAL OFKs OFKi. Z.div_mod_to_equations. lia. }
  destruct SHFK as (SF1 & SF2 & SF3 & SF4).
  assert (FKD : forall cls FA sz, In (mkABlock (ABFake cls) FA sz) LB -> al_fake L <= FA /\ 0 <= sz /\ FA + sz <= al_fake L + 11571200)
    by (intros cls FA sz Hin; exact (proj1 (proj2 BL) cls FA sz Hin)).
  split.
  -
    intros x Hx CL. split; [| intros Hw; apply WM; exact Hw]. apply MU. rewrite wa_unsigned by exact Hx.
    destruct CL as [STa | [CIa | [BLK | SH]]].
    + eapply (disjoint_outside W' x 1); [| clear; lia]. apply KX; [clear; lia|]. intros iv Hiv NEV. inWT Hiv; unfold AIMG_HI, AINSTANCE in *;
        clear -STa NEV CEIL LO OT OP AHI0 ACE ON OS SA2 SA3 NS0 NS1 NS8 NS9 WB SP47 ABND AL1 SA1 OTs OTi ONs ONi OSs OSi OPs OPi; lia.
    + destruct CIa as (iv & Hiv & R). pose proof (proj1 (Forall_forall _ _) CI_OK iv Hiv) as (Q1 & Q2 & Q3).
      pose proof (proj1 (Forall_forall _ _) CI_OK2 iv Hiv) as Q4. cbn [fst snd] in *.
      eapply disjoint_outside; [eapply (Kimg x 1); unfold AIMG_HI, AINSTANCE in *; clear -R Q1 Q2 Q3 Q4; lia | clear; lia].
    + destruct BLK as (b & Hb & R). destruct b as [[p|cls] A n']; cbn [ab_addr ab_size] in R.
      * destruct (proj1 BL p A n' Hb) as [(xb & Hxb & Sb & Ub & Nb)|(mb0 & ms0 & Lp & EUA & Gs)].
        -- destruct (BB xb Hxb) as [Bb1 Bb2].
           pose proof (awf_fits L st X xb WF Hxb) as FIT. unfold xb_fits in FIT. rewrite Sb in FIT. unfold xb_user in Ub. subst A n'.
           eapply disjoint_outside; [eapply (Kres x 1) | clear; lia]; clear -R Bb1 Bb2 FIT; lia.
        --
           assert (Hin : In (CSec mb0 ms0 n') (sec_chunks_of st)).
           { unfold sec_chunks_of, achunks. apply List.filter_In. split; [| reflexivity]. apply in_app_iff. left.
             apply in_map_iff. exists (p, CSec mb0 ms0 n'). split; [reflexivity|]. apply list_elem_of_In. apply elem_of_map_to_list. exact Lp. }
           pose proof (proj1 (Forall_forall _ _) VK _ Hin) as D. cbn [sec_mb sec_ms] in D.
           cbn [sec_wf1] in Gs. destruct Gs as (Gs1 & Gs2 & Gs3 & Gs4 & Gs5 & Gs6 & (Ct & Cc & Cr & Cp & Cn & Cs & Cf & Cd)).
           pose proof (sec_facts n' ltac:(clear -Gs5; lia) Gs6) as SFc. subst A. unfold SEC_UOFF, K_HIGH_MEM in *.
           destruct (ablk_int _ _ Gs2) as [kB GB].
           eapply disjoint_outside; [eapply (Kobj x 1) | clear; lia]; clear -R GB Gs3 Gs4 Gs5 SFc Ct Cp Cn Cs D; lia.
      * destruct (FKD cls A n' Hb) as (K1 & K2 & K3). atop_facts.
        eapply disjoint_outside; [eapply (Kobj x 1) | clear; lia]; clear -R K1 K3 OFK D_t_f D_f_p C_f D_n_f D_s_f OFKs OFKi; lia.
    + destruct SH as (x' & Hx' & ->).
      destruct Hx' as [STa | [CIa | FK]].
      * assert (SX : shad (a + ms) <= shad x' /\ shad x' + 1 <= 17594333495296).
        { split; [apply SAge; atop_facts; clear -STa ACE; lia|]. rewrite shad_div. unfold ASHOFF. clear -STa. Z.div_mod_to_equations. lia. }
        eapply disjoint_outside; [eapply (Kshad (shad x') 1); clear -SX SA1 SA2 MSB; lia | clear; lia].
      * destruct CIa as (iv & Hiv & R). pose proof (proj1 (Forall_forall _ _) CI_OK iv Hiv) as (Q1 & Q2 & Q3). cbn [fst snd] in *.
        assert (SX : 2147446784 <= shad x' /\ shad x' + 1 <= 0x800be200) by (rewrite shad_div; unfold ASHOFF, AIMG_HI in *; clear -R Q1 Q3; Z.div_mod_to_equations; lia).
        eapply disjoint_outside; [eapply (Kshad (shad x') 1); clear -SX SA1; lia | clear; lia].
      * destruct FK as (cls & FA & sz & Hin & R). destruct (FKD cls FA sz Hin) as (K1 & K2 & K3).
        assert (SX : shad (al_fake L) <= shad x' /\ shad x' + 1 <= shad (al_fake L + 11571200)).
        { rewrite !shad_div. clear -R K1 K3 OFK OFKs OFKi. Z.div_mod_to_equations. lia. }
        eapply disjoint_outside; [eapply (Kshad (shad x') 1) | clear; lia]; clear -SX SF1 SF3 SF4; lia.
  -
    split; [exact ALO|].
    split; [eapply (arng_sec L RNG RNG' st X); [exact WF| exact ARNG| exact FPLE| exact RA| exact RSA| exact RPA']|].
    split; [exists X; split; [exact AR'| replace (a + 6144) with (a + SEC_UOFF) by reflexivity; apply ablocks_sec; [exact WF| exact BL| exact VW]]|].
    unfold AHS, AH. cbn [ah_fake].
    eapply (hf_blocks _ HL L LB); [eapply (hf_frame _ HL L LB m m'); [exact HFK | exact MU | exact WM | apply Kt; clear; lia |] |].
    + unfold fake_untouched. apply Forall_forall. intros iv Hin.
      unfold W' in Hin. apply List.filter_In in Hin. destruct Hin as [Hin NEV]. unfold nonempty in NEV. apply Z.ltb_lt in NEV.
      inWT Hin. all: unfold AINSTANCE in *.
      all: clear -NEV CEIL LO OT OP OFK OD AHI0 ACE SA1 SA2 SA3 SF1 SF2 SF3 SF4 ON OS D_t_f D_t_d D_f_p D_d_p C_f C_d D_n_f D_s_f D_n_d D_s_d NS0 NS1 NS8 NS9 WB ABND AL1 OTs OTi ONs ONi OSs OSi OPs OPi OFKs OFKi ODs ODi.

      all: first [ lazymatch goal with
                   | |- context [al_t _] => clear D_f_p D_d_p C_f C_d D_n_f D_s_f D_n_d D_s_d
                   | |- context [al_ptr_array _] => clear D_t_f D_t_d C_f C_d D_n_f D_s_f D_n_d D_s_d
                   | |- context [al_nodes _] => clear D_t_f D_t_d D_f_p D_d_p C_f C_d D_s_f D_s_d
                   | |- context [al_store _] => clear D_t_f D_t_d D_f_p D_d_p C_f C_d D_n_f D_n_d
                   | |- _ => clear D_t_f D_t_d D_f_p D_d_p D_n_f D_s_f D_n_d D_s_d
                   end; repeat (split; [lia|]); lia
                 | repeat (split; [lia|]); lia ].
    + intros c F n'. split; [intros H; cbn [In] in H; destruct H as [H|H]; [discriminate H| exact H]| intros H; cbn [In]; right; exact H].
Qed.
End Store.
End CANSEC1.
End ASecStore.
End TwinB.
