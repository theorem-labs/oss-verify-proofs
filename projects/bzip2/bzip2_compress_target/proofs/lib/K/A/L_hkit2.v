(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require ShapeAlg AsanAcct.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Tac ImageA RzCPS NodesA SysStep.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Layout RT_iface R_unwind_chain D_defs D_kit D_clx D_libiface I_lkit I_lift L_hkit L_harn_defs.
Module TwinB__.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import Tac ImageA RzCPS NodesA SysStep.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Shadow.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.Layout.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_iface.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_unwind_chain.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_kit.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_clx.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_libiface.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.I_lkit.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.I_lift.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_hkit.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_harn_defs.TwinB__.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma live_remove_notin : forall p (l : list (Z * Z)), (forall e, In e l -> fst e <> p) -> live_remove p l = l.
Proof.
  intros p l H. induction l as [|e l IH]; [reflexivity|]. unfold live_remove in *. cbn.
  assert (E : (fst e =? p) = false) by (apply Z.eqb_neq; apply H; left; reflexivity).
  rewrite E. cbn. destruct (stdpp.base.decide True) as [_|N]; [| exfalso; apply N; exact I].
  f_equal. apply IH. intros e' He'. apply H. right. exact He'.
Qed.

Lemma live_remove_head : forall p n (l : list (Z * Z)), (forall e, In e l -> fst e <> p) -> live_remove p ((p, n) :: l) = l.
Proof.
  intros p n l H. unfold live_remove. cbn. rewrite Z.eqb_refl. cbn.
  destruct (stdpp.base.decide False) as [N|_]; [destruct N|]. exact (live_remove_notin p l H).
Qed.

Lemma live_remove_cons_keep : forall p e (l : list (Z * Z)), fst e <> p -> live_remove p (e :: l) = e :: live_remove p l.
Proof.
  intros p e l H. unfold live_remove. cbn. rewrite (proj2 (Z.eqb_neq _ _) H). cbn.
  destruct (stdpp.base.decide True) as [_|N]; [reflexivity| exfalso; apply N; exact I].
Qed.

Lemma rw_cells_recast' : forall (m : mem) A cs cs', rw_cells bsegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs ->
  rw_cells bsegs m A cs'.
Proof.
  intros m A cs cs' [[W B] R] W' E. split; [split; [exact W'| rewrite E; exact B]|].
  rewrite <- (cells_bytes_length cs' W'), E, (cells_bytes_length cs W). exact R.
Qed.

(* [comment removed for export] *)
Lemma stk_wmono' : forall (m m' : mem) lo hi, stk bsegs m lo hi -> wmono bsegs m m' -> stk bsegs m' lo hi.
Proof.
  intros m m' lo hi (H0 & H1 & H) W. split; [exact H0|]. split; [exact H1|]. intros a Ha.
  destruct (H a Ha) as [Hw _]. pose proof (W _ Hw) as Hw'. split; [exact Hw'| exact (wview_mrd_A m' _ Hw')].
Qed.

Lemma rw_cells_stk' : forall (m : mem) a cs hi, a + Z.of_nat (cells_size cs) = hi -> rw_cells bsegs m a cs -> stk bsegs m a hi.
Proof.
  intros m a cs hi E [_ (H0 & H1 & H)]. split; [lia|]. split; [lia|]. intros x Hx. pose proof (H (x - a) ltac:(lia)) as W.
  replace (a + (x - a)) with x in W by lia. split; [exact W | exact (wview_mrd_A m _ W)].
Qed.

(* [comment removed for export] *)
Lemma harn_site : forall r, In r [0x81434; 0x814c8; 0x8150c; 0x81514] -> In [r; RA_HARN] SITE_TRACES.
Proof.
  intros r Hr. unfold SITE_TRACES. apply in_or_app. right. unfold RA_HARN.
  destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn; tauto.
Qed.

Section Kit2.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.

(* [comment removed for export] *)
Lemma ASTA_switch : forall (Σ Σ' : rts RT) PMc Pm c, ASTA RT Σ PMc Pm c -> rt_allow RT Σ' = rt_allow RT Σ ->
  (forall mo, ARTM RT Σ mo -> ARTM RT Σ' mo) -> ASTA RT Σ' PMc Pm c.
Proof.
  intros Σ Σ' PMc Pm c H HA HM. unfold ASTA in *. rewrite HA.
  eapply AST_conseq; [exact H| auto|]. intros mo [H1 H2]. split; [apply HM; exact H1| exact H2].
Qed.

(* [comment removed for export] *)
Lemma newframe_apart : forall (Σ Σ1 : rts RT) (m1 : mem) Fr k usp a,
  ART RT Σ1 m1 -> rt_frames RT Σ1 = (Fr, k) :: rt_frames RT Σ -> rt_live RT Σ1 = rt_live RT Σ -> rt_sp0 RT Σ1 = rt_sp0 RT Σ ->
  rt_sp0 RT Σ - STACK_WIN <= usp -> aclient (rt_live RT Σ) (rt_frames RT Σ) usp a ->
  ~ (Fr <= a < Fr + fs_size k) /\ ~ (shad Fr <= a < shad (Fr + fs_size k)).
Proof using AF.
  intros Σ Σ1 m1 Fr k usp a ART1 FRS LV SP0 LU Ha.
  assert (INF : In (Fr, k) (rt_frames RT Σ1)) by (rewrite FRS; left; reflexivity).
  pose proof (af_frames_range RT AF Σ1 m1 Fr k ART1 INF) as (R0 & R1 & R2 & R3).
  pose proof (af_fshadow_apart RT AF Σ1 m1 Fr k ART1 INF) as (SL & SF).
  pose proof (af_sp0_range RT AF Σ1 m1 ART1) as SPR. pose proof (af_sp0_win RT AF Σ1 m1 ART1) as SPW.
  rewrite SP0 in R1, SPR, SPW.
  assert (FSZ : 0 <= fs_size k) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
  assert (SH1 : shad (Fr + fs_size k) <= 2^44 + SHB).
  { unfold shad. assert ((Fr + fs_size k) / 8 <= 2^44) by (apply Z.div_le_upper_bound; ul). lia. }
  assert (SH0 : SHB <= shad Fr) by (unfold shad; assert (0 <= Fr / 8) by (apply Z.div_pos; lia); lia).
  assert (SHM : shad Fr <= shad (Fr + fs_size k)) by (unfold shad; pose proof (Z.div_le_mono Fr (Fr + fs_size k) 8 ltac:(lia) ltac:(lia)); lia).
  destruct Ha as [H|[H|[H|[H|H]]]].
  - split; unfold SHB in *; ul.
  - pose proof (client_static_range a H). split; [destruct R2; unfold SEGTOP_A in *; lia|]. unfold SHB, SEGTOP_A in *. lia.
  - destruct H as (p & n & Hin & Hp). rewrite <- LV in Hin. destruct (R3 p n Hin); destruct (SL p n Hin); split; lia.
  - destruct H as (f & k' & Hin & Hf).
    destruct (af_frames_disj RT AF Σ1 m1 Fr k f k' [] (rt_frames RT Σ) ART1 FRS Hin) as [D|D];
      (destruct (SF f k' ltac:(rewrite FRS; right; exact Hin)) as [E|E]); split; lia.
  - destruct H as (f & k' & Hin & Hf).
    assert (INf : In (f, k') (rt_frames RT Σ1)) by (rewrite FRS; right; exact Hin).
    pose proof (af_fshadow_apart RT AF Σ1 m1 f k' ART1 INf) as (_ & SF').
    destruct (af_frames_disj RT AF Σ1 m1 Fr k f k' [] (rt_frames RT Σ) ART1 FRS Hin) as [D|D].
    + pose proof (Z.div_le_mono (Fr + fs_size k) f 8 ltac:(lia) D). destruct (SF' Fr k INF) as [E|E]; split; unfold shad in *; lia.
    + assert (FSZ' : 0 <= fs_size k') by (unfold fs_size; apply Z.shiftl_nonneg; lia).
      pose proof (Z.div_le_mono (f + fs_size k') Fr 8 ltac:(lia) D). destruct (SF' Fr k INF) as [E|E]; split; unfold shad in *; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

End Kit2.
End TwinB__.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import Tac ImageA RzCPS NodesA SysStep.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Layout Shadow RT_iface R_unwind_chain D_defs D_kit D_clx D_libiface I_lkit I_lift L_hkit L_harn_defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma live_remove_notin : forall p (l : list (Z * Z)), (forall e, In e l -> fst e <> p) -> live_remove p l = l.
Proof.
  intros p l H. induction l as [|e l IH]; [reflexivity|]. unfold live_remove in *. cbn.
  assert (E : (fst e =? p) = false) by (apply Z.eqb_neq; apply H; left; reflexivity).
  rewrite E. cbn. destruct (stdpp.base.decide True) as [_|N]; [| exfalso; apply N; exact I].
  f_equal. apply IH. intros e' He'. apply H. right. exact He'.
Qed.

Lemma live_remove_head : forall p n (l : list (Z * Z)), (forall e, In e l -> fst e <> p) -> live_remove p ((p, n) :: l) = l.
Proof.
  intros p n l H. unfold live_remove. cbn. rewrite Z.eqb_refl. cbn.
  destruct (stdpp.base.decide False) as [N|_]; [destruct N|]. exact (live_remove_notin p l H).
Qed.

Lemma live_remove_cons_keep : forall p e (l : list (Z * Z)), fst e <> p -> live_remove p (e :: l) = e :: live_remove p l.
Proof.
  intros p e l H. unfold live_remove. cbn. rewrite (proj2 (Z.eqb_neq _ _) H). cbn.
  destruct (stdpp.base.decide True) as [_|N]; [reflexivity| exfalso; apply N; exact I].
Qed.

Lemma rw_cells_recast' : forall (m : mem) A cs cs', rw_cells asegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs ->
  rw_cells asegs m A cs'.
Proof.
  intros m A cs cs' [[W B] R] W' E. split; [split; [exact W'| rewrite E; exact B]|].
  rewrite <- (cells_bytes_length cs' W'), E, (cells_bytes_length cs W). exact R.
Qed.

(* [comment removed for export] *)
Lemma stk_wmono' : forall (m m' : mem) lo hi, stk asegs m lo hi -> wmono asegs m m' -> stk asegs m' lo hi.
Proof.
  intros m m' lo hi (H0 & H1 & H) W. split; [exact H0|]. split; [exact H1|]. intros a Ha.
  destruct (H a Ha) as [Hw _]. pose proof (W _ Hw) as Hw'. split; [exact Hw'| exact (wview_mrd_A m' _ Hw')].
Qed.

Lemma rw_cells_stk' : forall (m : mem) a cs hi, a + Z.of_nat (cells_size cs) = hi -> rw_cells asegs m a cs -> stk asegs m a hi.
Proof.
  intros m a cs hi E [_ (H0 & H1 & H)]. split; [lia|]. split; [lia|]. intros x Hx. pose proof (H (x - a) ltac:(lia)) as W.
  replace (a + (x - a)) with x in W by lia. split; [exact W | exact (wview_mrd_A m _ W)].
Qed.

(* [comment removed for export] *)
Lemma harn_site : forall r, In r [0x819e8; 0x81a7c; 0x81ac0; 0x81ac8] -> In [r; RA_HARN] SITE_TRACES.
Proof.
  intros r Hr. unfold SITE_TRACES. apply in_or_app. right. unfold RA_HARN.
  destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn; tauto.
Qed.

Section Kit2.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.

(* [comment removed for export] *)
Lemma ASTA_switch : forall (Σ Σ' : rts RT) PMc Pm c, ASTA RT Σ PMc Pm c -> rt_allow RT Σ' = rt_allow RT Σ ->
  (forall mo, ARTM RT Σ mo -> ARTM RT Σ' mo) -> ASTA RT Σ' PMc Pm c.
Proof.
  intros Σ Σ' PMc Pm c H HA HM. unfold ASTA in *. rewrite HA.
  eapply AST_conseq; [exact H| auto|]. intros mo [H1 H2]. split; [apply HM; exact H1| exact H2].
Qed.

(* [comment removed for export] *)
Lemma newframe_apart : forall (Σ Σ1 : rts RT) (m1 : mem) Fr k usp a,
  ART RT Σ1 m1 -> rt_frames RT Σ1 = (Fr, k) :: rt_frames RT Σ -> rt_live RT Σ1 = rt_live RT Σ -> rt_sp0 RT Σ1 = rt_sp0 RT Σ ->
  rt_sp0 RT Σ - STACK_WIN <= usp -> aclient (rt_live RT Σ) (rt_frames RT Σ) usp a ->
  ~ (Fr <= a < Fr + fs_size k) /\ ~ (shad Fr <= a < shad (Fr + fs_size k)).
Proof using AF.
  intros Σ Σ1 m1 Fr k usp a ART1 FRS LV SP0 LU Ha.
  assert (INF : In (Fr, k) (rt_frames RT Σ1)) by (rewrite FRS; left; reflexivity).
  pose proof (af_frames_range RT AF Σ1 m1 Fr k ART1 INF) as (R0 & R1 & R2 & R3).
  pose proof (af_fshadow_apart RT AF Σ1 m1 Fr k ART1 INF) as (SL & SF).
  pose proof (af_sp0_range RT AF Σ1 m1 ART1) as SPR. pose proof (af_sp0_win RT AF Σ1 m1 ART1) as SPW.
  rewrite SP0 in R1, SPR, SPW.
  assert (FSZ : 0 <= fs_size k) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
  assert (SH1 : shad (Fr + fs_size k) <= 2^44 + SHB).
  { unfold shad. assert ((Fr + fs_size k) / 8 <= 2^44) by (apply Z.div_le_upper_bound; ul). lia. }
  assert (SH0 : SHB <= shad Fr) by (unfold shad; assert (0 <= Fr / 8) by (apply Z.div_pos; lia); lia).
  assert (SHM : shad Fr <= shad (Fr + fs_size k)) by (unfold shad; pose proof (Z.div_le_mono Fr (Fr + fs_size k) 8 ltac:(lia) ltac:(lia)); lia).
  destruct Ha as [H|[H|[H|[H|H]]]].
  - split; unfold SHB in *; ul.
  - pose proof (client_static_range a H). split; [destruct R2; unfold SEGTOP_A in *; lia|]. unfold SHB, SEGTOP_A in *. lia.
  - destruct H as (p & n & Hin & Hp). rewrite <- LV in Hin. destruct (R3 p n Hin); destruct (SL p n Hin); split; lia.
  - destruct H as (f & k' & Hin & Hf).
    destruct (af_frames_disj RT AF Σ1 m1 Fr k f k' [] (rt_frames RT Σ) ART1 FRS Hin) as [D|D];
      (destruct (SF f k' ltac:(rewrite FRS; right; exact Hin)) as [E|E]); split; lia.
  - destruct H as (f & k' & Hin & Hf).
    assert (INf : In (f, k') (rt_frames RT Σ1)) by (rewrite FRS; right; exact Hin).
    pose proof (af_fshadow_apart RT AF Σ1 m1 f k' ART1 INf) as (_ & SF').
    destruct (af_frames_disj RT AF Σ1 m1 Fr k f k' [] (rt_frames RT Σ) ART1 FRS Hin) as [D|D].
    + pose proof (Z.div_le_mono (Fr + fs_size k) f 8 ltac:(lia) D). destruct (SF' Fr k INF) as [E|E]; split; unfold shad in *; lia.
    + assert (FSZ' : 0 <= fs_size k') by (unfold fs_size; apply Z.shiftl_nonneg; lia).
      pose proof (Z.div_le_mono (f + fs_size k') Fr 8 ltac:(lia) D). destruct (SF' Fr k INF) as [E|E]; split; unfold shad in *; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

End Kit2.
