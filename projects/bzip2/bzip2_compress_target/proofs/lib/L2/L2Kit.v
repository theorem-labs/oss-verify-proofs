(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require PropExec KBridge.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require MState Mem Cells Step Frame Arr Exec SegsA0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.A Require Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import ShapeAlg.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec ImageA RzCPS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Layout Shadow RT_iface D_defs D_kit D_clx I_lkit I_read I_lift.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.

(* [comment removed for export] *)
Module NExec := OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.Exec.
Module NMem := OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.Mem.
Module NCells := OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.Cells.
Module NStep := OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.Step.
Module NFrame := OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.Frame.
Module NArr := OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.Arr.
Module NShadow := OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.A.Shadow.
Abbreviation a0segs := OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.SegsA0.a0segs.
#[local] Notation mem := (word -> option byte).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma evt_N2K : forall Q ms, NExec.evt a0segs Q ms -> evt asegs Q ms.
Proof. intros Q ms H. exact (proj1 (KBridge.evt_NK a0segs Q ms) H). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma kmem_inv_N : forall segs (m : mem), mem_inv segs m -> NMem.mem_inv segs m.
Proof. intros segs m H a b E. exact (mem_inv_ro segs m a b H E). Qed.

Lemma outside_dec : forall W x, outside W x \/ ~ outside W x.
Proof.
  induction W as [|[lo hi] W IH]; intros x; cbn [outside]; [left; exact I|].
  destruct (IH x) as [H|H]; [| right; tauto].
  destruct (Z_lt_dec x lo) as [L|L]; [left; split; [lia| exact H]|].
  destruct (Z_le_dec hi x) as [G|G]; [left; split; [lia| exact H]| right; intros [C _]; lia].
Qed.

(* [comment removed for export] *)
Fixpoint fp_below (W : list (Z * Z)) (top : Z) : Prop :=
  match W with [] => True | (lo, hi) :: W' => hi <= top /\ fp_below W' top end.
Lemma fp_below_in : forall W top x, fp_below W top -> ~ outside W x -> x < top.
Proof.
  induction W as [|[lo hi] W IH]; intros top x HB HO; cbn in *; [exfalso; apply HO; exact I|].
  destruct HB as [B1 B2]. destruct (Z_lt_dec x hi) as [L|L]; [lia|].
  apply (IH top x B2). intros O. apply HO. split; [lia| exact O].
Qed.

(* [comment removed for export] *)
Lemma kmem_inv_munch : forall segs W (m m' : mem), mem_inv segs m -> munch W m m' -> NMem.mem_inv segs m' -> fp_below W UTOP ->
  mem_inv segs m'.
Proof.
  intros segs W m m' H MU HN HB. apply mem_inv_intro.
  - intros a E. exact (mem_inv_seg_below segs m a H E).
  - intros a b E. split; [exact (HN a b E)|].
    destruct (outside_dec W (bv_unsigned a)) as [O|O].
    + rewrite (MU a O) in E. exact (mem_inv_ov_below segs m a b H E).
    + exact (fp_below_in W UTOP _ HB O).
Qed.

(* [comment removed for export] *)
Lemma agree_of_nmunch : forall W (m m' : mem) (P : Z -> Prop), NFrame.munch W m m' -> (forall x, P x -> outside W x) -> agree_on P m m'.
Proof. intros W m m' P H HP a Ha. exact (H a (HP _ Ha)). Qed.

(* [comment removed for export] *)
Lemma kmem_inv_munch' : forall segs W (m m' : mem), mem_inv segs m -> munch W m m' -> NMem.mem_inv segs m' ->
  (forall x, ~ outside W x -> x < UTOP) -> mem_inv segs m'.
Proof.
  intros segs W m m' H MU HN HB. apply mem_inv_intro.
  - intros a E. exact (mem_inv_seg_below segs m a H E).
  - intros a b E. split; [exact (HN a b E)|].
    destruct (outside_dec W (bv_unsigned a)) as [O|O].
    + rewrite (MU a O) in E. exact (mem_inv_ov_below segs m a b H E).
    + exact (HB _ O).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section NAgree.
Variable segs : list Segment.

Lemma n_cells_at_agree : forall (m m' : mem) a cs, NCells.cells_at segs m a cs ->
  agree_on (fun x => a <= x < a + Z.of_nat (NCells.cells_size cs)) m m' -> NCells.cells_at segs m' a cs.
Proof.
  intros m m' a cs [Hwf Hb] HA. split; [exact Hwf|]. apply (bytes_at_agree segs m m' a _ Hb).
  rewrite NCells.cells_bytes_length by exact Hwf. exact HA.
Qed.
Lemma n_ro_cells_agree : forall (m m' : mem) a cs, NStep.ro_cells segs m a cs ->
  agree_on (fun x => a <= x < a + Z.of_nat (NCells.cells_size cs)) m m' -> NStep.ro_cells segs m' a cs.
Proof. intros m m' a cs H HA. exact (n_cells_at_agree m m' a cs H HA). Qed.
Lemma n_rw_cells_agree : forall (m m' : mem) a cs, NStep.rw_cells segs m a cs ->
  agree_on (fun x => a <= x < a + Z.of_nat (NCells.cells_size cs)) m m' -> NStep.rw_cells segs m' a cs.
Proof.
  intros m m' a cs [Hc Hw] HA. split; [exact (n_cells_at_agree m m' a cs Hc HA)|]. exact (wr_at_agree_nw segs m m' a _ Hw HA).
Qed.
Lemma n_u8arr_agree : forall (m m' : mem) a bs, NArr.u8arr segs m a bs ->
  agree_on (fun x => a <= x < a + Z.of_nat (length bs)) m m' -> NArr.u8arr segs m' a bs.
Proof.
  intros m m' a bs [Hb Hw] HA. split; [exact (bytes_at_agree segs m m' a _ Hb HA)|]. exact (wr_at_agree_nw segs m m' a _ Hw HA).
Qed.
Lemma n_u32arr_agree : forall (m m' : mem) a ws, NArr.u32arr segs m a ws ->
  agree_on (fun x => a <= x < a + 4 * Z.of_nat (length ws)) m m' -> NArr.u32arr segs m' a ws.
Proof.
  intros m m' a ws [Hb Hw] HA. split.
  - apply (bytes_at_agree segs m m' a _ Hb). rewrite NArr.u32s_length. eapply agree_sub; [exact HA|]. intros x Hx. cbv beta in *. lia.
  - apply (wr_at_agree_nw segs m m' a _ Hw). eapply agree_sub; [exact HA|]. intros x Hx. cbv beta in *. lia.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma n_u8arr_bytes : forall (m : mem) a bs, NArr.u8arr segs m a bs -> bytes_at segs m a bs /\ wr_at segs m a (Z.of_nat (length bs)).
Proof. intros m a bs H. exact H. Qed.
Lemma n_rw_cells_bytes : forall (m : mem) a cs, NStep.rw_cells segs m a cs ->
  bytes_at segs m a (NCells.cells_bytes cs) /\ wr_at segs m a (Z.of_nat (NCells.cells_size cs)).
Proof. intros m a cs [[_ Hb] Hw]. exact (conj Hb Hw). Qed.
End NAgree.

(* [comment removed for export] *)
Lemma ro_C8_KN : forall (m : mem) A v, ro_cells asegs m A [C8 v] -> NStep.ro_cells a0segs m A [NCells.C8 v].
Proof. intros m A v [Hwf Hb]. split; [cbn; tauto| exact Hb]. Qed.
Lemma ro_C4_KN : forall (m : mem) A v, ro_cells asegs m A [C4 v] -> NStep.ro_cells a0segs m A [NCells.C4 v].
Proof. intros m A v [Hwf Hb]. split; [cbn; tauto| exact Hb]. Qed.

(* [comment removed for export] *)
Lemma n_wr_at_rw_CB : forall (m : mem) d n, wr_at asegs m d n -> 0 <= n -> exists junk, NStep.rw_cells a0segs m d [NCells.CB (Z.to_nat n) junk].
Proof.
  intros m d n W Hn. destruct (wr_at_rw_CB m d n W Hn) as (junk & [[Hwf Hb] Hw]). exists junk.
  cbn in Hwf. destruct Hwf as [L _]. cbn [cells_bytes cbytes cells_size csize Nat.add] in Hb, Hw. rewrite app_nil_r in Hb.
  split; [split|].
  - cbn. split; [exact L| exact I].
  - cbn [NCells.cells_bytes NCells.cbytes]. rewrite app_nil_r. exact Hb.
  - cbn [NCells.cells_size NCells.csize Nat.add]. exact Hw.
Qed.
Lemma wr_at_sub : forall segs (m : mem) a n a' n', wr_at segs m a n -> a <= a' -> a' + n' <= a + n -> 0 <= n' -> wr_at segs m a' n'.
Proof.
  intros segs m a n a' n' (W1 & W2 & W3) H1 H2 H3. split; [lia| split; [lia|]].
  intros i Hi. replace (a' + i) with (a + (a' - a + i)) by lia. apply W3. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma acc_sub : forall segs (m : mem) a n a' n', acc segs m a n -> a <= a' -> a' + n' <= a + n -> acc segs m a' n'.
Proof.
  intros segs m a n a' n' H H1 H2 i Hi. destruct (H (a' - a + i) ltac:(lia)) as (b & Hb & Hok).
  replace (a + (a' - a + i)) with (a' + i) in * by lia. exists b. split; [exact Hb| exact Hok].
Qed.
(* [comment removed for export] *)
Lemma acc_of_zero_shadow : forall segs (m : mem) F SHF q k, F mod 8 = 0 -> SHF = F / 8 + 2147450880 -> 0 <= F -> 0 <= q ->
  bytes_at segs m (SHF + q) (repeat z8 k) -> acc segs m (F + 8 * q) (8 * Z.of_nat k).
Proof.
  intros segs m F SHF q k HF -> H0 Hq HB.
  apply acc_ushadow; [| lia| lia|].
  - rewrite Z.add_mod, HF by lia. rewrite (Z.mul_comm 8 q), Z.mod_mul by lia. reflexivity.
  - unfold shad, SHB, ushadow. replace ((F + 8 * q) / 8) with (F / 8 + q).
    2:{ rewrite (Z.mul_comm 8 q), Z.div_add by lia. reflexivity. }
    replace (8 * Z.of_nat k / 8) with (Z.of_nat k) by (rewrite Z.mul_comm, Z.div_mul by lia; reflexivity).
    replace (8 * Z.of_nat k mod 8) with 0 by (rewrite Z.mul_comm, Z.mod_mul by lia; reflexivity).
    cbn [Z.eqb]. rewrite Nat2Z.id, app_nil_r. replace (F / 8 + q + 2147450880) with (F / 8 + 2147450880 + q) by lia. exact HB.
Qed.

(* [comment removed for export] *)
Lemma aclient_mono : forall live frames sp live' frames' sp' a,
  aclient live frames sp a -> (forall e, In e live -> In e live') -> (forall e, In e frames -> In e frames') -> sp' <= sp ->
  aclient live' frames' sp' a.
Proof.
  intros live frames sp live' frames' sp' a H HL HF Hsp. destruct H as [H|[H|[H|[H|H]]]].
  - left. lia.
  - right; left. exact H.
  - right; right; left. destruct H as (p & n & Hin & Hp). exists p, n. split; [apply HL; exact Hin| exact Hp].
  - right; right; right; left. destruct H as (f & k & Hin & Hf). exists f, k. split; [apply HF; exact Hin| exact Hf].
  - right; right; right; right. destruct H as (f & k & Hin & Hf). exists f, k. split; [apply HF; exact Hin| exact Hf].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Glue.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.

(* [comment removed for export] *)
Lemma l1_lift : forall (Σ : rts RT) PMc (Q : machine_state -> Prop) ms0, mat_stable PMc -> NExec.evt a0segs Q ms0 ->
  cps asegs (ASTA RT Σ PMc (eq ms0)) (ASTA RT Σ PMc Q).
Proof. intros Σ PMc Q ms0 MST H. apply (asta_evt' RT AF Σ PMc (eq ms0) Q MST). intros ms <-. exact (evt_N2K Q ms0 H). Qed.

(* [comment removed for export] *)
Lemma l1_realizes : forall (Σ : rts RT) PMc ms0 T c, mat_stable PMc -> ASTA RT Σ PMc (eq ms0) c ->
  NExec.evt a0segs (fun ms => forall c', ASTA RT Σ PMc (eq ms) c' -> realizes asegs c' T) ms0 -> realizes asegs c T.
Proof.
  intros Σ PMc ms0 T c MST Hc H. refine (cps_realizes asegs _ _ T c (l1_lift Σ PMc _ ms0 MST H) Hc _).
  intros c' Hc'. destruct (ASTA_unpack RT Σ _ _ c' Hc') as (ms & HQ & Hc''). exact (HQ c' Hc'').
Qed.

(* [comment removed for export] *)
Lemma art_of_munch : forall (Σ : rts RT) (m m' : mem) W sp, ART RT Σ m -> rt_sp0 RT Σ - STACK_WIN <= sp ->
  munch W m m' -> wmono asegs m m' ->
  (forall x, ~ outside W x -> aclient (rt_live RT Σ) (rt_frames RT Σ) sp x) -> ART RT Σ m'.
Proof.
  intros Σ m m' W sp ART0 HS MU WM HW. apply (af_frame RT AF Σ m m' sp ART0 HS); [| exact WM].
  intros a Ha. apply MU. destruct (outside_dec W (bv_unsigned a)) as [O|O]; [exact O| exfalso; exact (Ha (HW _ O))].
Qed.

(* [comment removed for export] *)
Lemma newframe_apart : forall (Σ Σ1 : rts RT) (m1 : mem) Fr k usp a,
  ART RT Σ1 m1 -> rt_frames RT Σ1 = (Fr, k) :: rt_frames RT Σ -> rt_live RT Σ1 = rt_live RT Σ -> rt_sp0 RT Σ1 = rt_sp0 RT Σ ->
  rt_sp0 RT Σ - STACK_WIN <= usp -> aclient (rt_live RT Σ) (rt_frames RT Σ) usp a ->
  ~ (Fr <= a < Fr + fs_size k) /\ ~ (shad Fr <= a < shad (Fr + fs_size k)).
Proof.
  intros Σ Σ1 m1 Fr k usp a ART1 FRS LV SP0 LU Ha.
  assert (INF : In (Fr, k) (rt_frames RT Σ1)) by (rewrite FRS; left; reflexivity).
  pose proof (af_frames_range RT AF Σ1 m1 Fr k ART1 INF) as (R0 & R1 & R2 & R3).
  pose proof (af_fshadow_apart RT AF Σ1 m1 Fr k ART1 INF) as (SL & SF).
  pose proof (af_sp0_range RT AF Σ1 m1 ART1) as SPR. pose proof (af_sp0_win RT AF Σ1 m1 ART1) as SPW.
  rewrite SP0 in R1, SPR, SPW.
  assert (FSZ : 0 <= fs_size k) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
  assert (SH1 : shad (Fr + fs_size k) <= 2^44 + SHB).
  { unfold shad. assert ((Fr + fs_size k) / 8 <= 2^44) by (apply Z.div_le_upper_bound; unfold STACK_WIN, USTACK_TOP in *; lia). lia. }
  assert (SH0 : SHB <= shad Fr) by (unfold shad; assert (0 <= Fr / 8) by (apply Z.div_pos; lia); lia).
  assert (SHM : shad Fr <= shad (Fr + fs_size k)) by (unfold shad; pose proof (Z.div_le_mono Fr (Fr + fs_size k) 8 ltac:(lia) ltac:(lia)); lia).
  destruct Ha as [H|[H|[H|[H|H]]]].
  - split; unfold SHB, STACK_WIN, USTACK_TOP in *; lia.
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
Lemma not_outside_cons : forall lo hi W x (P : Prop), (lo <= x < hi -> P) -> (~ outside W x -> P) -> ~ outside ((lo, hi) :: W) x -> P.
Proof.
  intros lo hi W x P H1 H2 HO. destruct (Z_lt_dec x lo) as [L|L].
  - apply H2. intros O. apply HO. split; [lia| exact O].
  - destruct (Z_le_dec hi x) as [G|G]; [| apply H1; lia]. apply H2. intros O. apply HO. split; [lia| exact O].
Qed.
Lemma not_outside_nil : forall x (P : Prop), ~ outside [] x -> P.
Proof. intros x P H. exfalso. apply H. exact I. Qed.

End Glue.

(* [comment removed for export] *)
Ltac per_interval_go :=
  first [ refine (not_outside_cons _ _ _ _ _ _ _); [ intro | per_interval_go ] | refine (not_outside_nil _ _) ].
Ltac per_interval :=
  let x := fresh "x" in let HO := fresh "HO" in
  intros x HO; revert HO; per_interval_go.
