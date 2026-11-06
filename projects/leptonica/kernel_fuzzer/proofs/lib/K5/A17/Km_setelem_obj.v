(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.A17 Require Import ImageA.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.Lib Require Import RzCPS NodesA Arr.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.A17 Require Import Layout.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.A17 Require Import RT_iface RT_traces RT_gaps_iface D_kit Lept_kit Lept_iface Lept_objkit LeptC_kit Km_setelem Km_iface Km_kit D_iface D_defs.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Lemma kel_obj_setword : forall live (m m' : mem) kel sy sx cy cx data rows (i j : Z) r,
  kel_obj live m kel sy sx cy cx data rows -> nth_error rows (Z.to_nat i) = Some r -> 0 <= i -> 0 <= j < sx ->
  (forall p1 n1 p2 n2, In (p1, n1) live -> In (p2, n2) live -> p1 <> p2 -> p1 + n1 <= p2 \/ p2 + n2 <= p1) ->
  (forall a : word, in_live live (bv_unsigned a) -> ~ (r + 4 * j <= bv_unsigned a < r + 4 * j + 4) -> m' a = m a) ->
  wmono asegs m m' ->
  kel_obj live m' kel sy sx cy cx data rows.
Proof.
  intros live m m' kel sy sx cy cx data rows i j r (KC & KCH & DA & DCH & LEN & ROWS & ND & SYB & SXB) NR Hi Hj LAP AG WM.
  pose proof (nth_error_In _ _ NR) as RIN. pose proof ROWS as ROWS'. rewrite Forall_forall in ROWS'.
  pose proof (ROWS' r RIN) as ((RI & R0 & R16 & RN) & _).
  pose proof KCH as (KI & K0 & K16 & KN). pose proof DCH as (DI & D0 & D16 & DN).
  pose proof ND as ND0. apply List.NoDup_cons_iff in ND0 as (NK & ND1). apply List.NoDup_cons_iff in ND1 as (NDd & NDR).
  assert (KR : kel <> r) by (intro E; apply NK; right; rewrite E; exact RIN).
  assert (DR : data <> r) by (intro E; apply NDd; rewrite E; exact RIN).
  pose proof (LAP kel 24 r (4 * sx) KI RI KR) as AKR. pose proof (LAP data (8 * sy) r (4 * sx) DI RI DR) as ADR.
  (* [comment removed for export] *)
  assert (AGC : forall p n, In (p, n) live -> (p + n <= r \/ r + 4 * sx <= p) -> agree_on (fun a => p <= a < p + n) m m').
  { intros p n Hin Hap a Ha. apply AG; [exists p, n; split; [exact Hin| exact Ha]| lia]. }
  split; [apply (rw_cells_agree_nw asegs m m' kel _ KC); eapply agree_sub; [exact (AGC kel 24 KI AKR)|]; cbn; intros z Hz; lia|].
  split; [exact KCH|].
  split; [apply (u64arr_agree_nw asegs m m' data _ DA); eapply agree_sub; [exact (AGC data (8 * sy) DI ADR)|];
          rewrite length_map; intros z Hz; cbv beta in *; lia|].
  split; [exact DCH|]. split; [exact LEN|]. split; [| exact (conj ND (conj SYB SXB))].
  eapply Forall_impl; [| exact ROWS]. intros r' (RCH' & RW'). split; [exact RCH'| exact (wr_at_transport asegs m m' r' _ RW' WM)].
Qed.

Section SETELEM_OBJ.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.

Definition kernelSetElement_obj_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (kel sy sx cy cx data : Z) (rows : list Z) (i j r : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 kel -> a1 = Z_to_bv 64 i -> a2 = Z_to_bv 64 j -> 0 <= i < sy -> 0 <= j < sx ->
  kel_obj (rt_live RT Σ) m kel sy sx cy cx data rows -> nth_error rows (Z.to_nat i) = Some r ->
  lenv RT Σ m sp lo (LSTK 1) ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_kernelSetElement m)))
    (fun c => exists (Σ' : rts RT),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [(r + 4 * j, r + 4 * j + 4)] m m'
          /\ kel_obj (rt_live RT Σ) m' kel sy sx cy cx data rows) c
       /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ).

Lemma kernelSetElement_obj_ok : kernelSetElement_cps RT -> kernelSetElement_obj_cps.
Proof using AF.
  intros KSE Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    kel sy sx cy cx data rows i j r FDO MST TP A0 A1 A2 IB JB KOBJ NR ENV.
  pose proof KOBJ as (KC & KCH & DA & DCH & LEN & ROWS & ND & SYB & SXB).
  pose proof (nth_error_In _ _ NR) as RIN. pose proof ROWS as ROWS'. rewrite Forall_forall in ROWS'.
  pose proof (ROWS' r RIN) as (RCH & RW).
  destruct (wr_at_cell4 m r (4 * sx) j RW ltac:(lia) ltac:(lia)) as (x0 & RC).
  pose proof (u64arr_cell m data (map (Z_to_bv 64) rows) i (Z_to_bv 64 r) DA ltac:(rewrite nth_error_map, NR; reflexivity) ltac:(lia)) as DC.
  pose proof ENV as (_ & _ & ART0 & _).
  eapply cps_conseq.
  - exact (KSE Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
             kel sy sx cy cx data i j r x0 FDO MST TP A0 A1 A2 IB JB (proj2 SYB) (proj2 SXB) KC KCH DC DCH RC RCH ENV).
  - intros c Hc; exact Hc.
  - intros c (Σ' & HA & LV & FR & SP & CR). exists Σ'.
    split; [| repeat split; assumption].
    eapply (ASTA_conseq RT); [exact HA|]. intros ms (m' & RS & LP & KP & (x & RC')).
    exists m'. split; [exact RS|]. split; [exact LP|]. split; [exact KP|].
    pose proof LP as ((_ & _ & WM & _) & _).
    apply (kel_obj_setword (rt_live RT Σ) m m' kel sy sx cy cx data rows i j r KOBJ NR ltac:(lia) JB).
    + intros p1 n1 p2 n2 H1 H2 NE. exact (live_apart RT AF Σ m p1 n1 p2 n2 ART0 H1 H2 NE).
    + intros a Ha Hn. unfold keeps, keepsL in KP. apply KP.
      * rewrite LV. right; right; left. exact Ha.
      * cbn [outside]. split; [exact Hn| exact I].
    + exact WM.
Qed.
End SETELEM_OBJ.

(* [comment removed for export] *)
Lemma km_chunk_mono : forall live live' p n, (forall e, In e live -> In e live') -> chunk live p n -> chunk live' p n.
Proof. intros live live' p n S (H1 & H2). exact (conj (S _ H1) H2). Qed.
Lemma km_cmap_obj_mono : forall live live' (m : mem) cmap cv, (forall e, In e live -> In e live') ->
  cmap_obj live m cmap cv -> cmap_obj live' m cmap cv.
Proof.
  intros live live' m cmap cv S (C & CH1 & CH2 & R).
  exact (conj C (conj (km_chunk_mono _ _ _ _ S CH1) (conj (km_chunk_mono _ _ _ _ S CH2) R))).
Qed.
Lemma km_pix_obj_mono : forall live live' (m : mem) pix v cv, (forall e, In e live -> In e live') ->
  pix_obj live m pix v cv -> pix_obj live' m pix v cv.
Proof.
  intros live live' m pix v cv S (C & CH & HOK & HD & HCM).
  split; [exact C| split; [exact (km_chunk_mono _ _ _ _ S CH)| split; [exact HOK| split]]].
  - destruct HD as [HD|(HD & R)]; [left; exact HD| right; exact (conj (km_chunk_mono _ _ _ _ S HD) R)].
  - destruct HCM as [HCM|(HCM & R)]; [left; exact HCM| right; exact (conj (km_cmap_obj_mono _ _ _ _ _ S HCM) R)].
Qed.

(* [comment removed for export] *)
Lemma kel_obj_cells : forall live (m m' : mem) kel sy sx cy cx cy' cx' data rows,
  kel_obj live m kel sy sx cy cx data rows ->
  rw_cells asegs m' kel (kel_cells sy sx cy' cx' data) ->
  agree_on (fun a => data <= a < data + 8 * sy) m m' -> wmono asegs m m' ->
  kel_obj live m' kel sy sx cy' cx' data rows.
Proof.
  intros live m m' kel sy sx cy cx cy' cx' data rows (KC & KCH & DA & DCH & LEN & ROWS & ND & SYB & SXB) KC' AG WM.
  split; [exact KC'|]. split; [exact KCH|].
  split; [apply (u64arr_agree_nw asegs m m' data _ DA); eapply agree_sub; [exact AG|]; rewrite length_map; intros z Hz; cbv beta in *; lia|].
  split; [exact DCH|]. split; [exact LEN|]. split; [| exact (conj ND (conj SYB SXB))].
  eapply Forall_impl; [| exact ROWS]. intros r' (RCH' & RW'). split; [exact RCH'| exact (wr_at_transport asegs m m' r' _ RW' WM)].
Qed.
