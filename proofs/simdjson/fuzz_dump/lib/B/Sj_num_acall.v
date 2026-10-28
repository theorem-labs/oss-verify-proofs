(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.P Require Import Sj_num_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout RT_iface D_defs D_kit Sj_akit Sj_acps Sj_hkit Sj_rtf Sj_num_akit Sj_num_amem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section ACall.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RTF : rt_contracts_f RT.
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.

Lemma acc_of_zr : forall (m : mem) U kk a n, U mod 8 = 0 -> 0 <= U ->
  bytes_at bsegs m (U / 8 + 2147450880) (repeat (Z_to_bv 8 0) kk) -> U <= a -> a + n <= U + 8 * Z.of_nat kk -> acc bsegs m a n.
Proof.
  intros m U kk a n U8 U0 ZR H1 H2. eapply acc_sub; [exact (acc_zero_run bsegs m U kk U8 U0 ZR)| exact H1| exact H2].
Qed.

Section Obj.
  Variables (Σ : rts RT) (K : config -> Prop) (m : mem) (U : Z) (ubs : list byte) (kk : nat) (lo : Z) (sp : word).
  Hypothesis UA : u8arr bsegs m U ubs.
  Hypothesis U8 : U mod 8 = 0.
  Hypothesis U0 : 0 < U.
  Hypothesis ULO : U + Z.of_nat (length ubs) <= lo.
  Hypothesis UKK : Z.of_nat (length ubs) <= 8 * Z.of_nat kk.
  Hypothesis ULEN : Z.of_nat (length ubs) < 2^40.
  Hypothesis ZR : bytes_at bsegs m (U / 8 + 2147450880) (repeat (Z_to_bv 8 0) kk).
  Hypothesis UFR : exists f c, In (f, c) (rt_frames RT Σ) /\ f <= U /\ U + Z.of_nat (length ubs) <= f + fs_size c - 8.
  Hypothesis ART0 : ART RT Σ m.
  Hypothesis MI0 : mem_inv bsegs m.
  Hypothesis COK : call_ok RT Σ m sp lo.

  Lemma obj_chk : forall a n, 0 <= n -> U <= a -> a + n <= U + Z.of_nat (length ubs) ->
    checked_src RT Σ m sp lo a n /\ checked_dst RT Σ m sp a n.
  Proof using UA U8 U0 ULO UKK ZR UFR.
    intros a n N0 A1 A2. destruct UFR as (f & c & Hin & F1 & F2).
    assert (AC : acc bsegs m a n) by (eapply acc_of_zr; [exact U8| lia| exact ZR| exact A1| lia]).
    assert (RC : rng_class RT Σ a n) by (right; left; exists f, c; split; [exact Hin| lia]).
    split.
    - split; [intros _; split; [exact AC| exact RC]| left; lia].
    - split; [intros _; split; [exact AC| exact RC]|]. split.
      + intros i Hi. right; right; right; left. exists f, c. split; [exact Hin| lia].
      + destruct UA as [_ (W0 & W1 & WW)]. split; [lia|]. split; [lia|]. intros i Hi.
        replace (a + i) with (U + (a - U + i)) by lia. apply WW. lia.
  Qed.

  Lemma aevt_memmove_u8 : forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (dz sz nz : Z),
    a0 = Z_to_bv 64 (U + dz) -> a1 = Z_to_bv 64 (U + sz) -> a2 = Z_to_bv 64 nz ->
    0 <= dz -> 0 <= sz -> 0 <= nz -> dz + nz <= Z.of_nat (length ubs) -> sz + nz <= Z.of_nat (length ubs) -> lo <= 2^47 -> frm0 fc ->
    (forall t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' ubs', frm0 fc' ->
       rt_after RT Σ (bv_unsigned sp) lo m m' -> rt_pres_ex (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (U + dz) nz m m' ->
       u8arr bsegs m' U ubs' -> length ubs' = length ubs ->
       aevt RT PMc Σ K (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (U + dz)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                           F' (ret_pc ra) fc' None m' (seg_rom bsegs))) ->
    aevt RT PMc Σ K (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 0x7ef54) fc None m (seg_rom bsegs)).
  Proof using AF RTF FDO MST UA U8 U0 ULO UKK ULEN ZR UFR ART0 MI0 COK.
    intros until nz. intros E0 E1 E2 D0 S0 N0 DN SN LO47 FRM HK.
    destruct (u8arr_range_split bsegs m U ubs (Z.to_nat dz) (Z.to_nat (dz + nz)) UA ltac:(lia) ltac:(lia))
      as (b1 & mid & b3 & L1 & LM & L3 & U1 & MID & U3).
    rewrite Z2Nat.id in MID, U3 by lia.
    set (bs := firstn (Z.to_nat nz) (skipn (Z.to_nat sz) ubs)).
    assert (BL : Z.of_nat (length bs) = nz) by (unfold bs; rewrite length_firstn, length_skipn; lia).
    assert (SRC : bytes_at bsegs m (U + sz) bs).
    { pose proof (bytes_at_sub bsegs m U ubs (Z.to_nat sz) (Z.to_nat nz) (proj1 UA) ltac:(lia)) as H. rewrite Z2Nat.id in H by lia. exact H. }
    destruct (obj_chk (U + sz) nz N0 ltac:(lia) ltac:(lia)) as [CS _]. destruct (obj_chk (U + dz) nz N0 ltac:(lia) ltac:(lia)) as [_ CD].
    eapply (aevt_memmove RT RTF PMc FDO MST Σ K ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m (U + dz) (U + sz) bs lo);
      rewrite ?BL; [exact E0| exact E1| exact E2| lia| lia| lia| exact SRC| exact CS| exact CD| exact ART0| exact MI0| exact COK| exact FRM|].
    intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' FRM' RA PR BY.
    pose proof RA as (_ & _ & WM' & _).
    destruct UFR as (f & c & Hin & F1 & F2).
    pose proof (agree_of_pres_ex _ _ _ _ _ m m' (fun x => aclient (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) x /\ ~ (U + dz <= x < U + dz + nz)) PR (fun x H => H)) as AG.
    assert (U1' : u8arr bsegs m' U b1).
    { apply (u8arr_agree m m' U b1 U1); [| exact WM']. eapply agree_sub; [exact AG|]. intros x Hx. cbv beta.
      split; [right; right; right; left; exists f, c; split; [exact Hin| lia]| lia]. }
    assert (U3' : u8arr bsegs m' (U + (dz + nz)) b3).
    { apply (u8arr_agree m m' _ b3 U3); [| exact WM']. eapply agree_sub; [exact AG|]. intros x Hx. cbv beta.
      split; [right; right; right; left; exists f, c; split; [exact Hin| lia]| lia]. }
    assert (MID' : rw_cells bsegs m' (U + Z.of_nat (length b1)) [CB (Z.to_nat nz) bs]).
    { replace (Z.to_nat nz) with (length bs) by lia. replace (U + Z.of_nat (length b1)) with (U + dz) by lia.
      apply rw_cells_CB_intro; [exact BY|]. rewrite BL. apply (wr_at_transport bsegs m m' _ _ (proj2 (proj2 CD)) WM'). }
    replace (U + (dz + nz)) with (U + Z.of_nat (length b1) + Z.of_nat (Z.to_nat nz)) in U3' by lia.
    destruct (u8arr_range_join bsegs m' U b1 _ _ b3 U1' MID' U3') as (ubs' & LJ & UA').
    eapply HK; [exact FRM'| exact RA| exact PR| exact UA'| lia].
  Qed.

  Lemma aevt_memset_u8 : forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (dz nz : Z) (cb : byte),
    a0 = Z_to_bv 64 (U + dz) -> a1 = Z_to_bv 64 (bv_unsigned cb) -> a2 = Z_to_bv 64 nz ->
    0 <= dz -> 0 <= nz -> dz + nz <= Z.of_nat (length ubs) -> lo <= 2^47 -> frm0 fc ->
    (forall t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' ubs', frm0 fc' ->
       rt_after RT Σ (bv_unsigned sp) lo m m' -> rt_pres_ex (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (U + dz) nz m m' ->
       u8arr bsegs m' U ubs' -> length ubs' = length ubs ->
       aevt RT PMc Σ K (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (U + dz)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                           F' (ret_pc ra) fc' None m' (seg_rom bsegs))) ->
    aevt RT PMc Σ K (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 0x7ed14) fc None m (seg_rom bsegs)).
  Proof using AF RTF FDO MST UA U8 U0 ULO UKK ULEN ZR UFR ART0 MI0 COK.
    intros until cb. intros E0 E1 E2 D0 N0 DN LO47 FRM HK.
    destruct (u8arr_range_split bsegs m U ubs (Z.to_nat dz) (Z.to_nat (dz + nz)) UA ltac:(lia) ltac:(lia))
      as (b1 & mid & b3 & L1 & LM & L3 & U1 & MID & U3).
    rewrite Z2Nat.id in MID, U3 by lia.
    destruct (obj_chk (U + dz) nz N0 ltac:(lia) ltac:(lia)) as [_ CD].
    eapply (aevt_memset RT RTF PMc FDO MST Σ K ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m (U + dz) nz cb lo);
      [exact E0| exact E1| exact E2| lia| lia| exact CD| exact ART0| exact MI0| exact COK| exact FRM|].
    intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' FRM' RA PR BY.
    pose proof RA as (_ & _ & WM' & _).
    destruct UFR as (f & c & Hin & F1 & F2).
    pose proof (agree_of_pres_ex _ _ _ _ _ m m' (fun x => aclient (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) x /\ ~ (U + dz <= x < U + dz + nz)) PR (fun x H => H)) as AG.
    assert (U1' : u8arr bsegs m' U b1).
    { apply (u8arr_agree m m' U b1 U1); [| exact WM']. eapply agree_sub; [exact AG|]. intros x Hx. cbv beta.
      split; [right; right; right; left; exists f, c; split; [exact Hin| lia]| lia]. }
    assert (U3' : u8arr bsegs m' (U + (dz + nz)) b3).
    { apply (u8arr_agree m m' _ b3 U3); [| exact WM']. eapply agree_sub; [exact AG|]. intros x Hx. cbv beta.
      split; [right; right; right; left; exists f, c; split; [exact Hin| lia]| lia]. }
    assert (MID' : rw_cells bsegs m' (U + Z.of_nat (length b1)) [CB (Z.to_nat nz) (repeat cb (Z.to_nat nz))]).
    { replace (U + Z.of_nat (length b1)) with (U + dz) by lia.
      pose proof (rw_cells_CB_intro m' (U + dz) (repeat cb (Z.to_nat nz)) BY) as H. rewrite repeat_length in H. apply H.
      rewrite Z2Nat.id by lia. apply (wr_at_transport bsegs m m' _ _ (proj2 (proj2 CD)) WM'). }
    replace (U + (dz + nz)) with (U + Z.of_nat (length b1) + Z.of_nat (Z.to_nat nz)) in U3' by lia.
    destruct (u8arr_range_join bsegs m' U b1 _ _ b3 U1' MID' U3') as (ubs' & LJ & UA').
    eapply HK; [exact FRM'| exact RA| exact PR| exact UA'| lia].
  Qed.
End Obj.
End ACall.
