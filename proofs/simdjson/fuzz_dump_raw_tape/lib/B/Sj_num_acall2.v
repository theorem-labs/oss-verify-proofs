(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.P Require Import Sj_num_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout RT_iface D_defs D_kit Sj_akit Sj_acps Sj_hkit Sj_rtf Sj_num_akit Sj_num_amem Sj_num_acall.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma zero_run_of_cells : forall (m : mem) A cs k, rw_cells bsegs m A cs -> cells_bytes cs = repeat (Z_to_bv 8 0) k ->
  bytes_at bsegs m A (repeat (Z_to_bv 8 0) k).
Proof. intros m A cs k H E. rewrite <- E. exact (rw_cells_bytes_at bsegs m A cs H). Qed.

Section ACall2.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RTF : rt_contracts_f RT.
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.

Section Obj2.
  Variables (Σ : rts RT) (K : config -> Prop) (m : mem) (lo : Z) (sp : word).

  Variables (U : Z) (ubs : list byte) (kk : nat).
  Hypothesis UA : u8arr bsegs m U ubs.
  Hypothesis U8 : U mod 8 = 0.
  Hypothesis U0 : 0 < U.
  Hypothesis ULO : U + Z.of_nat (length ubs) <= lo.
  Hypothesis UKK : Z.of_nat (length ubs) <= 8 * Z.of_nat kk.
  Hypothesis ULEN : Z.of_nat (length ubs) < 2^40.
  Hypothesis ZRU : bytes_at bsegs m (U / 8 + 2147450880) (repeat (Z_to_bv 8 0) kk).
  Hypothesis UFR : exists f c, In (f, c) (rt_frames RT Σ) /\ f <= U /\ U + Z.of_nat (length ubs) <= f + fs_size c - 8.

  Variables (V : Z) (vbs : list byte) (kv : nat).
  Hypothesis VA : u8arr bsegs m V vbs.
  Hypothesis V8 : V mod 8 = 0.
  Hypothesis V0 : 0 < V.
  Hypothesis VLO : V + Z.of_nat (length vbs) <= lo.
  Hypothesis VKK : Z.of_nat (length vbs) <= 8 * Z.of_nat kv.
  Hypothesis ZRV : bytes_at bsegs m (V / 8 + 2147450880) (repeat (Z_to_bv 8 0) kv).
  Hypothesis VFR : exists f c, In (f, c) (rt_frames RT Σ) /\ f <= V /\ V + Z.of_nat (length vbs) <= f + fs_size c - 8.
  Hypothesis ART0 : ART RT Σ m.
  Hypothesis MI0 : mem_inv bsegs m.
  Hypothesis COK : call_ok RT Σ m sp lo.

  Lemma aevt_memcpy_u8 : forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (nz : Z),
    a0 = Z_to_bv 64 U -> a1 = Z_to_bv 64 V -> a2 = Z_to_bv 64 nz ->
    0 <= nz -> nz <= Z.of_nat (length ubs) -> nz <= Z.of_nat (length vbs) -> (U + nz <= V \/ V + nz <= U) -> lo <= 2^47 -> frm0 fc ->
    (forall t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' ubs', frm0 fc' ->
       rt_after RT Σ (bv_unsigned sp) lo m m' -> rt_pres_ex (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) U nz m m' ->
       u8arr bsegs m' U ubs' -> length ubs' = length ubs ->
       aevt RT PMc Σ K (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 U) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                           F' (ret_pc ra) fc' None m' (seg_rom bsegs))) ->
    aevt RT PMc Σ K (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 0x7ee9c) fc None m (seg_rom bsegs)).
  Proof using AF RTF FDO MST UA U8 U0 ULO UKK ULEN ZRU UFR VA V8 V0 VLO VKK ZRV VFR ART0 MI0 COK.
    intros until nz. intros E0 E1 E2 N0 NU NV DJ LO47 FRM HK.
    destruct (u8arr_range_split bsegs m U ubs 0%nat (Z.to_nat nz) UA ltac:(lia) ltac:(lia))
      as (b1 & mid & b3 & L1 & LM & L3 & U1 & MID & U3).
    rewrite Z2Nat.id in U3 by lia. change (Z.of_nat 0) with 0 in MID. rewrite Z.add_0_r in MID. rewrite Nat.sub_0_r in MID.
    set (bs := firstn (Z.to_nat nz) vbs).
    assert (BL : Z.of_nat (length bs) = nz) by (unfold bs; rewrite length_firstn; lia).
    assert (SRC : bytes_at bsegs m V bs).
    { pose proof (bytes_at_sub bsegs m V vbs 0%nat (Z.to_nat nz) (proj1 VA) ltac:(lia)) as H.
      change (Z.of_nat 0) with 0 in H. rewrite Z.add_0_r in H. cbn [skipn] in H. exact H. }
    destruct (obj_chk RT Σ m V vbs kv lo sp VA V8 V0 VLO VKK ZRV VFR V nz N0 ltac:(lia) ltac:(lia)) as [CS _].
    destruct (obj_chk RT Σ m U ubs kk lo sp UA U8 U0 ULO UKK ZRU UFR U nz N0 ltac:(lia) ltac:(lia)) as [_ CD].
    eapply (aevt_memcpy RT RTF PMc FDO MST Σ K ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m U V bs lo);
      rewrite ?BL; [exact E0| exact E1| exact E2| lia| lia| lia| exact SRC| exact CS| exact CD| exact DJ| exact ART0| exact MI0| exact COK| exact FRM|].
    intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' FRM' RA PR BY.
    pose proof RA as (_ & _ & WM' & _).
    destruct UFR as (f & c & Hin & F1 & F2).
    pose proof (agree_of_pres_ex _ _ _ _ _ m m' (fun x => aclient (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) x /\ ~ (U <= x < U + nz)) PR (fun x H => H)) as AG.
    assert (U3' : u8arr bsegs m' (U + nz) b3).
    { apply (u8arr_agree m m' _ b3 U3); [| exact WM']. eapply agree_sub; [exact AG|]. intros x Hx. cbv beta.
      split; [right; right; right; left; exists f, c; split; [exact Hin| lia]| lia]. }
    assert (MID' : rw_cells bsegs m' U [CB (Z.to_nat nz) bs]).
    { replace (Z.to_nat nz) with (length bs) by lia.
      apply rw_cells_CB_intro; [exact BY|]. rewrite BL. apply (wr_at_transport bsegs m m' _ _ (proj2 (proj2 CD)) WM'). }
    assert (UA' : u8arr bsegs m' U (bs ++ b3)).
    { apply u8arr_app; [exact (u8arr_of_rw_cells bsegs m' U _ bs MID')|]. rewrite BL. exact U3'. }
    eapply HK; [exact FRM'| exact RA| exact PR| exact UA'|].
    rewrite length_app. apply Nat2Z.inj. rewrite Nat2Z.inj_add. lia.
  Qed.
End Obj2.
End ACall2.
