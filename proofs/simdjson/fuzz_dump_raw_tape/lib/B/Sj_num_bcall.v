(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Sj Require Import SjNumber.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.P Require Import Rnd Sj_num_kit Sj_num_walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout RT_iface D_defs D_kit D_clx Sj_akit Sj_acps Sj_hkit Sj_rtf Sj_num_akit Sj_num_amem Sj_num_bkit Sj_num_acall.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma zr_munch : forall W (m m' : mem) S k, bytes_at bsegs m S (repeat (Z_to_bv 8 0) k) ->
  (forall a, S <= a < S + Z.of_nat k -> outside W a) -> munch W m m' -> bytes_at bsegs m' S (repeat (Z_to_bv 8 0) k).
Proof.
  intros W m m' S k ZR OUT MU. apply (bytes_at_agree bsegs m m' S _ ZR).
  apply (agree_of_munch W m m' _ MU). intros x Hx. rewrite repeat_length in Hx. exact (OUT x Hx).
Qed.

Lemma shzp_zr : forall W (m : mem) X k, bytes_at bsegs m (X / 8 + 2147450880) (repeat (Z_to_bv 8 0) k) -> X mod 8 = 0 -> 0 <= X ->
  (forall a, X / 8 + 2147450880 <= a < X / 8 + 2147450880 + Z.of_nat k -> outside W a) ->
  forall m', munch W m m' -> wmono bsegs m m' -> shz m' X (8 * Z.of_nat k).
Proof.
  intros W m X k ZR X8 X0 OUT m' MU _. apply (shz_run0 m' X k X8 X0). exact (zr_munch W m m' _ k ZR OUT MU).
Qed.

Lemma limbz_app_mid : forall (b1 mid b3 : list byte) (j : Z), 0 <= j -> j + 8 <= Z.of_nat (length mid) ->
  limbz (b1 ++ mid ++ b3) (Z.of_nat (length b1) + j) = limbz mid j.
Proof.
  intros b1 mid b3 j J0 J8. unfold limbz. f_equal.
  replace (Z.to_nat (Z.of_nat (length b1) + j)) with (length b1 + Z.to_nat j)%nat by lia.
  rewrite skipn_app. rewrite skipn_all2 by lia. cbn [app].
  replace (length b1 + Z.to_nat j - length b1)%nat with (Z.to_nat j) by lia.
  rewrite skipn_app. rewrite firstn_app.
  replace (8 - length (skipn (Z.to_nat j) mid))%nat with 0%nat by (rewrite length_skipn; lia).
  cbn [firstn]. rewrite app_nil_r. reflexivity.
Qed.

Lemma limbz_sub : forall (bs : list byte) (s n j : Z), 0 <= s -> 0 <= j -> j + 8 <= n -> s + n <= Z.of_nat (length bs) ->
  limbz (firstn (Z.to_nat n) (skipn (Z.to_nat s) bs)) j = limbz bs (s + j).
Proof.
  intros bs s n j S0 J0 J8 SN. unfold limbz. f_equal.
  rewrite skipn_firstn_comm. rewrite firstn_firstn. replace (Init.Nat.min 8 (Z.to_nat n - Z.to_nat j)) with 8%nat by lia.
  rewrite skipn_skipn. replace (Z.to_nat j + Z.to_nat s)%nat with (Z.to_nat (s + j)) by lia. reflexivity.
Qed.

Section BCall.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RTF : rt_contracts_f RT.
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.

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

  Lemma aevt_memmove_u8N : forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (dz sz nz : Z),
    a0 = Z_to_bv 64 (U + dz) -> a1 = Z_to_bv 64 (U + sz) -> a2 = Z_to_bv 64 nz ->
    0 <= dz -> 0 <= sz -> 0 <= nz -> dz + nz <= Z.of_nat (length ubs) -> sz + nz <= Z.of_nat (length ubs) -> lo <= 2^47 -> frm0 fc ->
    (forall t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' ubs', frm0 fc' ->
       rt_after RT Σ (bv_unsigned sp) lo m m' -> rt_pres_ex (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (U + dz) nz m m' ->
       u8arr bsegs m' U ubs' -> length ubs' = length ubs ->
       (8 <= nz -> limbz ubs' (dz + nz - 8) = limbz ubs (sz + nz - 8)) ->
       aevt RT PMc Σ K (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (U + dz)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                           F' (ret_pc ra) fc' None m' (seg_rom bsegs))) ->
    aevt RT PMc Σ K (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 0x7f578) fc None m (seg_rom bsegs)).
  Proof using AF RTF FDO MST UA U8 U0 ULO UKK ULEN ZR UFR ART0 MI0 COK.
    intros until nz. intros E0 E1 E2 D0 S0 N0 DN SN LO47 FRM HK.
    destruct UA as [UB UW].
    set (b1 := firstn (Z.to_nat dz) ubs). set (b3 := skipn (Z.to_nat (dz + nz)) ubs).
    set (bs := firstn (Z.to_nat nz) (skipn (Z.to_nat sz) ubs)).
    assert (L1 : Z.of_nat (length b1) = dz) by (unfold b1; rewrite length_firstn; lia).
    assert (L3 : Z.of_nat (length b3) = Z.of_nat (length ubs) - (dz + nz)) by (unfold b3; rewrite length_skipn; lia).
    assert (BL : Z.of_nat (length bs) = nz) by (unfold bs; rewrite length_firstn, length_skipn; lia).
    assert (SRC : bytes_at bsegs m (U + sz) bs).
    { pose proof (bytes_at_sub bsegs m U ubs (Z.to_nat sz) (Z.to_nat nz) UB ltac:(lia)) as H. rewrite Z2Nat.id in H by lia. exact H. }
    assert (B1 : bytes_at bsegs m U b1).
    { pose proof (bytes_at_sub bsegs m U ubs 0 (Z.to_nat dz) UB ltac:(lia)) as H. cbn [skipn Z.of_nat] in H. rewrite Z.add_0_r in H. exact H. }
    assert (B3 : bytes_at bsegs m (U + (dz + nz)) b3).
    { pose proof (bytes_at_sub bsegs m U ubs (Z.to_nat (dz + nz)) (length ubs - Z.to_nat (dz + nz)) UB ltac:(lia)) as H.
      rewrite Z2Nat.id in H by lia. rewrite firstn_all2 in H by (rewrite length_skipn; lia). exact H. }
    destruct (obj_chk RT Σ m U ubs kk lo sp (conj UB UW) U8 U0 ULO UKK ZR UFR (U + sz) nz N0 ltac:(lia) ltac:(lia)) as [CS _].
    destruct (obj_chk RT Σ m U ubs kk lo sp (conj UB UW) U8 U0 ULO UKK ZR UFR (U + dz) nz N0 ltac:(lia) ltac:(lia)) as [_ CD].
    eapply (aevt_memmove RT RTF PMc FDO MST Σ K ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m (U + dz) (U + sz) bs lo);
      rewrite ?BL; [exact E0| exact E1| exact E2| lia| lia| lia| exact SRC| exact CS| exact CD| exact ART0| exact MI0| exact COK| exact FRM|].
    intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' FRM' RA PR BY.
    pose proof RA as (_ & _ & WM' & _).
    destruct UFR as (f & c & Hin & F1 & F2).
    pose proof (agree_of_pres_ex _ _ _ _ _ m m' (fun x => aclient (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) x /\ ~ (U + dz <= x < U + dz + nz)) PR (fun x H => H)) as AG.
    assert (B1' : bytes_at bsegs m' U b1).
    { apply (bytes_at_agree bsegs m m' U b1 B1). eapply agree_sub; [exact AG|]. intros x Hx. cbv beta.
      split; [right; right; right; left; exists f, c; split; [exact Hin| lia]| lia]. }
    assert (B3' : bytes_at bsegs m' (U + (dz + nz)) b3).
    { apply (bytes_at_agree bsegs m m' _ b3 B3). eapply agree_sub; [exact AG|]. intros x Hx. cbv beta.
      split; [right; right; right; left; exists f, c; split; [exact Hin| lia]| lia]. }
    assert (UB' : bytes_at bsegs m' U (b1 ++ bs ++ b3)).
    { apply bytes_at_app. split; [exact B1'|]. rewrite L1. apply bytes_at_app. split; [exact BY|]. rewrite BL. replace (U + dz + nz) with (U + (dz + nz)) by lia. exact B3'. }
    assert (LL : length (b1 ++ bs ++ b3) = length ubs) by (rewrite !length_app; lia).
    eapply (HK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m' (b1 ++ bs ++ b3)); [exact FRM'| exact RA| exact PR| | exact LL|].
    - split; [exact UB'|]. rewrite LL. exact (wr_at_transport bsegs m m' U _ UW WM').
    - intros N8. replace (dz + nz - 8) with (Z.of_nat (length b1) + (nz - 8)) by lia.
      rewrite limbz_app_mid by lia. unfold bs. rewrite limbz_sub by lia. f_equal. lia.
  Qed.
End Obj.
End BCall.
