(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit Require Import RunCtx.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import base decidable list.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit Require PropExec StoreOk Frame ShapeAlg ModelAmb S8ReadBase S8ReadStage S8ReadChunk.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ZBridge Walk Arr SysStep ITree Nodes.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Spec Require Import KInv. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Spec Require Import KLink. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Spec Require Import KEv.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Malloc Require MM15. Import MM15. Import MM15.ProgDeps. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Malloc Require MM13. Import MM13. Import MM13.MallocBlocks. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Malloc Require MM12. Import MM12. Import MM12.Malloc_iface. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Malloc Require MM02. Import MM02. Import MM02.Malloc_ifaceP.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.PlainS8 Require Import PImg RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Common Require Import RunDraw.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Mr Require Import MrRulesS8.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.MrP8 Require Import S8HeapPre S8HBase S8HConv S8TrTail S8RdLib S8RdInv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Module RC := OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.S8ReadChunk.

Section CHUNK.
Context {RCa1 : RunCtx}.
Context {rc : runConstT}.
Variable sp0 : Z.
Hypothesis SP0 : 0x7fff80000000 <= sp0 <= 0x800000000000.
Hypothesis SP16 : sp0 mod 16 = 0.
Hypothesis ATOPE : ATOP = sp0 - 8388608.
Variables (path : list byte) (stdin0 : ModelAmb.AmbIn) (fs0 : Fs) (tid : word) (content : list byte).
Hypothesis Hfile : fs_lookup fs0 path = Some content.
Hypothesis Htid : 0 < bv_unsigned tid < 2 ^ 22.

Abbreviation GRD := (G_rd path stdin0 fs0 tid).
Abbreviation GPOST := (G_post stdin0 fs0 tid).
Abbreviation RDI := (rd_inv sp0 tid content).
Let L : Z := Z.of_nat (length content).

Lemma blk_after_chunk : forall (M M' : word -> option byte) buf cap len len' bs,
  rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M buf [CB (Z.to_nat cap) bs] -> firstn (Z.to_nat len) bs = firstn (Z.to_nat len) content ->
  0 <= len <= len' -> len' <= cap -> len' <= L -> 0 < buf -> buf + cap <= ATOP ->
  RC.loop_post_mem content M M' sp0 buf len len' ->
  (sp0 - 136 + 8 <= buf \/ buf + cap <= sp0 - 136) -> (0x22ed9 + 65536 <= buf \/ buf + cap <= 0x22ed9) ->
  exists bs', rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M' buf [CB (Z.to_nat cap) bs'] /\ firstn (Z.to_nat len') bs' = firstn (Z.to_nat len') content.
Proof.
  intros M M' buf cap len len' bs BLK PRE HL1 HL2 HL3 HB HAT [FM RDN] D1 D2.
  destruct (munch_of_frame_mod _ _ _ FM) as [MU WM].
  pose proof (rw_cells_bound _ _ _ _ BLK) as BB. cbn [cells_size csize] in BB.
  set (n1 := Z.to_nat len). set (n2 := Z.to_nat (len' - len)). set (n3 := Z.to_nat (cap - len')).
  assert (LBS : length bs = Z.to_nat cap) by (destruct BLK as [[[W _] _] _]; exact W).
  pose proof (rw_cells_split_CB (run_segments psegs rc_inp rc_sp rc_mb) M buf [] (Z.to_nat cap) bs [] [n1; n2; n3] BLK ltac:(cbn [sum_nat]; lia)) as SP.
  cbn [app mk_CB_cells] in SP.
  set (b1 := firstn n1 bs) in *. set (b2 := firstn n2 (skipn n1 bs)) in *. set (b3 := firstn n3 (skipn n2 (skipn n1 bs))) in *.
  change [CB n1 b1; CB n2 b2; CB n3 b3] with ([CB n1 b1] ++ [CB n2 b2; CB n3 b3]) in SP.
  apply (proj1 (rw_cells_app (run_segments psegs rc_inp rc_sp rc_mb) M buf _ _)) in SP. destruct SP as [C1 C23].
  cbn [cells_size csize] in C23. rewrite Nat.add_0_r in C23. unfold n1 in C23 at 1. rewrite Z2Nat.id in C23 by lia.
  change [CB n2 b2; CB n3 b3] with ([CB n2 b2] ++ [CB n3 b3]) in C23.
  apply (proj1 (rw_cells_app (run_segments psegs rc_inp rc_sp rc_mb) M (buf + len) _ _)) in C23. destruct C23 as [C2 C3].
  cbn [cells_size csize] in C3. rewrite Nat.add_0_r in C3. unfold n2 in C3 at 1. rewrite Z2Nat.id in C3 by lia.
  replace (buf + len + (len' - len)) with (buf + len') in C3 by lia.
  assert (UR : bv_unsigned (Z_to_bv 64 S8ReadBase.RS) = 0x22ed9) by (apply unsigned_lit; unfold S8ReadBase.RS; lia).
  assert (DJ : forall A n, 0 <= n -> buf <= A -> A + n <= buf + cap -> (A + n <= buf + len \/ buf + len' <= A) ->
               disjoint_from (fm_ivs [(Z_to_bv 64 (sp0 - 136), 8); (Z_to_bv 64 (buf + len), len' - len); (Z_to_bv 64 S8ReadBase.RS, 65536)]) A n).
  { intros A0 n0 Hn H1 H2 H3. unfold fm_ivs. cbn [map fst snd disjoint_from]. rewrite UR, !unsigned_lit by lia. lia. }
  assert (C1' : rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M' buf [CB n1 b1]).
  { eapply rw_cells_transport; [exact C1 | exact MU | exact WM |]. cbn [cells_size csize]. apply DJ; unfold n1; lia. }
  assert (C3' : rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M' (buf + len') [CB n3 b3]).
  { eapply rw_cells_transport; [exact C3 | exact MU | exact WM |]. cbn [cells_size csize]. apply DJ; unfold n3; lia. }
  set (nw := S8ReadStage.pref (len' - len) (S8ReadStage.dropz len content)) in *.
  assert (LNW : length nw = n2).
  { pose proof (OP.rdn_length _ _ _ _ _ RDN) as X. exact X. }
  assert (C2' : rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M' (buf + len) [CB n2 nw]).
  { destruct C2 as [_ WR]. split; [split|].
    - cbn. split; [exact LNW | exact I].
    - cbn [cells_bytes cbytes]. rewrite app_nil_r. apply (bytes_at_of_rdn n2); [exact RDN | lia | unfold n2; lia].
    - destruct WR as (W0 & W1 & WW). split; [exact W0|]. split; [exact W1|]. intros i Hi. apply WM. apply WW. exact Hi. }
  pose proof (proj2 (rw_cells_app (run_segments psegs rc_inp rc_sp rc_mb) M' (buf + len) [CB n2 nw] [CB n3 b3])) as J23.
  cbn [cells_size csize] in J23. rewrite Nat.add_0_r in J23. unfold n2 in J23 at 1. rewrite Z2Nat.id in J23 by lia.
  replace (buf + len + (len' - len)) with (buf + len') in J23 by lia. specialize (J23 (conj C2' C3')).
  pose proof (proj2 (rw_cells_app (run_segments psegs rc_inp rc_sp rc_mb) M' buf [CB n1 b1] ([CB n2 nw] ++ [CB n3 b3]))) as J.
  cbn [cells_size csize] in J. rewrite Nat.add_0_r in J. unfold n1 in J at 1. rewrite Z2Nat.id in J by lia. specialize (J (conj C1' J23)).
  pose proof (rw_cells_merge (run_segments psegs rc_inp rc_sp rc_mb) M' buf [] _ [] ltac:(rewrite app_nil_r; exact J)) as MG.
  cbn [app cells_size csize cells_bytes cbytes] in MG. rewrite !app_nil_r, Nat.add_0_r in MG.
  exists (b1 ++ nw ++ b3). split.
  - replace (Z.to_nat cap) with (n1 + (n2 + n3))%nat by (unfold n1, n2, n3; lia). exact MG.
  - assert (LB1 : length b1 = n1) by (unfold b1; rewrite firstn_length_le; [reflexivity | unfold n1; lia]).
    rewrite app_assoc, firstn_app.
    replace (Z.to_nat len' - length (b1 ++ nw))%nat with 0%nat by (rewrite length_app, LB1, LNW; unfold n1, n2; lia).
    cbn [firstn]. rewrite app_nil_r. rewrite firstn_all2 by (rewrite length_app, LB1, LNW; unfold n1, n2; lia).
    unfold b1, n1. rewrite PRE. unfold nw.
    change (firstn (Z.to_nat len) content) with (S8ReadStage.pref len content).
    rewrite S8ReadStage.pref_app by lia. unfold S8ReadStage.pref. f_equal. lia.
Qed.

Ltac in_kept := cbv [RC.S0ReadChunkW.loop_kept In]; repeat (first [left; apply bv_eq; reflexivity | right]).
Ltac loop_regs R' G2 G9 G23 G19 GK :=
  apply rz_mkR; unfold mkR_of;
  rewrite (G2 : reg_get R' (Z_to_bv 5 2) = _), (G9 : reg_get R' (Z_to_bv 5 9) = _),
          (G23 : reg_get R' (Z_to_bv 5 23) = _), (G19 : reg_get R' (Z_to_bv 5 19) = _);
  rewrite (GK (Z_to_bv 5 3) ltac:(in_kept) : reg_get R' (Z_to_bv 5 3) = _),
          (GK (Z_to_bv 5 4) ltac:(in_kept) : reg_get R' (Z_to_bv 5 4) = _),
          (GK (Z_to_bv 5 8) ltac:(in_kept) : reg_get R' (Z_to_bv 5 8) = _),
          (GK (Z_to_bv 5 18) ltac:(in_kept) : reg_get R' (Z_to_bv 5 18) = _),
          (GK (Z_to_bv 5 20) ltac:(in_kept) : reg_get R' (Z_to_bv 5 20) = _),
          (GK (Z_to_bv 5 21) ltac:(in_kept) : reg_get R' (Z_to_bv 5 21) = _),
          (GK (Z_to_bv 5 22) ltac:(in_kept) : reg_get R' (Z_to_bv 5 22) = _),
          (GK (Z_to_bv 5 24) ltac:(in_kept) : reg_get R' (Z_to_bv 5 24) = _),
          (GK (Z_to_bv 5 25) ltac:(in_kept) : reg_get R' (Z_to_bv 5 25) = _),
          (GK (Z_to_bv 5 26) ltac:(in_kept) : reg_get R' (Z_to_bv 5 26) = _),
          (GK (Z_to_bv 5 27) ltac:(in_kept) : reg_get R' (Z_to_bv 5 27) = _);
  simp_regs; forget_regs R'.

Lemma chunk_rz : forall (K : ShapeAlg.TSet) (pb : bptr) (buf cap len : Z) (M : word -> option byte) (s : PState) (mo : Model)
    (x1 x3 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  RDI (GRD len) pb buf cap len M s mo -> 0 <= len < cap -> 65536 <= cap <= 2 ^ 40 ->
  (cap <= L -> forall (M' : word -> option byte) (mo' : Model) (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
     RDI (GRD cap) pb buf cap cap M' s mo' -> m_vmmaps mo' = m_vmmaps mo ->
     realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (MS (mkR y1 (Z_to_bv 64 (sp0 - 128)) x3 (Z_to_bv 64 RATP) y5 y6 y7 x8 (Z_to_bv 64 buf)
                                    y10 y11 y12 y13 y14 y15 y16 y17 x18 (Z_to_bv 64 cap) (Z_to_bv 64 3) (Z_to_bv 64 cap)
                                    (Z_to_bv 64 0x22ed9) (Z_to_bv 64 buf) x24 x25 x26 x27 y28 y29 y30 y31)
                               bvmap_empty (Z_to_bv 64 0x14968) fc0 None M' (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) mo') K) ->
  (L < cap -> forall (M' : word -> option byte) (mo' : Model) (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
     RDI GPOST pb buf cap L M' s mo' -> m_vmmaps mo' = m_vmmaps mo ->
     realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (MS (mkR y1 (Z_to_bv 64 (sp0 - 128)) x3 (Z_to_bv 64 RATP) y5 y6 y7 x8 (Z_to_bv 64 buf)
                                    y10 y11 y12 y13 y14 y15 y16 y17 x18 (Z_to_bv 64 L) (Z_to_bv 64 3) (Z_to_bv 64 cap)
                                    (Z_to_bv 64 0x22ed9) (Z_to_bv 64 0) x24 x25 x26 x27 y28 y29 y30 y31)
                               bvmap_empty (Z_to_bv 64 0x149d0) fc0 None M' (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) mo') K) ->
  realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (MS (mkR x1 (Z_to_bv 64 (sp0 - 128)) x3 (Z_to_bv 64 RATP) x5 x6 x7 x8 (Z_to_bv 64 buf)
                                 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 len) (Z_to_bv 64 3) (Z_to_bv 64 cap)
                                 (Z_to_bv 64 0x22ed9) x23 x24 x25 x26 x27 x28 x29 x30 x31)
                            bvmap_empty (Z_to_bv 64 0x149a0) fc0 None M (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) mo) K.
Proof.
  intros until x31. intros RI HLEN HCAP KFULL KEND.
  pose proof (rd_blk_range _ _ _ _ _ _ _ _ _ _ _ RI) as (BR1 & BR2 & BR3 & BR4).
  pose proof RI as [HH HOWN (bs & BLK & PRE) [LEN1 LEN2] BASE].
  pose proof BASE as [ST _ _ _ _ _ _ _].
  pose proof HOWN as [(Ld & _ & HKL & _) [_ HG]]. unfold G_rd in HG.
  pose proof (kl_minv _ _ _ HKL) as MINV.
  assert (SPW : sp_window_lo <= bv_unsigned (vm_init_sp (m_vmmaps mo)) <= sp_window_hi)
    by (destruct MINV as (_ & _ & _ & _ & _ & _ & _ & _ & _ & X & _); exact X).   (* minv + reader *)
  set (V := m_vmmaps mo) in *.
  rewrite HG.
  lazymatch goal with |- realizes _ (mkCfg (MS ?RR _ _ _ _ _ _) _) _ =>
    eapply (RC.chunk_loop_mid path content stdin0 fs0 tid V Hfile (Z.to_nat (cap - len)) RR M sp0 buf len cap K) end.
  - lia.
  - unfold RC.mid_regs. repeat split; reflexivity.
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - exact LEN2.
  - apply (store_ok_of_stk M (sp0 - 6144513) (sp0 - 128)); [exact ST | lia | lia].
  - pose proof (wr_at_store_ok (run_segments psegs rc_inp rc_sp rc_mb) M buf (Z.of_nat (Z.to_nat cap + 0)) len (Z.to_nat (cap - len)) (proj2 BLK) ltac:(lia) ltac:(lia)) as X.
    exact X.
  -
    intros HL R' M' (G2 & G9 & G23 & G19 & GK) PM.
    assert (BLK' : exists bs', rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M' buf [CB (Z.to_nat cap) bs'] /\ firstn (Z.to_nat cap) bs' = firstn (Z.to_nat cap) content).
    { eapply (blk_after_chunk M M' buf cap len cap bs); try eassumption; try lia. }
    destruct PM as [FM _]. destruct (munch_of_frame_mod _ _ _ FM) as [MU WM].
    loop_regs R' G2 G9 G23 G19 GK.
    eapply KFULL; [exact HL| | reflexivity].
    eapply (rd_inv_munch sp0 SP0 ATOPE tid content (GRD len) (GRD cap) pb buf cap len cap _ M M' s mo _ RI MU WM);
      [ | | exact BLK' | lia | exact HL | ].
    + unfold fm_ivs. cbn [map fst snd]. rewrite !unsigned_lit by (unfold S8ReadBase.RS; lia).
      apply Forall_cons; [ | apply Forall_cons; [ | apply Forall_cons; [ | apply Forall_nil]]];
        unfold fp_rd; cbn [fst snd]; unfold S8ReadBase.RS; lia.
    + unfold fm_ivs. cbn [map fst snd]. rewrite !unsigned_lit by (unfold S8ReadBase.RS; lia).
      apply Forall_cons; [ | apply Forall_cons; [ | apply Forall_cons; [ | apply Forall_nil]]];
        cbn [fst snd]; unfold S8ReadBase.RS; intros; lia.
    + eapply (OWN_same_vm [pb] (GRD len) (GRD cap) s mo); [exact HOWN | reflexivity | | reflexivity | reflexivity].
      apply minv_modelG; [rewrite Hfile; discriminate | exact Htid | exact (rdr_of_OWN_rd _ _ _ _ _ _ _ _ HOWN) | exact SPW].
  -
    intros HL R' M' (G2 & G9 & G23 & G19 & GK) PM.
    assert (BLK' : exists bs', rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M' buf [CB (Z.to_nat cap) bs'] /\ firstn (Z.to_nat L) bs' = firstn (Z.to_nat L) content).
    { eapply (blk_after_chunk M M' buf cap len L bs); try eassumption; try lia. }
    destruct PM as [FM _]. destruct (munch_of_frame_mod _ _ _ FM) as [MU WM].
    loop_regs R' G2 G9 G23 G19 GK.
    eapply KEND; [exact HL| | reflexivity].
    eapply (rd_inv_munch sp0 SP0 ATOPE tid content (GRD len) GPOST pb buf cap len L _ M M' s mo _ RI MU WM);
      [ | | exact BLK' | lia | lia | ].
    + unfold fm_ivs. cbn [map fst snd]. rewrite !unsigned_lit by (unfold S8ReadBase.RS; lia).
      apply Forall_cons; [ | apply Forall_cons; [ | apply Forall_cons; [ | apply Forall_nil]]];
        unfold fp_rd; cbn [fst snd]; unfold S8ReadBase.RS; lia.
    + unfold fm_ivs. cbn [map fst snd]. rewrite !unsigned_lit by (unfold S8ReadBase.RS; lia).
      apply Forall_cons; [ | apply Forall_cons; [ | apply Forall_cons; [ | apply Forall_nil]]];
        cbn [fst snd]; unfold S8ReadBase.RS; intros; lia.
    + eapply (OWN_same_vm [pb] (GRD len) GPOST s mo); [exact HOWN | reflexivity | | reflexivity | reflexivity].
      apply minv_model_post; [exact Htid | exact (rdr_of_OWN_rd _ _ _ _ _ _ _ _ HOWN) | exact SPW].
Qed.
End CHUNK.
