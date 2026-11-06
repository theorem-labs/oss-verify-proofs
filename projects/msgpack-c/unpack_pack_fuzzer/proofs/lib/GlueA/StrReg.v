(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PrimInt63 Uint63.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Cells Frame ITree Nodes.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib Require ALib.Mem ALib.Step.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import AcctCore ExecF ITreeA NodesA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Shadow.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg AProto ABase AMalloc_iface.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AMalloc_iface2.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import RtCells.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Instr State Step Plan PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import Mem.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib Defs DefsA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Ledger Op Adeq.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.Step Plan PlanS CtrLib HeapOp.
Open Scope Z_scope.
Unset Lia Cache.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Actr.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64Proofs ValProofs MemProofs.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require Import CtrFX.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require HeapCtr HeapCtrB.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require CallA GlueA CtrPre.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import UnreggSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import StackSh RangePre StrRegC.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue Require InitLib.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require UnreggPre.
Unset Nia Cache. Unset Nra Cache.
Import CtrFX ActrA StrRegC.
Module AP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec.

Definition zarg_holds {rc : runConstT} (az : word) (m : word -> option byte) : Prop :=
  bv_unsigned az <= 2 ^ 47 /\
  forall s, shad (bv_unsigned az + 7) <= s < Shadow.KHIGH -> m (ALib.Mem.wa s) = Some (Z_to_bv 8 0) /\ wb asegs m s = true.

Lemma bytes_at_of_rbA {rc : runConstT} : forall (m : word -> option byte) A (bs : list byte),
  0 <= A -> A + Z.of_nat (length bs) <= 2 ^ 64 ->
  (forall j, 0 <= j < Z.of_nat (length bs) -> rb asegs m (A + j) = Some (nth (Z.to_nat j) bs (Z_to_bv 8 0))) ->
  ALib.Mem.bytes_at asegs m A bs.
Proof.
  intros m A bs HA HB RB. split; [lia|]. split; [lia|].
  intros i Hi. rewrite <- (GlueA.rb_mrdA asegs). rewrite (RB (Z.of_nat i)) by lia. rewrite Nat2Z.id. symmetry. apply nth_error_nth'. lia.
Qed.

Definition legal_str (j js : int) : Prop := (j = 1%uint63 /\ js = 9%uint63) \/ (j = 3%uint63 /\ js = 10%uint63).

Lemma nth_map_seq : forall (f : nat -> byte) n i d, (i < n)%nat -> nth i (map f (seq 0 n)) d = f i.
Proof.
  intros f n i d Hi. rewrite (nth_indep _ d (f 0%nat)) by (rewrite length_map, length_seq; exact Hi).
  rewrite map_nth, seq_nth by exact Hi. reflexivity.
Qed.

Lemma slice_all : forall (l : list byte) n d, n = length l -> map (fun i => nth (Z.to_nat 0 + i)%nat l d) (seq 0 n) = l.
Proof.
  intros l n d ->. apply (nth_ext _ _ d d); [rewrite length_map, length_seq; reflexivity|].
  intros i Hi. rewrite length_map, length_seq in Hi. rewrite nth_map_seq by exact Hi. reflexivity.
Qed.

Lemma str_reg_ok_shape : forall st wnl k rr j js, str_reg_ok st wnl k rr j js = true ->
  exists az, find_op ZARG_ID (s_ops st) = Some [az]
    /\ PrimInt63.eqb k 0%uint63 = false /\ str_region rr j js = true
    /\ rg_lo rr = 0%uint63 /\ rg_w rr = false /\ rg_hi rr = VBlob false js (VL wzero) 8%uint63 /\ rg_bg rr = BGBlob j 0%uint63 /\ rg_cells rr = IMap.Leaf
    /\ CtrA.win_lookup wnl k = None
    /\ (exists ks offs rss, ActrA.sp_region st = Some (ks, offs, rss) /\ k <> ks)
    /\ known_leu (s_facts st) (sv_alu ALU_ADD az (VL (wlit 72%uint63))) (VP k wzero) = true
    /\ known_leu (s_facts st) (sv_alu ALU_ADD (VP k wzero) (rg_hi rr)) (VL TOP16) = true.
Proof.
  intros st wnl k rr j js H. unfold str_reg_ok in H.
  destruct (find_op ZARG_ID (s_ops st)) as [[|az [|? ?]]|] eqn:FZ; try discriminate H.
  repeat match type of H with (_ && _)%bool = true => let X := fresh "Q" in apply andb_prop in H as [H X] end.
  apply negb_true_iff in H.
  destruct (CtrA.win_lookup wnl k) as [[? ?]|] eqn:WLK; [discriminate Q2|].
  destruct (ActrA.sp_region st) as [[[ks offs] rss]|] eqn:SPR; [|discriminate Q1]. apply negb_true_iff in Q1. apply Uint63.eqb_false_spec in Q1.
  pose proof Q3 as SRG. unfold str_region in Q3.
  repeat match type of Q3 with (_ && _)%bool = true => let X := fresh "S" in apply andb_prop in Q3 as [Q3 X] end.
  apply Uint63.eqb_correct in Q3. apply negb_true_iff in S2.
  destruct (rg_hi rr) as [| | | | | | | |sx js' off w8| |] eqn:RH; try discriminate S1. destruct sx; [discriminate S1|].
  destruct off as [z| | | | | | | | | |]; try discriminate S1.
  repeat match type of S1 with (_ && _)%bool = true => let X := fresh "T" in apply andb_prop in S1 as [S1 X] end.
  apply Uint63.eqb_correct in S1. subst js'. apply ValP.weqb_eq in T0. subst z. apply Uint63.eqb_correct in T. subst w8.
  destruct (rg_bg rr) as [| | | |j' sh] eqn:RB; try discriminate S0. apply andb_prop in S0 as [S0 S0']. apply Uint63.eqb_correct in S0, S0'. subst j' sh.
  destruct (rg_cells rr) as [|? ? ? ? ?] eqn:RC; [|discriminate S].
  exists az. split; [reflexivity|]. split; [exact H|]. split; [exact SRG|]. split; [exact Q3|]. split; [exact S2|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [exists ks, offs, rss; split; [reflexivity| exact Q1]|]. split; [exact Q0| exact Q].
Qed.

Section Facts.
Context {rc : runConstT}.
Variable AI : AMallocIface2.
Variable ACCT : word -> alayout -> footprint -> astate -> list ablock -> Model -> Prop.
Variable UNIV : list (list Z).
Variable Cw : client_world.
Variable OPS : optable.
Hypothesis OPS_holds_zarg : forall az m mo, op_holds OPS ZARG_ID [az] m mo -> zarg_holds az m.
Hypothesis ACCT_rng : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng RNG (ATOP + 4096) (2^47 - (ATOP + 4096)).
Hypothesis ACCT_rng_stk_sh : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng RNG (shad ATOP) (Shadow.KHIGH - shad ATOP).

Lemma known_leu_sound_q : forall E st ms model a b, st_ok asegs OPS E st ms model ->
  known_leu (s_facts st) a b = true -> bv_unsigned (den E a) <= bv_unsigned (den E b).
Proof.
  intros E st ms model a b HS H. unfold known_leu, dec_false in H.
  destruct (decide_ltu (s_facts st) b a) as [[|]|] eqn:Hd; try discriminate H.
  pose proof (ValP.decide_ltu_sound E (s_facts st) (so_facts _ _ _ _ _ _ HS) b a false Hd) as X.
  apply (proj1 (ValP.ltu_iff _ _ false)) in X. exact X.
Qed.

Lemma str_reg_facts : forall E st ms mo r hargs wnl (L : alayout) (RNG : footprint) (sta : astate) (LBa : list ablock) (aw : word) k rr j js o len,
  st_ok asegs OPS E st ms mo ->
  CtrPre.acallG AI ACCT UNIV Cw E st ms mo r hargs wnl L RNG sta LBa aw -> ACCT aw L RNG sta LBa mo ->
  let sp := bv_unsigned (AP.getr (ms_regs ms) 2) in
  ATOP + 4096 <= CtrPre.sp_lo E st -> CtrPre.sp_lo E st <= sp - 4096 -> sp < 2 ^ 47 ->
  IMap.find k (s_regs st) = Some rr -> str_reg_ok st wnl k rr j js = true ->
  0 <= o -> 0 <= len -> o + len <= hiZ E rr ->
  exists (RLO RHI : Z),
    let Sa := bv_unsigned (ev E k) + o in
    bv_unsigned (ev E k) + hiZ E rr <= 2 ^ 47 - 16
    /\ ALib.Mem.bytes_at asegs (ms_mem ms) Sa (map (fun i => nth (Z.to_nat o + i)%nat (eb E j) (Z_to_bv 8 0)) (seq 0 (Z.to_nat len)))
    /\ sp <= Sa /\ Shadow.app_blk Sa (Sa + len) /\ 0 < Sa /\ Shadow.unpoisoned (ms_mem ms) Sa (Sa + len)
    /\ (RLO <= Sa /\ Sa + len <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0 /\ 0 <= RLO /\ RHI <= Shadow.KEND)
    /\ ALib.Mem.wr_at asegs (ms_mem ms) (shad RLO) (shad RHI - shad RLO)
    /\ rng RNG Sa len /\ rng RNG (shad RLO) (shad RHI - shad RLO).
Proof.
  intros E st ms mo r hargs wnl L RNG sta LBa aw k rr j js o len HS CF AC sp BOT LO SPT Hk SRO Ho Hlen HIN.
  pose proof atop_range as ATR. set (m := ms_mem ms) in *.
  destruct (str_reg_ok_shape st wnl k rr j js SRO) as (az & FZ & Q4 & SRG & Q3 & S2 & RH & RB & RC & WLK & (ks0 & offs0 & rss0 & SPR0 & KNS) & Q0 & Q).
  assert (LOZ : loZ rr = 0) by (unfold loZ; rewrite Q3; reflexivity).
  pose proof (so_reg _ _ _ _ _ _ HS k rr Hk) as RO.
  destruct (ro_range _ _ _ _ _ _ RO Q4) as [RG0 RG1]. rewrite LOZ in RG0.
  set (Sa0 := bv_unsigned (ev E k)) in *. set (hz := hiZ E rr) in *.
  assert (HZ0 : 0 <= hz) by (unfold hz, hiZ; pose proof (bv_unsigned_in_range _ (den E (rg_hi rr))); lia).
  pose proof (bv_unsigned_in_range _ (ev E k)) as RSa. fold Sa0 in RSa. unfold bv_modulus in RSa. change (2 ^ Z.of_N 64) with (2 ^ 64) in RSa.
  unfold two64 in RG1.
  idtac "SR-1".

  assert (BYT : ALib.Mem.bytes_at asegs m (Sa0 + o) (map (fun i => nth (Z.to_nat o + i)%nat (eb E j) (Z_to_bv 8 0)) (seq 0 (Z.to_nat len)))).
  { apply bytes_at_of_rbA; [lia | rewrite length_map, length_seq; lia|].
    intros q Hq. rewrite length_map, length_seq in Hq.
    pose proof (ro_bg _ _ _ _ _ _ RO (o + q) ltac:(intros _; rewrite LOZ; fold hz; lia) ltac:(intros K; rewrite K in Q4; discriminate Q4)) as BG.
    assert (UNC : uncovered rr (o + q)) by (intros g gr _ F; rewrite RC in F; discriminate F).
    specialize (BG UNC). unfold bg_byte in BG. rewrite RB in BG. change (to_Z 0%uint63) with 0 in BG. rewrite Z.sub_0_r in BG.
    fold Sa0 m in BG. replace (Sa0 + o + q) with (Sa0 + (o + q)) by lia. rewrite BG. f_equal.
    rewrite nth_map_seq by lia. f_equal. lia. }

  assert (SPA : sp <= Sa0).
  { destruct CF as (LB & ks & offs & rss & ksp & nn & md & Asv & nw & rest & SPR & Hksp & SPE & K16 & LOSP & FLOOR & Hf & Hc & Eh & Tnw & Nn & Ln & N255
                    & NWI & AN & AJ & TS & WF & HC & AWden & AR).
    assert (KN0 : k <> 0%uint63) by (intros ->; discriminate Q4).
    pose proof (CallA.aregion_just_sound asegs OPS E st ms mo wnl ks offs rss k rr HS SPR AJ Hk KN0) as JU.
    rewrite SPR in SPR0. injection SPR0 as <- <- <-.
    destruct JU as [[EQ _]|[_ [(len0 & kd0 & WLS & _)|[[J1 _]|VJ]]]]; [contradiction | rewrite WLK in WLS; discriminate WLS | |].
    2:{
        exfalso. destruct VJ as [VJ|SL].
        -
          unfold ActrA.view_just, ActrA.zero_view, ActrA.view_I, ActrA.ro_lit_hi, ActrA.view_tail in VJ. rewrite RH in VJ. cbn in VJ.
          rewrite ?andb_false_r in VJ. cbn in VJ. first [discriminate VJ | match type of VJ with ?T => idtac "VJ-REM" T end; fail].
        -
          unfold ActrA.sliver_just in SL. destruct (ActrA.stack_wlo st); [|discriminate SL]. destruct (IMap.find ks (s_regs st)); [|discriminate SL].
          apply andb_prop in SL as [SL _]. apply andb_prop in SL as [SL _]. apply andb_prop in SL as [_ SL]. rewrite RB in SL. cbn in SL. discriminate SL. }
    rewrite LOZ, Z.add_0_r in J1. fold Sa0 in J1.
    assert (E2 : bv_unsigned (AP.getr (ms_regs ms) 2) = bv_unsigned (den E (getr st X2))) by (f_equal; exact (GlueA.getr_RA asegs OPS E st ms mo HS X2)).
    unfold sp. rewrite E2. exact J1. }

  pose proof (known_leu_sound_q E st ms mo _ _ HS Q) as KE. rewrite ValP.den_sv_alu in KE. cbn [alu64 alu] in KE. rewrite bv_add_unsigned in KE.
  assert (DV0 : bv_unsigned (den E (VP k wzero)) = Sa0).
  { rewrite ValP.den_VP. change (w2Zs wzero) with 0. rewrite Z.add_0_r. apply Z.mod_small. unfold two64. fold Sa0. lia. }
  rewrite DV0 in KE. change (bv_unsigned (den E (rg_hi rr))) with hz in KE. change (bv_unsigned (den E (VL TOP16))) with (2 ^ 47 - 16) in KE.
  rewrite bv_wrap_small in KE by (unfold bv_modulus; change (2 ^ Z.of_N 64) with (2 ^ 64); lia).

  pose proof (proj1 (Forall_forall _ _) (so_ops _ _ _ _ _ _ HS) _ (UnreggPre.find_op_In _ _ _ FZ)) as HO. cbn [op_id op_args map] in HO.
  destruct (OPS_holds_zarg _ _ _ HO) as [AZB ZARG]. fold m in ZARG. set (Az := bv_unsigned (den E az)) in *.
  pose proof (known_leu_sound_q E st ms mo _ _ HS Q0) as KB. rewrite ValP.den_sv_alu in KB. cbn [alu64 alu den] in KB. rewrite bv_add_unsigned in KB.
  fold (den E (VP k wzero)) in KB. rewrite DV0 in KB. fold Az in KB. change (bv_unsigned (wbv (wlit 72%uint63))) with 72 in KB.
  pose proof (bv_unsigned_in_range _ (den E az)) as RAZ. fold Az in RAZ.
  rewrite bv_wrap_small in KB by (unfold bv_modulus; change (2 ^ Z.of_N 64) with (2 ^ 64); lia).
  idtac "SR-2".
  exists ((Sa0 + o) / 64 * 64), ((Sa0 + o + len + 63) / 64 * 64). cbv zeta.
  split; [exact KE|].
  assert (H1 : (Sa0 + o) / 64 * 64 <= Sa0 + o /\ Sa0 + o < (Sa0 + o) / 64 * 64 + 64) by (Z.div_mod_to_equations; lia).
  assert (H2 : Sa0 + o + len <= (Sa0 + o + len + 63) / 64 * 64 /\ (Sa0 + o + len + 63) / 64 * 64 <= 2 ^ 47) by (Z.div_mod_to_equations; lia).
  assert (SH1 : shad (Az + 7) <= shad ((Sa0 + o) / 64 * 64)) by (apply shad_mono; lia).
  assert (SH2 : shad ((Sa0 + o) / 64 * 64) <= shad ((Sa0 + o + len + 63) / 64 * 64)) by (apply shad_mono; lia).
  pose proof (shad_mono _ _ (proj2 H2)) as SH3. rewrite shad_top in SH3.
  assert (SH0 : 0 <= shad (Az + 7)) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; pose proof (Z.div_pos (Az + 7) (2 ^ 3)); lia).
  split; [exact BYT|]. split; [lia|].
  split; [split; [lia|]; right; unfold Shadow.KHIGH, Shadow.KEND; lia|].
  split; [lia|].
  split.
  { split; [lia|]. split; [lia|]. intros G _ G1 G2. exists (Z_to_bv 8 0). split; [| left; reflexivity].
    apply (proj1 (ZARG (ASHOFF + G) ltac:(unfold shad in *; rewrite !Z.shiftr_div_pow2 in * by lia; change (2 ^ 3) with 8 in *; unfold Shadow.KHIGH, ASHOFF in *; Z.div_mod_to_equations; lia))). }
  split; [repeat split; try lia; try (apply Z_mod_mult); unfold Shadow.KEND; lia|].
  split.
  { split; [lia|]. split; [unfold Shadow.KHIGH in *; lia|]. intros i Hi. apply (GlueA.wb_wviewA asegs). apply (proj2 (ZARG (shad ((Sa0 + o) / 64 * 64) + i) ltac:(lia))). }
  split; [apply (rng_sub _ _ _ _ _ (ACCT_rng _ _ _ _ _ _ AC)); lia|].
  apply (rng_sub _ _ _ _ _ (ACCT_rng_stk_sh _ _ _ _ _ _ AC)); [apply shad_mono; lia | lia].
Qed.
End Facts.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.AcctCore OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ITreeA OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.NodesA.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import AProto.TwinB ABase.TwinB AMalloc_iface.TwinB.
Import AMalloc_iface2.TwinB.
Import RtCells.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Plan OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.PlanSound.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap.Op.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Lib OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Defs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.DefsA.
Import Ledger.TwinB Op.TwinB Adeq.TwinB.

Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.Step Plan PlanS CtrLib HeapOp.
Open Scope Z_scope.
Unset Lia Cache.

Import Actr.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64Proofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.ValProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.MemProofs.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.CtrFX.

Import UnreggSound.TwinB.
Import StackSh.TwinB RangePre.TwinB StrRegC.TwinB.

Unset Nia Cache. Unset Nra Cache.
Import CtrFX ActrA StrRegC.TwinB.StrRegC.
Module AP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec.

Definition zarg_holds {rc : runConstT} (az : word) (m : word -> option byte) : Prop :=
  bv_unsigned az <= 2 ^ 47 /\
  forall s, shad (bv_unsigned az + 7) <= s < Shadow.KHIGH -> m (ALib.Mem.wa s) = Some (Z_to_bv 8 0) /\ wb bsegs m s = true.

Lemma bytes_at_of_rbA {rc : runConstT} : forall (m : word -> option byte) A (bs : list byte),
  0 <= A -> A + Z.of_nat (length bs) <= 2 ^ 64 ->
  (forall j, 0 <= j < Z.of_nat (length bs) -> rb bsegs m (A + j) = Some (nth (Z.to_nat j) bs (Z_to_bv 8 0))) ->
  ALib.Mem.bytes_at bsegs m A bs.
Proof.
  intros m A bs HA HB RB. split; [lia|]. split; [lia|].
  intros i Hi. rewrite <- (GlueA.TwinB.rb_mrdA bsegs). rewrite (RB (Z.of_nat i)) by lia. rewrite Nat2Z.id. symmetry. apply nth_error_nth'. lia.
Qed.

Definition legal_str (j js : int) : Prop := (j = 1%uint63 /\ js = 9%uint63) \/ (j = 3%uint63 /\ js = 10%uint63).

Lemma nth_map_seq : forall (f : nat -> byte) n i d, (i < n)%nat -> nth i (map f (seq 0 n)) d = f i.
Proof.
  intros f n i d Hi. rewrite (nth_indep _ d (f 0%nat)) by (rewrite length_map, length_seq; exact Hi).
  rewrite map_nth, seq_nth by exact Hi. reflexivity.
Qed.

Lemma slice_all : forall (l : list byte) n d, n = length l -> map (fun i => nth (Z.to_nat 0 + i)%nat l d) (seq 0 n) = l.
Proof.
  intros l n d ->. apply (nth_ext _ _ d d); [rewrite length_map, length_seq; reflexivity|].
  intros i Hi. rewrite length_map, length_seq in Hi. rewrite nth_map_seq by exact Hi. reflexivity.
Qed.

Lemma str_reg_ok_shape : forall st wnl k rr j js, str_reg_ok st wnl k rr j js = true ->
  exists az, find_op ZARG_ID (s_ops st) = Some [az]
    /\ PrimInt63.eqb k 0%uint63 = false /\ str_region rr j js = true
    /\ rg_lo rr = 0%uint63 /\ rg_w rr = false /\ rg_hi rr = VBlob false js (VL wzero) 8%uint63 /\ rg_bg rr = BGBlob j 0%uint63 /\ rg_cells rr = IMap.Leaf
    /\ CtrA.win_lookup wnl k = None
    /\ (exists ks offs rss, ActrA.sp_region st = Some (ks, offs, rss) /\ k <> ks)
    /\ known_leu (s_facts st) (sv_alu ALU_ADD az (VL (wlit 72%uint63))) (VP k wzero) = true
    /\ known_leu (s_facts st) (sv_alu ALU_ADD (VP k wzero) (rg_hi rr)) (VL TOP16) = true.
Proof.
  intros st wnl k rr j js H. unfold str_reg_ok in H.
  destruct (find_op ZARG_ID (s_ops st)) as [[|az [|? ?]]|] eqn:FZ; try discriminate H.
  repeat match type of H with (_ && _)%bool = true => let X := fresh "Q" in apply andb_prop in H as [H X] end.
  apply negb_true_iff in H.
  destruct (CtrA.win_lookup wnl k) as [[? ?]|] eqn:WLK; [discriminate Q2|].
  destruct (ActrA.sp_region st) as [[[ks offs] rss]|] eqn:SPR; [|discriminate Q1]. apply negb_true_iff in Q1. apply Uint63.eqb_false_spec in Q1.
  pose proof Q3 as SRG. unfold str_region in Q3.
  repeat match type of Q3 with (_ && _)%bool = true => let X := fresh "S" in apply andb_prop in Q3 as [Q3 X] end.
  apply Uint63.eqb_correct in Q3. apply negb_true_iff in S2.
  destruct (rg_hi rr) as [| | | | | | | |sx js' off w8| |] eqn:RH; try discriminate S1. destruct sx; [discriminate S1|].
  destruct off as [z| | | | | | | | | |]; try discriminate S1.
  repeat match type of S1 with (_ && _)%bool = true => let X := fresh "T" in apply andb_prop in S1 as [S1 X] end.
  apply Uint63.eqb_correct in S1. subst js'. apply ValP.weqb_eq in T0. subst z. apply Uint63.eqb_correct in T. subst w8.
  destruct (rg_bg rr) as [| | | |j' sh] eqn:RB; try discriminate S0. apply andb_prop in S0 as [S0 S0']. apply Uint63.eqb_correct in S0, S0'. subst j' sh.
  destruct (rg_cells rr) as [|? ? ? ? ?] eqn:RC; [|discriminate S].
  exists az. split; [reflexivity|]. split; [exact H|]. split; [exact SRG|]. split; [exact Q3|]. split; [exact S2|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [exists ks, offs, rss; split; [reflexivity| exact Q1]|]. split; [exact Q0| exact Q].
Qed.

Section Facts.
Context {rc : runConstT}.
Variable AI : AMallocIface2.
Variable ACCT : word -> alayout -> footprint -> astate -> list ablock -> Model -> Prop.
Variable UNIV : list (list Z).
Variable Cw : client_world.
Variable OPS : optable.
Hypothesis OPS_holds_zarg : forall az m mo, op_holds OPS ZARG_ID [az] m mo -> zarg_holds az m.
Hypothesis ACCT_rng : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng RNG (ATOP + 4096) (2^47 - (ATOP + 4096)).
Hypothesis ACCT_rng_stk_sh : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng RNG (shad ATOP) (Shadow.KHIGH - shad ATOP).

Lemma known_leu_sound_q : forall E st ms model a b, st_ok bsegs OPS E st ms model ->
  known_leu (s_facts st) a b = true -> bv_unsigned (den E a) <= bv_unsigned (den E b).
Proof.
  intros E st ms model a b HS H. unfold known_leu, dec_false in H.
  destruct (decide_ltu (s_facts st) b a) as [[|]|] eqn:Hd; try discriminate H.
  pose proof (ValP.decide_ltu_sound E (s_facts st) (so_facts _ _ _ _ _ _ HS) b a false Hd) as X.
  apply (proj1 (ValP.ltu_iff _ _ false)) in X. exact X.
Qed.

Lemma str_reg_facts : forall E st ms mo r hargs wnl (L : alayout) (RNG : footprint) (sta : astate) (LBa : list ablock) (aw : word) k rr j js o len,
  st_ok bsegs OPS E st ms mo ->
  CtrPre.TwinB.acallG AI ACCT UNIV Cw E st ms mo r hargs wnl L RNG sta LBa aw -> ACCT aw L RNG sta LBa mo ->
  let sp := bv_unsigned (AP.getr (ms_regs ms) 2) in
  ATOP + 4096 <= CtrPre.TwinB.sp_lo E st -> CtrPre.TwinB.sp_lo E st <= sp - 4096 -> sp < 2 ^ 47 ->
  IMap.find k (s_regs st) = Some rr -> str_reg_ok st wnl k rr j js = true ->
  0 <= o -> 0 <= len -> o + len <= hiZ E rr ->
  exists (RLO RHI : Z),
    let Sa := bv_unsigned (ev E k) + o in
    bv_unsigned (ev E k) + hiZ E rr <= 2 ^ 47 - 16
    /\ ALib.Mem.bytes_at bsegs (ms_mem ms) Sa (map (fun i => nth (Z.to_nat o + i)%nat (eb E j) (Z_to_bv 8 0)) (seq 0 (Z.to_nat len)))
    /\ sp <= Sa /\ Shadow.app_blk Sa (Sa + len) /\ 0 < Sa /\ Shadow.unpoisoned (ms_mem ms) Sa (Sa + len)
    /\ (RLO <= Sa /\ Sa + len <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0 /\ 0 <= RLO /\ RHI <= Shadow.KEND)
    /\ ALib.Mem.wr_at bsegs (ms_mem ms) (shad RLO) (shad RHI - shad RLO)
    /\ rng RNG Sa len /\ rng RNG (shad RLO) (shad RHI - shad RLO).
Proof.
  intros E st ms mo r hargs wnl L RNG sta LBa aw k rr j js o len HS CF AC sp BOT LO SPT Hk SRO Ho Hlen HIN.
  pose proof atop_range as ATR. set (m := ms_mem ms) in *.
  destruct (str_reg_ok_shape st wnl k rr j js SRO) as (az & FZ & Q4 & SRG & Q3 & S2 & RH & RB & RC & WLK & (ks0 & offs0 & rss0 & SPR0 & KNS) & Q0 & Q).
  assert (LOZ : loZ rr = 0) by (unfold loZ; rewrite Q3; reflexivity).
  pose proof (so_reg _ _ _ _ _ _ HS k rr Hk) as RO.
  destruct (ro_range _ _ _ _ _ _ RO Q4) as [RG0 RG1]. rewrite LOZ in RG0.
  set (Sa0 := bv_unsigned (ev E k)) in *. set (hz := hiZ E rr) in *.
  assert (HZ0 : 0 <= hz) by (unfold hz, hiZ; pose proof (bv_unsigned_in_range _ (den E (rg_hi rr))); lia).
  pose proof (bv_unsigned_in_range _ (ev E k)) as RSa. fold Sa0 in RSa. unfold bv_modulus in RSa. change (2 ^ Z.of_N 64) with (2 ^ 64) in RSa.
  unfold two64 in RG1.
  idtac "SR-1".

  assert (BYT : ALib.Mem.bytes_at bsegs m (Sa0 + o) (map (fun i => nth (Z.to_nat o + i)%nat (eb E j) (Z_to_bv 8 0)) (seq 0 (Z.to_nat len)))).
  { apply bytes_at_of_rbA; [lia | rewrite length_map, length_seq; lia|].
    intros q Hq. rewrite length_map, length_seq in Hq.
    pose proof (ro_bg _ _ _ _ _ _ RO (o + q) ltac:(intros _; rewrite LOZ; fold hz; lia) ltac:(intros K; rewrite K in Q4; discriminate Q4)) as BG.
    assert (UNC : uncovered rr (o + q)) by (intros g gr _ F; rewrite RC in F; discriminate F).
    specialize (BG UNC). unfold bg_byte in BG. rewrite RB in BG. change (to_Z 0%uint63) with 0 in BG. rewrite Z.sub_0_r in BG.
    fold Sa0 m in BG. replace (Sa0 + o + q) with (Sa0 + (o + q)) by lia. rewrite BG. f_equal.
    rewrite nth_map_seq by lia. f_equal. lia. }

  assert (SPA : sp <= Sa0).
  { destruct CF as (LB & ks & offs & rss & ksp & nn & md & Asv & nw & rest & SPR & Hksp & SPE & K16 & LOSP & FLOOR & Hf & Hc & Eh & Tnw & Nn & Ln & N255
                    & NWI & AN & AJ & TS & WF & HC & AWden & AR).
    assert (KN0 : k <> 0%uint63) by (intros ->; discriminate Q4).
    pose proof (CallA.TwinB.aregion_just_sound bsegs OPS E st ms mo wnl ks offs rss k rr HS SPR AJ Hk KN0) as JU.
    rewrite SPR in SPR0. injection SPR0 as <- <- <-.
    destruct JU as [[EQ _]|[_ [(len0 & kd0 & WLS & _)|[[J1 _]|VJ]]]]; [contradiction | rewrite WLK in WLS; discriminate WLS | |].
    2:{
        exfalso. destruct VJ as [VJ|SL].
        -
          unfold ActrA.view_just, ActrA.zero_view, ActrA.view_I, ActrA.ro_lit_hi, ActrA.view_tail in VJ. rewrite RH in VJ. cbn in VJ.
          rewrite ?andb_false_r in VJ. cbn in VJ. first [discriminate VJ | match type of VJ with ?T => idtac "VJ-REM" T end; fail].
        -
          unfold ActrA.sliver_just in SL. destruct (ActrA.stack_wlo st); [|discriminate SL]. destruct (IMap.find ks (s_regs st)); [|discriminate SL].
          apply andb_prop in SL as [SL _]. apply andb_prop in SL as [SL _]. apply andb_prop in SL as [_ SL]. rewrite RB in SL. cbn in SL. discriminate SL. }
    rewrite LOZ, Z.add_0_r in J1. fold Sa0 in J1.
    assert (E2 : bv_unsigned (AP.getr (ms_regs ms) 2) = bv_unsigned (den E (getr st X2))) by (f_equal; exact (GlueA.TwinB.getr_RA bsegs OPS E st ms mo HS X2)).
    unfold sp. rewrite E2. exact J1. }

  pose proof (known_leu_sound_q E st ms mo _ _ HS Q) as KE. rewrite ValP.den_sv_alu in KE. cbn [alu64 alu] in KE. rewrite bv_add_unsigned in KE.
  assert (DV0 : bv_unsigned (den E (VP k wzero)) = Sa0).
  { rewrite ValP.den_VP. change (w2Zs wzero) with 0. rewrite Z.add_0_r. apply Z.mod_small. unfold two64. fold Sa0. lia. }
  rewrite DV0 in KE. change (bv_unsigned (den E (rg_hi rr))) with hz in KE. change (bv_unsigned (den E (VL TOP16))) with (2 ^ 47 - 16) in KE.
  rewrite bv_wrap_small in KE by (unfold bv_modulus; change (2 ^ Z.of_N 64) with (2 ^ 64); lia).

  pose proof (proj1 (Forall_forall _ _) (so_ops _ _ _ _ _ _ HS) _ (UnreggPre.TwinB.find_op_In _ _ _ FZ)) as HO. cbn [op_id op_args map] in HO.
  destruct (OPS_holds_zarg _ _ _ HO) as [AZB ZARG]. fold m in ZARG. set (Az := bv_unsigned (den E az)) in *.
  pose proof (known_leu_sound_q E st ms mo _ _ HS Q0) as KB. rewrite ValP.den_sv_alu in KB. cbn [alu64 alu den] in KB. rewrite bv_add_unsigned in KB.
  fold (den E (VP k wzero)) in KB. rewrite DV0 in KB. fold Az in KB. change (bv_unsigned (wbv (wlit 72%uint63))) with 72 in KB.
  pose proof (bv_unsigned_in_range _ (den E az)) as RAZ. fold Az in RAZ.
  rewrite bv_wrap_small in KB by (unfold bv_modulus; change (2 ^ Z.of_N 64) with (2 ^ 64); lia).
  idtac "SR-2".
  exists ((Sa0 + o) / 64 * 64), ((Sa0 + o + len + 63) / 64 * 64). cbv zeta.
  split; [exact KE|].
  assert (H1 : (Sa0 + o) / 64 * 64 <= Sa0 + o /\ Sa0 + o < (Sa0 + o) / 64 * 64 + 64) by (Z.div_mod_to_equations; lia).
  assert (H2 : Sa0 + o + len <= (Sa0 + o + len + 63) / 64 * 64 /\ (Sa0 + o + len + 63) / 64 * 64 <= 2 ^ 47) by (Z.div_mod_to_equations; lia).
  assert (SH1 : shad (Az + 7) <= shad ((Sa0 + o) / 64 * 64)) by (apply shad_mono; lia).
  assert (SH2 : shad ((Sa0 + o) / 64 * 64) <= shad ((Sa0 + o + len + 63) / 64 * 64)) by (apply shad_mono; lia).
  pose proof (shad_mono _ _ (proj2 H2)) as SH3. rewrite shad_top in SH3.
  assert (SH0 : 0 <= shad (Az + 7)) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; pose proof (Z.div_pos (Az + 7) (2 ^ 3)); lia).
  split; [exact BYT|]. split; [lia|].
  split; [split; [lia|]; right; unfold Shadow.KHIGH, Shadow.KEND; lia|].
  split; [lia|].
  split.
  { split; [lia|]. split; [lia|]. intros G _ G1 G2. exists (Z_to_bv 8 0). split; [| left; reflexivity].
    apply (proj1 (ZARG (ASHOFF + G) ltac:(unfold shad in *; rewrite !Z.shiftr_div_pow2 in * by lia; change (2 ^ 3) with 8 in *; unfold Shadow.KHIGH, ASHOFF in *; Z.div_mod_to_equations; lia))). }
  split; [repeat split; try lia; try (apply Z_mod_mult); unfold Shadow.KEND; lia|].
  split.
  { split; [lia|]. split; [unfold Shadow.KHIGH in *; lia|]. intros i Hi. apply (GlueA.TwinB.wb_wviewA bsegs). apply (proj2 (ZARG (shad ((Sa0 + o) / 64 * 64) + i) ltac:(lia))). }
  split; [apply (rng_sub _ _ _ _ _ (ACCT_rng _ _ _ _ _ _ AC)); lia|].
  apply (rng_sub _ _ _ _ _ (ACCT_rng_stk_sh _ _ _ _ _ _ AC)); [apply shad_mono; lia | lia].
Qed.
End Facts.
End TwinB.
