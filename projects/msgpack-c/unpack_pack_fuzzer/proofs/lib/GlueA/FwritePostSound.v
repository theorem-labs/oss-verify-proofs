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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require I_fwrite.
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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import RangeC RangeFX HalfC VprintfC VprintfSound FwritePostC MemsetPre RangePre.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require UnreggLib.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require UnreggPre.
Unset Nia Cache. Unset Nra Cache.
Import CtrFX ActrA VprintfC FwritePostC.
Module IFW := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.I_fwrite.I_fwrite.
Module AP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec.

Definition FWRITE_POST_SYM : Z := 0x4f4c4.

Section Helpers.
Context {rc : runConstT}.

Lemma mapped_c8s : forall n (m : amem) A, 0 <= A -> A + 8 * Z.of_nat n <= 2 ^ 64 ->
  (forall i, 0 <= i < 8 * Z.of_nat n -> wb asegs m (A + i) = true /\ rb asegs m (A + i) <> None) ->
  exists ws : list word, length ws = n /\ AS.rw_cells asegs m A (map C8 ws).
Proof.
  induction n as [|n IH]; intros m A HA HB H.
  - exists []. split; [reflexivity|]. apply UnreggLib.rw_cells_of_rb; cbn; try lia; try exact I; try (intros i Hi; lia).
  - destruct (IH m (A + 8) ltac:(lia) ltac:(lia)) as (ws & LEN & RW).
    { intros i Hi. replace (A + 8 + i) with (A + (8 + i)) by lia. apply H. lia. }
    destruct (UnreggLib.mapped_chunk asegs m 8 A HA ltac:(lia)) as (j8 & RW8).
    { intros i Hi. apply H. lia. }
    destruct RW8 as [[WF8 BY8] WR8]. cbn [cells_wf cell_wf] in WF8. destruct WF8 as [L8 _].
    cbn [cells_bytes cbytes] in BY8. rewrite app_nil_r in BY8.
    exists (le_bytes_to_word j8 :: ws). split; [cbn; lia|].
    assert (WFm : forall l : list word, cells_wf (map C8 l)) by (induction l; cbn; auto).
    assert (SZ : forall l : list word, cells_size (map C8 l) = (8 * length l)%nat) by (induction l as [|? ? IHl]; cbn [map cells_size csize length]; [reflexivity | rewrite IHl; lia]).
    assert (RT : AM.le8 (le_bytes_to_word j8) = j8).
    { unfold AM.le8, word_to_le_bytes, le_bytes_to_word. rewrite Z_to_bv_unsigned.
      pose proof (MemP.bytes_le_to_Z_bound j8) as BD. rewrite L8 in BD. change (8 * Z.of_nat 8) with 64 in BD.
      rewrite bv_wrap_small by (unfold bv_modulus; exact BD). rewrite <- L8. apply MemFX.MemFX.Z_to_le_bytes_to_Z. }
    apply UnreggLib.rw_cells_of_rb.
    + apply (WFm (_ :: ws)).
    + exact HA.
    + rewrite (SZ (_ :: ws)). cbn [length]. lia.
    + intros i Hi. cbn [map cells_bytes cbytes] in Hi |- *. rewrite RT in Hi |- *.
      destruct (Nat.lt_ge_cases i 8) as [Q|Q].
      * rewrite nth_error_app1 by (rewrite L8; exact Q). destruct BY8 as (_ & _ & B). rewrite (GlueA.rb_mrdA asegs). apply B. rewrite L8. exact Q.
      * rewrite nth_error_app2 by (rewrite L8; exact Q). rewrite L8.
        destruct RW as [[_ (_ & _ & B)] _]. rewrite (GlueA.rb_mrdA asegs). replace (A + Z.of_nat i) with (A + 8 + Z.of_nat (i - 8)) by lia.
        apply B. rewrite length_app, L8 in Hi. lia.
    + intros i Hi. rewrite (SZ (_ :: ws)) in Hi. cbn [length] in Hi. apply H. lia.
Qed.

Lemma mapped_stk : forall (m : amem) lo hi, 0 <= lo -> hi <= 2 ^ 64 ->
  (forall a, lo <= a < hi -> wb asegs m a = true /\ rb asegs m a <> None) -> stk asegs m lo hi.
Proof.
  intros m lo hi H0 H1 H. split; [exact H0|]. split; [exact H1|]. intros a Ha. destruct (H a Ha) as [W Rb]. split.
  - apply (GlueA.wb_wviewA asegs). exact W.
  - rewrite (GlueA.rb_mrdA asegs) in Rb. destruct (AM.mrd asegs m (AM.wa a)) as [b|]; [exists b; reflexivity | contradiction].
Qed.

Lemma zro_range_facts : forall (RNG : footprint) (m : amem) P N, zro_holds m -> rng RNG 0x7fffa000 0xc4000 ->
  LOWIMG_LO <= P -> 0 <= N -> P + N + 64 <= LOWIMG_HI ->
  Shadow.app_blk P (P + N) /\ Shadow.unpoisoned m P (P + N)
  /\ exists RLO RHI, (RLO <= P /\ P + N <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0 /\ 0 <= RLO /\ RHI <= Shadow.KEND)
       /\ ALib.Mem.wr_at asegs m (shad RLO) (shad RHI - shad RLO) /\ rng RNG (shad RLO) (shad RHI - shad RLO).
Proof.
  intros RNG m P N Z RS HP HN HH. unfold LOWIMG_LO, LOWIMG_HI in *.
  split; [split; [lia|]; left; unfold Shadow.KLOW; lia|].
  split.
  { split; [lia|]. split; [lia|]. intros G _ G1 G2. exists (Z_to_bv 8 0). split; [| left; reflexivity].
    apply (proj1 (Z (ASHOFF + G) ltac:(unfold ZRO_LO, ZRO_HI, ASHOFF; lia))). }
  exists (P / 64 * 64), ((P + N + 63) / 64 * 64).
  assert (H1 : P / 64 * 64 <= P /\ 0x10040 <= P / 64 * 64) by (Z.div_mod_to_equations; lia).
  assert (H2 : P + N <= (P + N + 63) / 64 * 64 /\ (P + N + 63) / 64 * 64 <= 0x22c40) by (Z.div_mod_to_equations; lia).
  assert (S1 : shad (P / 64 * 64) <= shad ((P + N + 63) / 64 * 64) /\ ZRO_LO <= shad (P / 64 * 64) /\ shad ((P + N + 63) / 64 * 64) <= ZRO_HI).
  { unfold shad, ASHOFF, ZRO_LO, ZRO_HI. rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. Z.div_mod_to_equations. lia. }
  split; [repeat split; try lia; try (apply Z_mod_mult); unfold Shadow.KEND; lia|].
  split.
  - split; [unfold ZRO_LO in S1; lia|]. split; [unfold ZRO_HI in S1; lia|]. intros i Hi. apply (GlueA.wb_wviewA asegs).
    apply (proj2 (Z (shad (P / 64 * 64) + i) ltac:(lia))).
  - apply (rng_sub _ _ _ _ _ RS); unfold ZRO_LO, ZRO_HI in S1; lia.
Qed.
End Helpers.

Section Sound.
Context {rc : runConstT}.
Variable AI : AMallocIface2.
Variable ACCT : word -> alayout -> footprint -> astate -> list ablock -> Model -> Prop.
Variable UNIV : list (list Z).
Variable Cw : client_world.
Variable OPS : optable.
Hypothesis AI_fake : AI_fake_law AI.
Hypothesis OPS_holds1 : forall args m mo, op_holds OPS HEAP_ID args m mo <-> heap_holdsX AI ACCT UNIV Cw args m mo.
Hypothesis OPS_holds_zro : forall m mo, op_holds OPS ZRO_ID [] m mo -> zro_holds m.
Variable OTHER : Model -> Model -> Prop.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.
Variable NMAXt : nat.
Notation twfS := (twfA node nstepA nexitA (nsafeA NMAXt) fstepS NMAXt).
Hypothesis ACCT_rng : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng RNG (ATOP + 4096) (2^47 - (ATOP + 4096)).
Hypothesis ACCT_rng_aimg : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng_aimg RNG.
Hypothesis ACCT_rng_aimg_sh : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng RNG 0x7fffa000 0xc4000.
Hypothesis ACCT_silent : forall aw L RNG st LBa mo,
  ACCT aw L RNG st LBa mo -> MP mo ->
  exists A0 moc, mrel A0 moc mo /\ minvA moc /\ m_halted moc = None /\
    twfS RNG A0 (Ret (Exc.Ok tt)) moc (acct_leaf_silent ACCT OPS OTHER MP mo aw L st LBa).

Lemma afwrite_post_shape : forall st sts, afwrite_post_apply asegs st = Some sts ->
  exists r hargs wnl st1 ks o2 o8 size res p rss v5 v4 v3 v2 v1 v0 rav,
    acall_pre ASTACK None st = Some (r, hargs, wnl, st1)
    /\ getr st X2 = VP ks o2 /\ getr st X8 = VP ks o8 /\ getr st X9 = VL size /\ getr st X10 = VL res /\ getr st X18 = VL p
    /\ getr st X21 = VL (wlit 1%uint63) /\ IMap.find ks (s_regs st) = Some rss
    /\ wadd o2 (wlit FRAME) = o8 /\ RangeC.in_region rss o2 FRAME = true
    /\ wt size = false /\ wt res = false /\ wt p = false /\ 1 <= to_Z (wl size) /\ to_Z (wl res) * to_Z (wl size) <= 4096
    /\ LOWIMG_LO <= to_Z (wl p) /\ to_Z (wl p) + to_Z (wl res) * to_Z (wl size) + 64 <= LOWIMG_HI
    /\ find_op ZRO_ID (s_ops st) = Some []
    /\ load8 asegs (setpc (setr (clobber st1) X10 (VL res)) r) (cell_addr (VP ks o8) 0%uint63) = Some v5
    /\ load8 asegs (setpc (setr (clobber st1) X10 (VL res)) r) (cell_addr (VP ks o8) 1%uint63) = Some v4
    /\ load8 asegs (setpc (setr (clobber st1) X10 (VL res)) r) (cell_addr (VP ks o8) 2%uint63) = Some v3
    /\ load8 asegs (setpc (setr (clobber st1) X10 (VL res)) r) (cell_addr (VP ks o8) 3%uint63) = Some v2
    /\ load8 asegs (setpc (setr (clobber st1) X10 (VL res)) r) (cell_addr (VP ks o8) 4%uint63) = Some v1
    /\ load8 asegs (setpc (setr (clobber st1) X10 (VL res)) r) (cell_addr (VP ks o8) 5%uint63) = Some v0
    /\ load8 asegs (setpc (setr (clobber st1) X10 (VL res)) r) (cell_addr (VP ks o8) 6%uint63) = Some (VL rav)
    /\ wt rav = false /\ to_Z (wl rav) < 2 ^ 62 /\ PrimInt63.land (wl rav) 1%uint63 = 0%uint63
    /\ sts = [setpc (HalfC.set_regs (setpc (setr (clobber st1) X10 (VL res)) r) (fwp_regs (VP ks o8) rav v5 v4 v3 v2 v1 v0)) (wl rav)].
Proof.
  intros st sts H. unfold afwrite_post_apply in H.
  destruct (acall_pre ASTACK None st) as [[[[r hargs] wnl] st1]|] eqn:P; [|discriminate H].
  destruct (getr st X2) as [|ks o2| | | | | | | | |] eqn:G2; try discriminate H.
  destruct (getr st X8) as [|k8 o8| | | | | | | | |] eqn:G8; try discriminate H.
  destruct (getr st X9) as [size| | | | | | | | | |] eqn:G9; try discriminate H.
  destruct (getr st X10) as [res| | | | | | | | | |] eqn:G10; try discriminate H.
  destruct (getr st X18) as [p| | | | | | | | | |] eqn:G18; try discriminate H.
  destruct (IMap.find ks (s_regs st)) as [rss|] eqn:FR; [|discriminate H]. cbv zeta in H.
  match type of H with (if ?cnd then _ else _) = _ => destruct cnd eqn:CND; [|discriminate H] end.
  repeat match type of CND with (_ && _)%bool = true => let X := fresh "Q" in apply andb_prop in CND as [CND X] end.
  apply Uint63.eqb_correct in CND. subst k8. apply ValP.weqb_eq in Q9. apply negb_true_iff in Q7, Q6, Q5.
  apply Z.leb_le in Q4, Q3, Q2, Q1. unfold CtrS.is_lit in Q0. apply ValP.sv_eqb_eq in Q0.
  destruct (find_op ZRO_ID (s_ops st)) as [[|? ?]|] eqn:FO; try discriminate Q.
  set (st2 := setpc (setr (clobber st1) X10 (VL res)) r) in *.
  destruct (load8 asegs st2 (cell_addr (VP ks o8) 0%uint63)) as [v5|] eqn:L0; [|discriminate H].
  destruct (load8 asegs st2 (cell_addr (VP ks o8) 1%uint63)) as [v4|] eqn:L1; [|discriminate H].
  destruct (load8 asegs st2 (cell_addr (VP ks o8) 2%uint63)) as [v3|] eqn:L2; [|discriminate H].
  destruct (load8 asegs st2 (cell_addr (VP ks o8) 3%uint63)) as [v2|] eqn:L3; [|discriminate H].
  destruct (load8 asegs st2 (cell_addr (VP ks o8) 4%uint63)) as [v1|] eqn:L4; [|discriminate H].
  destruct (load8 asegs st2 (cell_addr (VP ks o8) 5%uint63)) as [v0|] eqn:L5; [|discriminate H].
  destruct (load8 asegs st2 (cell_addr (VP ks o8) 6%uint63)) as [[rav| | | | | | | | | |]|] eqn:L6; try discriminate H.
  match type of H with (if ?cnd then _ else _) = _ => destruct cnd eqn:CR; [|discriminate H] end.
  apply andb_prop in CR as [CR EV]. apply andb_prop in CR as [WR LT]. apply negb_true_iff in WR.
  apply Uint63.ltb_spec in LT. change (to_Z 4611686018427387904%uint63) with (2 ^ 62) in LT. apply Uint63.eqb_correct in EV.
  injection H as <-.
  exists r, hargs, wnl, st1, ks, o2, o8, size, res, p, rss, v5, v4, v3, v2, v1, v0, rav.
  repeat split; try assumption; try reflexivity.
Qed.

Definition afwrite_post_leaf : Prop :=
  forall st (K : TSet) E ms mo r hargs wnl st1 ks o8 res v5 v4 v3 v2 v1 v0 rav (L : alayout) (RNG : footprint) (sta : astate) (LBa : list ablock) (aw : word)
         (s5v s4v s3v s2v s1v s0v ravv : word),
  st_ok asegs OPS E st ms mo -> PB (eb E) ->
  (forall st', In st' [setpc (HalfC.set_regs (setpc (setr (clobber st1) X10 (VL res)) r) (fwp_regs (VP ks o8) rav v5 v4 v3 v2 v1 v0)) (wl rav)] ->
     forall E' ms' mo', env_ext (s_next st) E E' -> MP mo' -> st_ok asegs OPS E' st' ms' mo' -> realizes asegs (mkCfg ms' mo') K) ->
  acall_pre ASTACK None st = Some (r, hargs, wnl, st1) -> getr st X8 = VP ks o8 -> getr st X10 = VL res ->
  load8 asegs (setpc (setr (clobber st1) X10 (VL res)) r) (cell_addr (VP ks o8) 0%uint63) = Some v5 ->
  load8 asegs (setpc (setr (clobber st1) X10 (VL res)) r) (cell_addr (VP ks o8) 1%uint63) = Some v4 ->
  load8 asegs (setpc (setr (clobber st1) X10 (VL res)) r) (cell_addr (VP ks o8) 2%uint63) = Some v3 ->
  load8 asegs (setpc (setr (clobber st1) X10 (VL res)) r) (cell_addr (VP ks o8) 3%uint63) = Some v2 ->
  load8 asegs (setpc (setr (clobber st1) X10 (VL res)) r) (cell_addr (VP ks o8) 4%uint63) = Some v1 ->
  load8 asegs (setpc (setr (clobber st1) X10 (VL res)) r) (cell_addr (VP ks o8) 5%uint63) = Some v0 ->
  load8 asegs (setpc (setr (clobber st1) X10 (VL res)) r) (cell_addr (VP ks o8) 6%uint63) = Some (VL rav) ->
  wt rav = false -> to_Z (wl rav) < 2 ^ 62 -> PrimInt63.land (wl rav) 1%uint63 = 0%uint63 ->
  call_pre st = Some r -> forget_stack_below_sp_g st = Some st1 ->
  CtrPre.acallG AI ACCT UNIV Cw E st ms mo r hargs wnl L RNG sta LBa aw ->
  AHEAP AI L RNG sta LBa (ms_mem ms) -> ALib.Mem.mem_inv asegs (ms_mem ms) ->
  let R := ms_regs ms in
  ATOP + 4096 <= CtrPre.sp_lo E st -> CtrPre.sp_lo E st <= bv_unsigned (AP.getr R 2) - 4096 -> bv_unsigned (AP.getr R 2) < 2 ^ 47 ->
  bv_unsigned (AP.getr R 2) = bv_unsigned (AP.getr R 8) - 2128 -> bv_unsigned (AP.getr R 8) <= 2 ^ 47 ->
  ALib.Step.rw_cells asegs (ms_mem ms) (bv_unsigned (AP.getr R 8) - 56) [C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ravv] ->
  forall ms' mo',
  IFW.fwrite_i_post_post (AP.getr R 8) (AP.getr R 3) (AP.getr R 4) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24) (AP.getr R 25) (AP.getr R 26) (AP.getr R 27)
     (ms_fregs ms) (ms_fcsr ms) ravv s0v s1v s2v s3v s4v s5v (w2Z res) (CtrPre.sp_lo E st) (ms_mem ms) ms' ->
  MP mo' -> op_minv OPS mo' -> OTHER mo mo' -> ACCT aw L RNG sta LBa mo' ->
  realizes asegs (mkCfg ms' mo') K.

Theorem afwrite_post_sound_of_leaf : afwrite_post_leaf ->
  forall pc, to_Z pc = FWRITE_POST_SYM -> contract_sound asegs OPS MP PB (afwrite_post_c asegs pc).
Proof.
  intros LEAF pc Hpc st sts Hspc Happ K E ms mo HS HMP HPB HK. cbn [c_apply c_pc afwrite_post_c] in Happ, Hspc.
  assert (HPC : to_Z (s_pc st) = FWRITE_POST_SYM) by (rewrite Hspc; exact Hpc).
  destruct (afwrite_post_shape st sts Happ) as (r & hargs & wnl & st1 & ks & o2 & o8 & size & res & p & rss & v5 & v4 & v3 & v2 & v1 & v0 & rav
      & PRE & G2 & G8 & G9 & G10 & G18 & G21 & FR & EO8 & INR & WTS & WTR & WTP & SZ1 & NB & PLO & PHI & FZ
      & L0 & L1 & L2 & L3 & L4 & L5 & L6 & WRAV & RAVLT & RAVEV & ->).
  destruct (CtrPre.acall_pre_facts0 AI ACCT UNIV Cw OPS AI_fake OPS_holds1 ACCT_rng ASTACK None st r hargs wnl st1 E ms mo HS ltac:(vm_compute; split; congruence) PRE)
    as (L & RNG & sta & LBa & aw & Ems & AH & AC & UIN & MI & ST & BOT & LO & LOR & TP & RA & RR & SPT & SP16 & RSTK & CP & FS & CF).
  pose proof (AI_rtcells AI _ _ _ _ _ AH) as RT.
  set (R := ms_regs ms) in *. set (m := ms_mem ms) in *.
  pose proof atop_range as ATR.

  pose proof (proj1 (Forall_forall _ _) (so_ops _ _ _ _ _ _ HS) _ (UnreggPre.find_op_In _ _ _ FZ)) as HO. cbn [op_id op_args map] in HO.
  pose proof (OPS_holds_zro _ _ HO) as ZRO. fold m in ZRO.

  assert (KS0 : PrimInt63.eqb ks 0%uint63 = false).
  { destruct CF as (LB & ks' & offs & rss' & ksp & nn & md & Asv & nw & rest & SPR & _). unfold sp_region in SPR. rewrite G2, FR in SPR.
    destruct (PrimInt63.eqb ks 0%uint63); [cbn in SPR; discriminate SPR | reflexivity]. }
  assert (WRS : rg_w rss = true).
  { destruct CF as (LB & ks' & offs & rss' & ksp & nn & md & Asv & nw & rest & SPR & _). unfold sp_region in SPR. rewrite G2, FR in SPR.
    destruct (rg_w rss); [reflexivity|]. rewrite andb_false_r in SPR. cbn in SPR. discriminate SPR. }
  pose proof (so_reg _ _ _ _ _ _ HS ks rss FR) as RO.
  destruct (ro_range _ _ _ _ _ _ RO KS0) as [RG0 RG1]. pose proof (ro_valid _ _ _ _ _ _ RO KS0) as RV.
  destruct (RangeFX.in_region_sound E rss o2 FRAME INR ltac:(change (to_Z FRAME) with 2128; lia)) as (IR1 & IR2 & _).
  pose proof (RangeFX.in_region_end rss o2 FRAME INR ltac:(change (to_Z FRAME) with 2128; lia)) as IRE. rewrite EO8 in IRE.
  change (to_Z FRAME) with 2128 in IR2, IRE.
  set (spm := bv_unsigned (ev E ks) + w2Zs o2) in *.
  assert (E2 : bv_unsigned (AP.getr R (reg_of_r5 X2)) = spm).
  { unfold R. rewrite (GlueA.getr_RA asegs OPS E st ms mo HS X2), G2, ValP.den_VP. apply Z.mod_small. unfold spm, two64 in *. lia. }
  assert (E8 : bv_unsigned (AP.getr R (reg_of_r5 X8)) = spm + 2128).
  { unfold R. rewrite (GlueA.getr_RA asegs OPS E st ms mo HS X8), G8, ValP.den_VP, IRE. replace (bv_unsigned (ev E ks) + (w2Zs o2 + 2128)) with (spm + 2128) by (unfold spm; lia).
    apply Z.mod_small. unfold spm, two64 in *. lia. }
  idtac "PS-1".
  set (sp0 := spm + 2128) in *.
  assert (SP0T : sp0 <= 2 ^ 47).
  { destruct CF as (LB & ks' & offs & rss' & ksp & nn & md & Asv & nw & rest & SPR & Hksp & SPE & K16 & LOSP & FLOOR & Hf & Hc & Eh & Tnw & Nn & Ln & N255
                    & NWI & AN & AJ & TS & WF & HC & AWden & AR).
    assert (KN0 : ks <> 0%uint63) by (intros ->; discriminate KS0).
    pose proof (CallA.aregion_just_sound asegs OPS E st ms mo wnl ks' offs rss' ks rss HS SPR AJ FR KN0) as JU.
    unfold sp_region in SPR. rewrite G2, FR in SPR.
    match type of SPR with (if ?c then _ else _) = _ => destruct c; [|discriminate SPR] end. injection SPR as <- _ _.
    destruct JU as [[_ J]|[NE _]]; [| exfalso; apply NE; reflexivity]. unfold sp0, spm. lia. }
  assert (E2' : bv_unsigned (AP.getr R 2) = spm) by exact E2. assert (E8' : bv_unsigned (AP.getr R 8) = sp0) by exact E8.

  assert (VAL : forall a, spm <= a < sp0 -> wb asegs m a = true /\ rb asegs m a <> None).
  { intros a Ha. destruct (RV a ltac:(unfold sp0, spm in *; lia)) as (V1 & V2 & _). split; [exact (V2 WRS)| exact V1]. }
  assert (STM : stk asegs m spm (sp0 - 56)) by (apply mapped_stk; [unfold spm; lia | unfold sp0; lia | intros a Ha; apply VAL; unfold sp0 in *; lia]).
  destruct (mapped_c8s 7 m (sp0 - 56) ltac:(unfold sp0, spm; lia) ltac:(unfold sp0; lia)) as (ws & LWS & FRC).
  { intros i Hi. apply VAL. unfold sp0 in *. lia. }
  destruct ws as [|s5v [|s4v [|s3v [|s2v [|s1v [|s0v [|ravv [|? ?]]]]]]]]; try discriminate LWS. cbn [map] in FRC.

  pose proof (ACCT_rng_aimg _ _ _ _ _ _ AC) as RIMG. pose proof (ACCT_rng_aimg_sh _ _ _ _ _ _ AC) as RSH.
  set (resZ := w2Z res) in *. set (sizeZ := w2Z size) in *. set (P := w2Z p) in *.
  assert (EW : resZ = to_Z (wl res) /\ sizeZ = to_Z (wl size) /\ P = to_Z (wl p)).
  { unfold resZ, sizeZ, P, w2Z. rewrite WTS, WTR, WTP. lia. }
  destruct EW as (EWr & EWs & EWp). rewrite <- EWr, <- EWs in NB, PHI. rewrite <- EWs in SZ1. rewrite <- EWp in PLO, PHI.
  pose proof (w2Z_range res) as RRES. fold resZ in RRES.
  destruct (zro_range_facts RNG m P (resZ * sizeZ) ZRO RSH PLO ltac:(nia) PHI) as (APP & UNP & RLO & RHI & HULL & WRH & RNGH).
  idtac "PS-2".

  assert (EQ2 : AP.getr R 2 = Z_to_bv 64 (bv_unsigned (AP.getr R 8) + -2128)).
  { apply bv_eq. rewrite Z_to_bv_unsigned, E2', E8'. unfold sp0. replace (spm + 2128 + -2128) with spm by lia.
    symmetry. apply bv_wrap_small. unfold bv_modulus. unfold spm in *. change (2 ^ Z.of_N 64) with (2 ^ 64). unfold two64 in *. lia. }
  assert (EQ10 : AP.getr R 10 = Z_to_bv 64 resZ).
  { change (AP.getr R 10) with (AP.getr R (reg_of_r5 X10)). unfold R. rewrite (GlueA.getr_RA asegs OPS E st ms mo HS X10), G10. reflexivity. }
  assert (EQ21 : AP.getr R 21 = Z_to_bv 64 1).
  { change (AP.getr R 21) with (AP.getr R (reg_of_r5 X21)). unfold R. rewrite (GlueA.getr_RA asegs OPS E st ms mo HS X21), G21. reflexivity. }
  assert (EQ9 : AP.getr R 9 = Z_to_bv 64 sizeZ).
  { change (AP.getr R 9) with (AP.getr R (reg_of_r5 X9)). unfold R. rewrite (GlueA.getr_RA asegs OPS E st ms mo HS X9), G9. reflexivity. }
  assert (EQ18 : bv_unsigned (AP.getr R 18) = P).
  { change (AP.getr R 18) with (AP.getr R (reg_of_r5 X18)). unfold R. rewrite (GlueA.getr_RA asegs OPS E st ms mo HS X18), G18. cbn [den]. apply wbv_unsigned. }
  idtac "PS-3".
  destruct (ACCT_silent aw L RNG sta LBa mo AC HMP) as (AL0 & moc & MR & MINV & HH & TW).
  assert (RSTK0 : rng RNG (CtrPre.sp_lo E st) (sp0 - CtrPre.sp_lo E st)).
  { apply (rng_sub _ _ _ _ _ (ACCT_rng _ _ _ _ _ _ AC)); lia. }
  assert (EV : evtF asegs RNG
            (IFW.fwrite_i_post_post (AP.getr R 8) (AP.getr R 3) (AP.getr R 4) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24) (AP.getr R 25)
               (AP.getr R 26) (AP.getr R 27) (ms_fregs ms) (ms_fcsr ms) ravv s0v s1v s2v s3v s4v s5v resZ (CtrPre.sp_lo E st) m)
            (MS (mkR (AP.getr R 1) (Z_to_bv 64 (bv_unsigned (AP.getr R 8) + -2128)) (AP.getr R 3) (AP.getr R 4) (AP.getr R 5) (AP.getr R 6) (AP.getr R 7) (AP.getr R 8)
                (AP.getr R 9) (Z_to_bv 64 resZ) (AP.getr R 11) (AP.getr R 12) (AP.getr R 13) (AP.getr R 14) (AP.getr R 15) (AP.getr R 16)
                (AP.getr R 17) (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (Z_to_bv 64 1) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24)
                (AP.getr R 25) (AP.getr R 26) (AP.getr R 27) (AP.getr R 28) (AP.getr R 29) (AP.getr R 30) (AP.getr R 31))
                (ms_fregs ms) (Z_to_bv 64 FWRITE_POST_SYM) (ms_fcsr ms) None m (seg_rom asegs))).
  { unfold artcells in RT. decompose [and] RT. clear RT.
    eapply (IFW.fwrite_i_post RNG) with (size := sizeZ) (N := resZ * sizeZ) (RLO := RLO) (RHI := RHI).
    all: rewrite ?E8', ?EQ18.
    all: try lazymatch goal with
         | |- ALib.Mem.mem_inv _ _ => exact MI
         | |- stk _ _ _ _ => first [ replace (sp0 - 2128) with spm by (unfold sp0; lia); rewrite <- E2'; exact ST
                                   | replace (sp0 - 2128) with spm by (unfold sp0; lia); exact STM ]
         | |- ALib.Step.rw_cells _ _ _ _ => first [exact FRC | assumption]
         | |- Shadow.unpoisoned _ _ _ => exact UNP
         | |- Shadow.app_blk _ _ => exact APP
         | |- ALib.Mem.wr_at _ _ _ _ => exact WRH
         | |- rng_aimg _ => exact RIMG
         | |- rng _ (shad _) _ => exact RNGH
         | |- rng _ _ _ => exact RSTK0
         | |- _ = Z_to_bv 64 _ => exact EQ9
         | |- _ * _ = _ => reflexivity
         | |- _ <= _ /\ _ => exact HULL
         end.
    all: try (unfold Shadow.KHIGH, sp0 in *; lia).
    all: try (unfold Shadow.KHIGH, sp0 in *; nia).
    all: match goal with |- ?G => idtac "REMW" G end. }
  rewrite <- EQ2, <- EQ10, <- EQ21 in EV.
  assert (F1 : bv_unsigned (AP.getr R 2) = bv_unsigned (AP.getr R 8) - 2128) by (rewrite E2', E8'; unfold sp0; lia).
  assert (F2 : bv_unsigned (AP.getr R 8) <= 2 ^ 47) by (rewrite E8'; lia).
  assert (F3 : ALib.Step.rw_cells asegs m (bv_unsigned (AP.getr R 8) - 56) [C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ravv]) by (rewrite E8'; exact FRC).
  rewrite Ems, HPC. apply (GlueA.realizes_to_mkRA asegs).
  eapply (implS_twfS_realizes_silent asegs NMAXt (Ret (Exc.Ok tt)) RNG AL0
            (fun (_ : unit) (RNGq : footprint) ms' => RNGq = RNG /\ IFW.fwrite_i_post_post (AP.getr R 8) (AP.getr R 3) (AP.getr R 4) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24) (AP.getr R 25)
               (AP.getr R 26) (AP.getr R 27) (ms_fregs ms) (ms_fcsr ms) ravv s0v s1v s2v s3v s4v s5v resZ (CtrPre.sp_lo E st) m ms')
            _ _ moc mo K).
  - cbn [implF epostF]. eapply evtF_mono; [exact EV|]. intros ms' PO. split; [reflexivity| exact PO].
  - exact TW.
  - exact HH.
  - exact MINV.
  - exact MR.
  - intros rr RNG' A' ms' moc' mo' HQ HP' ACC' HH' MINV' MR'.
    destruct (HP' mo' MR') as (HMP' & HMI' & OTH & ACP). destruct HQ as [-> HQ].
    exact (LEAF st K E ms mo r hargs wnl st1 ks o8 res v5 v4 v3 v2 v1 v0 rav L RNG sta LBa aw s5v s4v s3v s2v s1v s0v ravv HS HPB HK PRE G8 G10
             L0 L1 L2 L3 L4 L5 L6 WRAV RAVLT RAVEV CP FS CF AH MI BOT LO SPT F1 F2 F3 ms' mo' HQ HMP' HMI' OTH ACP).
Qed.
End Sound.

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
Import RangeC.TwinB RangeFX.TwinB HalfC.TwinB VprintfC.TwinB VprintfSound.TwinB FwritePostC.TwinB MemsetPre.TwinB RangePre.TwinB.

Unset Nia Cache. Unset Nra Cache.
Import CtrFX ActrA VprintfC.TwinB.VprintfC FwritePostC.TwinB.FwritePostC.
Module IFW := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.I_fwrite.TwinB.I_fwrite.
Module AP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec.

Definition FWRITE_POST_SYM : Z := 0x4fe54.

Section Helpers.
Context {rc : runConstT}.

Lemma mapped_c8s : forall n (m : amem) A, 0 <= A -> A + 8 * Z.of_nat n <= 2 ^ 64 ->
  (forall i, 0 <= i < 8 * Z.of_nat n -> wb bsegs m (A + i) = true /\ rb bsegs m (A + i) <> None) ->
  exists ws : list word, length ws = n /\ AS.rw_cells bsegs m A (map C8 ws).
Proof.
  induction n as [|n IH]; intros m A HA HB H.
  - exists []. split; [reflexivity|]. apply UnreggLib.TwinB.rw_cells_of_rb; cbn; try lia; try exact I; try (intros i Hi; lia).
  - destruct (IH m (A + 8) ltac:(lia) ltac:(lia)) as (ws & LEN & RW).
    { intros i Hi. replace (A + 8 + i) with (A + (8 + i)) by lia. apply H. lia. }
    destruct (UnreggLib.TwinB.mapped_chunk bsegs m 8 A HA ltac:(lia)) as (j8 & RW8).
    { intros i Hi. apply H. lia. }
    destruct RW8 as [[WF8 BY8] WR8]. cbn [cells_wf cell_wf] in WF8. destruct WF8 as [L8 _].
    cbn [cells_bytes cbytes] in BY8. rewrite app_nil_r in BY8.
    exists (le_bytes_to_word j8 :: ws). split; [cbn; lia|].
    assert (WFm : forall l : list word, cells_wf (map C8 l)) by (induction l; cbn; auto).
    assert (SZ : forall l : list word, cells_size (map C8 l) = (8 * length l)%nat) by (induction l as [|? ? IHl]; cbn [map cells_size csize length]; [reflexivity | rewrite IHl; lia]).
    assert (RT : AM.le8 (le_bytes_to_word j8) = j8).
    { unfold AM.le8, word_to_le_bytes, le_bytes_to_word. rewrite Z_to_bv_unsigned.
      pose proof (MemP.bytes_le_to_Z_bound j8) as BD. rewrite L8 in BD. change (8 * Z.of_nat 8) with 64 in BD.
      rewrite bv_wrap_small by (unfold bv_modulus; exact BD). rewrite <- L8. apply MemFX.MemFX.Z_to_le_bytes_to_Z. }
    apply UnreggLib.TwinB.rw_cells_of_rb.
    + apply (WFm (_ :: ws)).
    + exact HA.
    + rewrite (SZ (_ :: ws)). cbn [length]. lia.
    + intros i Hi. cbn [map cells_bytes cbytes] in Hi |- *. rewrite RT in Hi |- *.
      destruct (Nat.lt_ge_cases i 8) as [Q|Q].
      * rewrite nth_error_app1 by (rewrite L8; exact Q). destruct BY8 as (_ & _ & B). rewrite (GlueA.TwinB.rb_mrdA bsegs). apply B. rewrite L8. exact Q.
      * rewrite nth_error_app2 by (rewrite L8; exact Q). rewrite L8.
        destruct RW as [[_ (_ & _ & B)] _]. rewrite (GlueA.TwinB.rb_mrdA bsegs). replace (A + Z.of_nat i) with (A + 8 + Z.of_nat (i - 8)) by lia.
        apply B. rewrite length_app, L8 in Hi. lia.
    + intros i Hi. rewrite (SZ (_ :: ws)) in Hi. cbn [length] in Hi. apply H. lia.
Qed.

Lemma mapped_stk : forall (m : amem) lo hi, 0 <= lo -> hi <= 2 ^ 64 ->
  (forall a, lo <= a < hi -> wb bsegs m a = true /\ rb bsegs m a <> None) -> stk bsegs m lo hi.
Proof.
  intros m lo hi H0 H1 H. split; [exact H0|]. split; [exact H1|]. intros a Ha. destruct (H a Ha) as [W Rb]. split.
  - apply (GlueA.TwinB.wb_wviewA bsegs). exact W.
  - rewrite (GlueA.TwinB.rb_mrdA bsegs) in Rb. destruct (AM.mrd bsegs m (AM.wa a)) as [b|]; [exists b; reflexivity | contradiction].
Qed.

Lemma zro_range_facts : forall (RNG : footprint) (m : amem) P N, zro_holds m -> rng RNG 0x7fffa000 0xc5000 ->
  LOWIMG_LO <= P -> 0 <= N -> P + N + 64 <= LOWIMG_HI ->
  Shadow.app_blk P (P + N) /\ Shadow.unpoisoned m P (P + N)
  /\ exists RLO RHI, (RLO <= P /\ P + N <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0 /\ 0 <= RLO /\ RHI <= Shadow.KEND)
       /\ ALib.Mem.wr_at bsegs m (shad RLO) (shad RHI - shad RLO) /\ rng RNG (shad RLO) (shad RHI - shad RLO).
Proof.
  intros RNG m P N Z RS HP HN HH. unfold LOWIMG_LO, LOWIMG_HI in *.
  split; [split; [lia|]; left; unfold Shadow.KLOW; lia|].
  split.
  { split; [lia|]. split; [lia|]. intros G _ G1 G2. exists (Z_to_bv 8 0). split; [| left; reflexivity].
    apply (proj1 (Z (ASHOFF + G) ltac:(unfold ZRO_LO, ZRO_HI, ASHOFF; lia))). }
  exists (P / 64 * 64), ((P + N + 63) / 64 * 64).
  assert (H1 : P / 64 * 64 <= P /\ 0x10040 <= P / 64 * 64) by (Z.div_mod_to_equations; lia).
  assert (H2 : P + N <= (P + N + 63) / 64 * 64 /\ (P + N + 63) / 64 * 64 <= 0x22cc0) by (Z.div_mod_to_equations; lia).
  assert (S1 : shad (P / 64 * 64) <= shad ((P + N + 63) / 64 * 64) /\ ZRO_LO <= shad (P / 64 * 64) /\ shad ((P + N + 63) / 64 * 64) <= ZRO_HI).
  { unfold shad, ASHOFF, ZRO_LO, ZRO_HI. rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. Z.div_mod_to_equations. lia. }
  split; [repeat split; try lia; try (apply Z_mod_mult); unfold Shadow.KEND; lia|].
  split.
  - split; [unfold ZRO_LO in S1; lia|]. split; [unfold ZRO_HI in S1; lia|]. intros i Hi. apply (GlueA.TwinB.wb_wviewA bsegs).
    apply (proj2 (Z (shad (P / 64 * 64) + i) ltac:(lia))).
  - apply (rng_sub _ _ _ _ _ RS); unfold ZRO_LO, ZRO_HI in S1; lia.
Qed.
End Helpers.

Section Sound.
Context {rc : runConstT}.
Variable AI : AMallocIface2.
Variable ACCT : word -> alayout -> footprint -> astate -> list ablock -> Model -> Prop.
Variable UNIV : list (list Z).
Variable Cw : client_world.
Variable OPS : optable.
Hypothesis AI_fake : AI_fake_law AI.
Hypothesis OPS_holds1 : forall args m mo, op_holds OPS HEAP_ID args m mo <-> heap_holdsX AI ACCT UNIV Cw args m mo.
Hypothesis OPS_holds_zro : forall m mo, op_holds OPS ZRO_ID [] m mo -> zro_holds m.
Variable OTHER : Model -> Model -> Prop.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.
Variable NMAXt : nat.
Notation twfS := (twfA node nstepA nexitA (nsafeA NMAXt) fstepS NMAXt).
Hypothesis ACCT_rng : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng RNG (ATOP + 4096) (2^47 - (ATOP + 4096)).
Hypothesis ACCT_rng_aimg : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng_aimg RNG.
Hypothesis ACCT_rng_aimg_sh : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng RNG 0x7fffa000 0xc5000.
Hypothesis ACCT_silent : forall aw L RNG st LBa mo,
  ACCT aw L RNG st LBa mo -> MP mo ->
  exists A0 moc, mrel A0 moc mo /\ minvA moc /\ m_halted moc = None /\
    twfS RNG A0 (Ret (Exc.Ok tt)) moc (acct_leaf_silent ACCT OPS OTHER MP mo aw L st LBa).

Lemma afwrite_post_shape : forall st sts, afwrite_post_apply bsegs st = Some sts ->
  exists r hargs wnl st1 ks o2 o8 size res p rss v5 v4 v3 v2 v1 v0 rav,
    acall_pre ASTACK None st = Some (r, hargs, wnl, st1)
    /\ getr st X2 = VP ks o2 /\ getr st X8 = VP ks o8 /\ getr st X9 = VL size /\ getr st X10 = VL res /\ getr st X18 = VL p
    /\ getr st X21 = VL (wlit 1%uint63) /\ IMap.find ks (s_regs st) = Some rss
    /\ wadd o2 (wlit FRAME) = o8 /\ RangeC.TwinB.RangeC.in_region rss o2 FRAME = true
    /\ wt size = false /\ wt res = false /\ wt p = false /\ 1 <= to_Z (wl size) /\ to_Z (wl res) * to_Z (wl size) <= 4096
    /\ LOWIMG_LO <= to_Z (wl p) /\ to_Z (wl p) + to_Z (wl res) * to_Z (wl size) + 64 <= LOWIMG_HI
    /\ find_op ZRO_ID (s_ops st) = Some []
    /\ load8 bsegs (setpc (setr (clobber st1) X10 (VL res)) r) (cell_addr (VP ks o8) 0%uint63) = Some v5
    /\ load8 bsegs (setpc (setr (clobber st1) X10 (VL res)) r) (cell_addr (VP ks o8) 1%uint63) = Some v4
    /\ load8 bsegs (setpc (setr (clobber st1) X10 (VL res)) r) (cell_addr (VP ks o8) 2%uint63) = Some v3
    /\ load8 bsegs (setpc (setr (clobber st1) X10 (VL res)) r) (cell_addr (VP ks o8) 3%uint63) = Some v2
    /\ load8 bsegs (setpc (setr (clobber st1) X10 (VL res)) r) (cell_addr (VP ks o8) 4%uint63) = Some v1
    /\ load8 bsegs (setpc (setr (clobber st1) X10 (VL res)) r) (cell_addr (VP ks o8) 5%uint63) = Some v0
    /\ load8 bsegs (setpc (setr (clobber st1) X10 (VL res)) r) (cell_addr (VP ks o8) 6%uint63) = Some (VL rav)
    /\ wt rav = false /\ to_Z (wl rav) < 2 ^ 62 /\ PrimInt63.land (wl rav) 1%uint63 = 0%uint63
    /\ sts = [setpc (HalfC.TwinB.HalfC.set_regs (setpc (setr (clobber st1) X10 (VL res)) r) (fwp_regs (VP ks o8) rav v5 v4 v3 v2 v1 v0)) (wl rav)].
Proof.
  intros st sts H. unfold afwrite_post_apply in H.
  destruct (acall_pre ASTACK None st) as [[[[r hargs] wnl] st1]|] eqn:P; [|discriminate H].
  destruct (getr st X2) as [|ks o2| | | | | | | | |] eqn:G2; try discriminate H.
  destruct (getr st X8) as [|k8 o8| | | | | | | | |] eqn:G8; try discriminate H.
  destruct (getr st X9) as [size| | | | | | | | | |] eqn:G9; try discriminate H.
  destruct (getr st X10) as [res| | | | | | | | | |] eqn:G10; try discriminate H.
  destruct (getr st X18) as [p| | | | | | | | | |] eqn:G18; try discriminate H.
  destruct (IMap.find ks (s_regs st)) as [rss|] eqn:FR; [|discriminate H]. cbv zeta in H.
  match type of H with (if ?cnd then _ else _) = _ => destruct cnd eqn:CND; [|discriminate H] end.
  repeat match type of CND with (_ && _)%bool = true => let X := fresh "Q" in apply andb_prop in CND as [CND X] end.
  apply Uint63.eqb_correct in CND. subst k8. apply ValP.weqb_eq in Q9. apply negb_true_iff in Q7, Q6, Q5.
  apply Z.leb_le in Q4, Q3, Q2, Q1. unfold CtrS.is_lit in Q0. apply ValP.sv_eqb_eq in Q0.
  destruct (find_op ZRO_ID (s_ops st)) as [[|? ?]|] eqn:FO; try discriminate Q.
  set (st2 := setpc (setr (clobber st1) X10 (VL res)) r) in *.
  destruct (load8 bsegs st2 (cell_addr (VP ks o8) 0%uint63)) as [v5|] eqn:L0; [|discriminate H].
  destruct (load8 bsegs st2 (cell_addr (VP ks o8) 1%uint63)) as [v4|] eqn:L1; [|discriminate H].
  destruct (load8 bsegs st2 (cell_addr (VP ks o8) 2%uint63)) as [v3|] eqn:L2; [|discriminate H].
  destruct (load8 bsegs st2 (cell_addr (VP ks o8) 3%uint63)) as [v2|] eqn:L3; [|discriminate H].
  destruct (load8 bsegs st2 (cell_addr (VP ks o8) 4%uint63)) as [v1|] eqn:L4; [|discriminate H].
  destruct (load8 bsegs st2 (cell_addr (VP ks o8) 5%uint63)) as [v0|] eqn:L5; [|discriminate H].
  destruct (load8 bsegs st2 (cell_addr (VP ks o8) 6%uint63)) as [[rav| | | | | | | | | |]|] eqn:L6; try discriminate H.
  match type of H with (if ?cnd then _ else _) = _ => destruct cnd eqn:CR; [|discriminate H] end.
  apply andb_prop in CR as [CR EV]. apply andb_prop in CR as [WR LT]. apply negb_true_iff in WR.
  apply Uint63.ltb_spec in LT. change (to_Z 4611686018427387904%uint63) with (2 ^ 62) in LT. apply Uint63.eqb_correct in EV.
  injection H as <-.
  exists r, hargs, wnl, st1, ks, o2, o8, size, res, p, rss, v5, v4, v3, v2, v1, v0, rav.
  repeat split; try assumption; try reflexivity.
Qed.

Definition afwrite_post_leaf : Prop :=
  forall st (K : TSet) E ms mo r hargs wnl st1 ks o8 res v5 v4 v3 v2 v1 v0 rav (L : alayout) (RNG : footprint) (sta : astate) (LBa : list ablock) (aw : word)
         (s5v s4v s3v s2v s1v s0v ravv : word),
  st_ok bsegs OPS E st ms mo -> PB (eb E) ->
  (forall st', In st' [setpc (HalfC.TwinB.HalfC.set_regs (setpc (setr (clobber st1) X10 (VL res)) r) (fwp_regs (VP ks o8) rav v5 v4 v3 v2 v1 v0)) (wl rav)] ->
     forall E' ms' mo', env_ext (s_next st) E E' -> MP mo' -> st_ok bsegs OPS E' st' ms' mo' -> realizes bsegs (mkCfg ms' mo') K) ->
  acall_pre ASTACK None st = Some (r, hargs, wnl, st1) -> getr st X8 = VP ks o8 -> getr st X10 = VL res ->
  load8 bsegs (setpc (setr (clobber st1) X10 (VL res)) r) (cell_addr (VP ks o8) 0%uint63) = Some v5 ->
  load8 bsegs (setpc (setr (clobber st1) X10 (VL res)) r) (cell_addr (VP ks o8) 1%uint63) = Some v4 ->
  load8 bsegs (setpc (setr (clobber st1) X10 (VL res)) r) (cell_addr (VP ks o8) 2%uint63) = Some v3 ->
  load8 bsegs (setpc (setr (clobber st1) X10 (VL res)) r) (cell_addr (VP ks o8) 3%uint63) = Some v2 ->
  load8 bsegs (setpc (setr (clobber st1) X10 (VL res)) r) (cell_addr (VP ks o8) 4%uint63) = Some v1 ->
  load8 bsegs (setpc (setr (clobber st1) X10 (VL res)) r) (cell_addr (VP ks o8) 5%uint63) = Some v0 ->
  load8 bsegs (setpc (setr (clobber st1) X10 (VL res)) r) (cell_addr (VP ks o8) 6%uint63) = Some (VL rav) ->
  wt rav = false -> to_Z (wl rav) < 2 ^ 62 -> PrimInt63.land (wl rav) 1%uint63 = 0%uint63 ->
  call_pre st = Some r -> forget_stack_below_sp_g st = Some st1 ->
  CtrPre.TwinB.acallG AI ACCT UNIV Cw E st ms mo r hargs wnl L RNG sta LBa aw ->
  AHEAP AI L RNG sta LBa (ms_mem ms) -> ALib.Mem.mem_inv bsegs (ms_mem ms) ->
  let R := ms_regs ms in
  ATOP + 4096 <= CtrPre.TwinB.sp_lo E st -> CtrPre.TwinB.sp_lo E st <= bv_unsigned (AP.getr R 2) - 4096 -> bv_unsigned (AP.getr R 2) < 2 ^ 47 ->
  bv_unsigned (AP.getr R 2) = bv_unsigned (AP.getr R 8) - 2128 -> bv_unsigned (AP.getr R 8) <= 2 ^ 47 ->
  ALib.Step.rw_cells bsegs (ms_mem ms) (bv_unsigned (AP.getr R 8) - 56) [C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ravv] ->
  forall ms' mo',
  IFW.fwrite_i_post_post (AP.getr R 8) (AP.getr R 3) (AP.getr R 4) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24) (AP.getr R 25) (AP.getr R 26) (AP.getr R 27)
     (ms_fregs ms) (ms_fcsr ms) ravv s0v s1v s2v s3v s4v s5v (w2Z res) (CtrPre.TwinB.sp_lo E st) (ms_mem ms) ms' ->
  MP mo' -> op_minv OPS mo' -> OTHER mo mo' -> ACCT aw L RNG sta LBa mo' ->
  realizes bsegs (mkCfg ms' mo') K.

Theorem afwrite_post_sound_of_leaf : afwrite_post_leaf ->
  forall pc, to_Z pc = FWRITE_POST_SYM -> contract_sound bsegs OPS MP PB (afwrite_post_c bsegs pc).
Proof.
  intros LEAF pc Hpc st sts Hspc Happ K E ms mo HS HMP HPB HK. cbn [c_apply c_pc afwrite_post_c] in Happ, Hspc.
  assert (HPC : to_Z (s_pc st) = FWRITE_POST_SYM) by (rewrite Hspc; exact Hpc).
  destruct (afwrite_post_shape st sts Happ) as (r & hargs & wnl & st1 & ks & o2 & o8 & size & res & p & rss & v5 & v4 & v3 & v2 & v1 & v0 & rav
      & PRE & G2 & G8 & G9 & G10 & G18 & G21 & FR & EO8 & INR & WTS & WTR & WTP & SZ1 & NB & PLO & PHI & FZ
      & L0 & L1 & L2 & L3 & L4 & L5 & L6 & WRAV & RAVLT & RAVEV & ->).
  destruct (CtrPre.TwinB.acall_pre_facts0 AI ACCT UNIV Cw OPS AI_fake OPS_holds1 ACCT_rng ASTACK None st r hargs wnl st1 E ms mo HS ltac:(vm_compute; split; congruence) PRE)
    as (L & RNG & sta & LBa & aw & Ems & AH & AC & UIN & MI & ST & BOT & LO & LOR & TP & RA & RR & SPT & SP16 & RSTK & CP & FS & CF).
  pose proof (AI_rtcells AI _ _ _ _ _ AH) as RT.
  set (R := ms_regs ms) in *. set (m := ms_mem ms) in *.
  pose proof atop_range as ATR.

  pose proof (proj1 (Forall_forall _ _) (so_ops _ _ _ _ _ _ HS) _ (UnreggPre.TwinB.find_op_In _ _ _ FZ)) as HO. cbn [op_id op_args map] in HO.
  pose proof (OPS_holds_zro _ _ HO) as ZRO. fold m in ZRO.

  assert (KS0 : PrimInt63.eqb ks 0%uint63 = false).
  { destruct CF as (LB & ks' & offs & rss' & ksp & nn & md & Asv & nw & rest & SPR & _). unfold sp_region in SPR. rewrite G2, FR in SPR.
    destruct (PrimInt63.eqb ks 0%uint63); [cbn in SPR; discriminate SPR | reflexivity]. }
  assert (WRS : rg_w rss = true).
  { destruct CF as (LB & ks' & offs & rss' & ksp & nn & md & Asv & nw & rest & SPR & _). unfold sp_region in SPR. rewrite G2, FR in SPR.
    destruct (rg_w rss); [reflexivity|]. rewrite andb_false_r in SPR. cbn in SPR. discriminate SPR. }
  pose proof (so_reg _ _ _ _ _ _ HS ks rss FR) as RO.
  destruct (ro_range _ _ _ _ _ _ RO KS0) as [RG0 RG1]. pose proof (ro_valid _ _ _ _ _ _ RO KS0) as RV.
  destruct (RangeFX.TwinB.RangeFX.in_region_sound E rss o2 FRAME INR ltac:(change (to_Z FRAME) with 2128; lia)) as (IR1 & IR2 & _).
  pose proof (RangeFX.TwinB.RangeFX.in_region_end rss o2 FRAME INR ltac:(change (to_Z FRAME) with 2128; lia)) as IRE. rewrite EO8 in IRE.
  change (to_Z FRAME) with 2128 in IR2, IRE.
  set (spm := bv_unsigned (ev E ks) + w2Zs o2) in *.
  assert (E2 : bv_unsigned (AP.getr R (reg_of_r5 X2)) = spm).
  { unfold R. rewrite (GlueA.TwinB.getr_RA bsegs OPS E st ms mo HS X2), G2, ValP.den_VP. apply Z.mod_small. unfold spm, two64 in *. lia. }
  assert (E8 : bv_unsigned (AP.getr R (reg_of_r5 X8)) = spm + 2128).
  { unfold R. rewrite (GlueA.TwinB.getr_RA bsegs OPS E st ms mo HS X8), G8, ValP.den_VP, IRE. replace (bv_unsigned (ev E ks) + (w2Zs o2 + 2128)) with (spm + 2128) by (unfold spm; lia).
    apply Z.mod_small. unfold spm, two64 in *. lia. }
  idtac "PS-1".
  set (sp0 := spm + 2128) in *.
  assert (SP0T : sp0 <= 2 ^ 47).
  { destruct CF as (LB & ks' & offs & rss' & ksp & nn & md & Asv & nw & rest & SPR & Hksp & SPE & K16 & LOSP & FLOOR & Hf & Hc & Eh & Tnw & Nn & Ln & N255
                    & NWI & AN & AJ & TS & WF & HC & AWden & AR).
    assert (KN0 : ks <> 0%uint63) by (intros ->; discriminate KS0).
    pose proof (CallA.TwinB.aregion_just_sound bsegs OPS E st ms mo wnl ks' offs rss' ks rss HS SPR AJ FR KN0) as JU.
    unfold sp_region in SPR. rewrite G2, FR in SPR.
    match type of SPR with (if ?c then _ else _) = _ => destruct c; [|discriminate SPR] end. injection SPR as <- _ _.
    destruct JU as [[_ J]|[NE _]]; [| exfalso; apply NE; reflexivity]. unfold sp0, spm. lia. }
  assert (E2' : bv_unsigned (AP.getr R 2) = spm) by exact E2. assert (E8' : bv_unsigned (AP.getr R 8) = sp0) by exact E8.

  assert (VAL : forall a, spm <= a < sp0 -> wb bsegs m a = true /\ rb bsegs m a <> None).
  { intros a Ha. destruct (RV a ltac:(unfold sp0, spm in *; lia)) as (V1 & V2 & _). split; [exact (V2 WRS)| exact V1]. }
  assert (STM : stk bsegs m spm (sp0 - 56)) by (apply mapped_stk; [unfold spm; lia | unfold sp0; lia | intros a Ha; apply VAL; unfold sp0 in *; lia]).
  destruct (mapped_c8s 7 m (sp0 - 56) ltac:(unfold sp0, spm; lia) ltac:(unfold sp0; lia)) as (ws & LWS & FRC).
  { intros i Hi. apply VAL. unfold sp0 in *. lia. }
  destruct ws as [|s5v [|s4v [|s3v [|s2v [|s1v [|s0v [|ravv [|? ?]]]]]]]]; try discriminate LWS. cbn [map] in FRC.

  pose proof (ACCT_rng_aimg _ _ _ _ _ _ AC) as RIMG. pose proof (ACCT_rng_aimg_sh _ _ _ _ _ _ AC) as RSH.
  set (resZ := w2Z res) in *. set (sizeZ := w2Z size) in *. set (P := w2Z p) in *.
  assert (EW : resZ = to_Z (wl res) /\ sizeZ = to_Z (wl size) /\ P = to_Z (wl p)).
  { unfold resZ, sizeZ, P, w2Z. rewrite WTS, WTR, WTP. lia. }
  destruct EW as (EWr & EWs & EWp). rewrite <- EWr, <- EWs in NB, PHI. rewrite <- EWs in SZ1. rewrite <- EWp in PLO, PHI.
  pose proof (w2Z_range res) as RRES. fold resZ in RRES.
  destruct (zro_range_facts RNG m P (resZ * sizeZ) ZRO RSH PLO ltac:(nia) PHI) as (APP & UNP & RLO & RHI & HULL & WRH & RNGH).
  idtac "PS-2".

  assert (EQ2 : AP.getr R 2 = Z_to_bv 64 (bv_unsigned (AP.getr R 8) + -2128)).
  { apply bv_eq. rewrite Z_to_bv_unsigned, E2', E8'. unfold sp0. replace (spm + 2128 + -2128) with spm by lia.
    symmetry. apply bv_wrap_small. unfold bv_modulus. unfold spm in *. change (2 ^ Z.of_N 64) with (2 ^ 64). unfold two64 in *. lia. }
  assert (EQ10 : AP.getr R 10 = Z_to_bv 64 resZ).
  { change (AP.getr R 10) with (AP.getr R (reg_of_r5 X10)). unfold R. rewrite (GlueA.TwinB.getr_RA bsegs OPS E st ms mo HS X10), G10. reflexivity. }
  assert (EQ21 : AP.getr R 21 = Z_to_bv 64 1).
  { change (AP.getr R 21) with (AP.getr R (reg_of_r5 X21)). unfold R. rewrite (GlueA.TwinB.getr_RA bsegs OPS E st ms mo HS X21), G21. reflexivity. }
  assert (EQ9 : AP.getr R 9 = Z_to_bv 64 sizeZ).
  { change (AP.getr R 9) with (AP.getr R (reg_of_r5 X9)). unfold R. rewrite (GlueA.TwinB.getr_RA bsegs OPS E st ms mo HS X9), G9. reflexivity. }
  assert (EQ18 : bv_unsigned (AP.getr R 18) = P).
  { change (AP.getr R 18) with (AP.getr R (reg_of_r5 X18)). unfold R. rewrite (GlueA.TwinB.getr_RA bsegs OPS E st ms mo HS X18), G18. cbn [den]. apply wbv_unsigned. }
  idtac "PS-3".
  destruct (ACCT_silent aw L RNG sta LBa mo AC HMP) as (AL0 & moc & MR & MINV & HH & TW).
  assert (RSTK0 : rng RNG (CtrPre.TwinB.sp_lo E st) (sp0 - CtrPre.TwinB.sp_lo E st)).
  { apply (rng_sub _ _ _ _ _ (ACCT_rng _ _ _ _ _ _ AC)); lia. }
  assert (EV : evtF bsegs RNG
            (IFW.fwrite_i_post_post (AP.getr R 8) (AP.getr R 3) (AP.getr R 4) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24) (AP.getr R 25)
               (AP.getr R 26) (AP.getr R 27) (ms_fregs ms) (ms_fcsr ms) ravv s0v s1v s2v s3v s4v s5v resZ (CtrPre.TwinB.sp_lo E st) m)
            (MS (mkR (AP.getr R 1) (Z_to_bv 64 (bv_unsigned (AP.getr R 8) + -2128)) (AP.getr R 3) (AP.getr R 4) (AP.getr R 5) (AP.getr R 6) (AP.getr R 7) (AP.getr R 8)
                (AP.getr R 9) (Z_to_bv 64 resZ) (AP.getr R 11) (AP.getr R 12) (AP.getr R 13) (AP.getr R 14) (AP.getr R 15) (AP.getr R 16)
                (AP.getr R 17) (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (Z_to_bv 64 1) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24)
                (AP.getr R 25) (AP.getr R 26) (AP.getr R 27) (AP.getr R 28) (AP.getr R 29) (AP.getr R 30) (AP.getr R 31))
                (ms_fregs ms) (Z_to_bv 64 FWRITE_POST_SYM) (ms_fcsr ms) None m (seg_rom bsegs))).
  { unfold artcells in RT. decompose [and] RT. clear RT.
    eapply (IFW.fwrite_i_post RNG) with (size := sizeZ) (N := resZ * sizeZ) (RLO := RLO) (RHI := RHI).
    all: rewrite ?E8', ?EQ18.
    all: try lazymatch goal with
         | |- ALib.Mem.mem_inv _ _ => exact MI
         | |- stk _ _ _ _ => first [ replace (sp0 - 2128) with spm by (unfold sp0; lia); rewrite <- E2'; exact ST
                                   | replace (sp0 - 2128) with spm by (unfold sp0; lia); exact STM ]
         | |- ALib.Step.rw_cells _ _ _ _ => first [exact FRC | assumption]
         | |- Shadow.unpoisoned _ _ _ => exact UNP
         | |- Shadow.app_blk _ _ => exact APP
         | |- ALib.Mem.wr_at _ _ _ _ => exact WRH
         | |- rng_aimg _ => exact RIMG
         | |- rng _ (shad _) _ => exact RNGH
         | |- rng _ _ _ => exact RSTK0
         | |- _ = Z_to_bv 64 _ => exact EQ9
         | |- _ * _ = _ => reflexivity
         | |- _ <= _ /\ _ => exact HULL
         end.
    all: try (unfold Shadow.KHIGH, sp0 in *; lia).
    all: try (unfold Shadow.KHIGH, sp0 in *; nia).
    all: match goal with |- ?G => idtac "REMW" G end. }
  rewrite <- EQ2, <- EQ10, <- EQ21 in EV.
  assert (F1 : bv_unsigned (AP.getr R 2) = bv_unsigned (AP.getr R 8) - 2128) by (rewrite E2', E8'; unfold sp0; lia).
  assert (F2 : bv_unsigned (AP.getr R 8) <= 2 ^ 47) by (rewrite E8'; lia).
  assert (F3 : ALib.Step.rw_cells bsegs m (bv_unsigned (AP.getr R 8) - 56) [C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ravv]) by (rewrite E8'; exact FRC).
  rewrite Ems, HPC. apply (GlueA.TwinB.realizes_to_mkRA bsegs).
  eapply (implS_twfS_realizes_silent bsegs NMAXt (Ret (Exc.Ok tt)) RNG AL0
            (fun (_ : unit) (RNGq : footprint) ms' => RNGq = RNG /\ IFW.fwrite_i_post_post (AP.getr R 8) (AP.getr R 3) (AP.getr R 4) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24) (AP.getr R 25)
               (AP.getr R 26) (AP.getr R 27) (ms_fregs ms) (ms_fcsr ms) ravv s0v s1v s2v s3v s4v s5v resZ (CtrPre.TwinB.sp_lo E st) m ms')
            _ _ moc mo K).
  - cbn [implF epostF]. eapply evtF_mono; [exact EV|]. intros ms' PO. split; [reflexivity| exact PO].
  - exact TW.
  - exact HH.
  - exact MINV.
  - exact MR.
  - intros rr RNG' A' ms' moc' mo' HQ HP' ACC' HH' MINV' MR'.
    destruct (HP' mo' MR') as (HMP' & HMI' & OTH & ACP). destruct HQ as [-> HQ].
    exact (LEAF st K E ms mo r hargs wnl st1 ks o8 res v5 v4 v3 v2 v1 v0 rav L RNG sta LBa aw s5v s4v s3v s2v s1v s0v ravv HS HPB HK PRE G8 G10
             L0 L1 L2 L3 L4 L5 L6 WRAV RAVLT RAVEV CP FS CF AH MI BOT LO SPT F1 F2 F3 ms' mo' HQ HMP' HMI' OTH ACP).
Qed.
End Sound.
End TwinB.
