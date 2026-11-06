(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PrimInt63 Uint63.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Cells Frame ITree Nodes.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib Require ALib.Mem.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import AcctCore ExecF ITreeA NodesA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg AProto ABase AMalloc_iface AMalloc_iface2.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Instr State Step Plan PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import Mem.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib DefsA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Ledger Op Adeq.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St Step Plan PlanS CtrLib HeapOp.
Open Scope Z_scope.
Unset Lia Cache.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Actr.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64Proofs ValProofs MemProofs StepSoundBase.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require Import CtrFX.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require HeapCtr HeapCtrB.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require CallA CallV CtrPre GlueA.
Unset Nia Cache. Unset Nra Cache.
Import ValP MemP CtrFX.
Import ActrA.
Module AP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec.

Section Pat.
Context {rc : runConstT}.
Variable AI : AMallocIface2.
Variable IMGX : list iv.
Hypothesis IMGX_aci : imgx_ok AI IMGX.
Variable ACCT : word -> alayout -> footprint -> astate -> list ablock -> Model -> Prop.
Variable UNIV : list (list Z).
Variable Cw : client_world.
Variable OPS : optable.
Hypothesis AI_fake : AI_fake_law AI.

Lemma KT9 : w2Z K_TWIN = 9. Proof. reflexivity. Qed.
Lemma KB1 : w2Z CtrLib.K_BLOCK = 1. Proof. reflexivity. Qed.

Lemma twin_shape_ok_inv : forall st sh n, twin_shape_ok st sh n = true ->
  exists r, IMap.find sh (s_regs st) = Some r
    /\ ((is_twin_region r n = true /\ size_shape_ok (s_facts st) n = true)
        \/ (is_twin_main r n = true /\ exists s2, tail_scan (s_facts st) (s_regs st) sh n = Some s2)).
Proof.
  intros st sh n H. unfold twin_shape_ok in H. destruct (IMap.find sh (s_regs st)) as [r|]; [|discriminate H]. exists r. split; [reflexivity|].
  apply orb_prop in H as [H|H]; apply andb_prop in H as [H1 H2]; [left; auto| right]. split; [exact H1|].
  destruct (tail_scan (s_facts st) (s_regs st) sh n) as [s2|]; [exists s2; reflexivity| discriminate H2].
Qed.
Lemma twin_pat_ok_t_inv : forall st wl kb n, twin_pat_ok_t st wl kb n = true ->
  exists sh lent, twin_of (s_facts st) kb = Some sh /\ CtrA.win_lookup wl sh = Some (lent, K_TWIN) /\ lent = twin_len n
    /\ PrimInt63.eqb sh 0%uint63 = false /\ twin_shape_ok st sh n = true.
Proof.
  intros st wl kb n H. unfold twin_pat_ok_t in H. destruct (twin_of (s_facts st) kb) as [sh|] eqn:TW; [|discriminate H].
  destruct (CtrA.win_lookup wl sh) as [[lent kd]|] eqn:WL; [|discriminate H].
  apply andb_prop in H as [H SHP]. apply andb_prop in H as [H NZ]. apply andb_prop in H as [KD LEN].
  apply weqb_eq in KD. subst kd. apply sv_eqb_eq in LEN. apply negb_true_iff in NZ. exists sh, lent. split; [reflexivity|]. split; [exact WL|]. split; [exact LEN|]. split; [exact NZ| exact SHP].
Qed.

Theorem twin_pat_sound_t : forall E st ms mo r hargs wnl L RNG sta LBa aw kb n p,
  st_ok asegs OPS E st ms mo ->
  CtrPre.acallG AI ACCT UNIV Cw E st ms mo r hargs wnl L RNG sta LBa aw ->
  twin_pat_ok_t st wnl kb n = true ->
  In (HB p (bv_unsigned (ev E kb)) (bv_unsigned (den E n))) LBa ->
  ablock_shadow (ms_mem ms) (bv_unsigned (ev E kb)) (bv_unsigned (den E n)).
Proof.
  intros E st ms mo r hargs wnl L RNG sta LBa aw kb n p HS CF OK HP.
  destruct CF as (LB & ks & offs & rss & ksp & nn & md & A & nw & rest & SPR & Hksp & SPE & K16 & LOSP & FLOOR & Hf & Hc & Eh & Tnw & Nn & Ln & N255
                  & NW & AN & AJ & TS & WF & HC & AWden & (W & WOF & AR & TI)).
  destruct (twin_pat_ok_t_inv st wnl kb n OK) as (sh & lent & TW & WLt & LEN & SHNZ & SHP).
  destruct (twin_shape_ok_inv st sh n SHP) as (rs & Frs & SHAPE).
  pose proof (so_facts _ _ _ _ _ _ HS) as HF.
  set (Ab := bv_unsigned (ev E kb)) in *. set (N := bv_unsigned (den E n)) in *.

  pose proof AR as [HWw EMw]. pose proof HWw as (AH & _). destruct WOF as (E1 & E2 & E3 & E4). rewrite E4 in AH.
  destruct (heap_block_facts AI _ _ _ _ _ (HB p Ab N) AH HP ltac:(exists p; reflexivity)) as (NN & (BK & _ & HI & _) & _). cbn [ab_addr ab_size] in NN, BK, HI.
  unfold ablk, AIMG_HI, KLS in BK. pose proof atop_range as ATR. unfold AREQMAX in NN.

  assert (ESH : bv_unsigned (ev E sh) = shad Ab).
  { rewrite (CallV.twin_of_sound E _ kb sh HF TW). fold Ab. unfold shad, ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
    rewrite Z.mod_small; [lia|]. clear - BK HI ATR NN. Z.div_mod_to_equations. lia. }
  assert (ELT : bv_unsigned (den E lent) = shlen (N + 7)).
  { rewrite LEN, (CallA.twin_len_den E n) by (fold N; lia). fold N. unfold shlen. rewrite Z.shiftr_div_pow2 by lia. reflexivity. }
  intros g G0 G1.

  assert (P1 : rb asegs (ms_mem ms) (shad Ab + g) = Some (Z_to_bv 8 (if 8 * g + 8 <=? N then 0 else N - 8 * g))).
  { destruct SHAPE as [[TR SS]|[TM [s2 TSC]]].
    - pose proof (so_reg _ _ _ _ _ _ HS sh rs Frs) as RO.
      pose proof (CallA.size_shape_sound E _ n HF SS) as SH8.
      pose proof (CallA.is_twin_region_sound asegs (s_priv st) E (ms_mem ms) sh rs n RO SHNZ TR) as PATR. fold N in PATR. rewrite ESH in PATR.
      apply PATR; [lia| | exact G0| exact G1]. exact SH8.
    - pose proof (CallA.twin_pair_sound asegs (s_priv st) E (ms_mem ms) (s_facts st) (s_regs st) sh rs n s2 HF (so_reg _ _ _ _ _ _ HS) Frs SHNZ TM TSC) as PATP.
      fold N in PATP. rewrite ESH in PATP. apply PATP; [clear - NN; lia| | exact G0| exact G1].
      unfold shad, ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. clear - BK HI ATR NN. Z.div_mod_to_equations. lia. }

  destruct (HeapCtrB.nonstack_windows_In E nn rest wnl sh lent K_TWIN NW (HeapCtrB.win_lookup_In _ _ _ _ WLt)) as (_ & _ & _ & INW).
  rewrite ESH, ELT, KT9 in INW.
  destruct TI as (_ & T2 & _). destruct (T2 _ INW eq_refl) as (b & HbT & EIV). unfold w_iv in EIV. cbn [w_lo w_len] in EIV.
  pose proof HWw as (_ & _ & _ & _ & _ & _ & _ & MAP & _).
  assert (MP : ms_mem ms (ALib.Mem.wa (shad Ab + g)) <> None).
  { apply MAP. apply in_ivs_In. exists (twin_iv b). split; [apply in_map; exact HbT|]. rewrite <- EIV.
    unfold in_iv. cbn [fst snd]. unfold shlen. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. clear - G0 G1. Z.div_mod_to_equations. lia. }
  unfold rb in P1. unfold ALib.Mem.wa in *. destruct (ms_mem ms (Z_to_bv 64 (shad Ab + g))) as [y|]; [exact P1| contradiction].
Qed.

Theorem twin_pat_sound : forall E st ms mo r hargs wnl L RNG sta LBa aw kb,
  st_ok asegs OPS E st ms mo ->
  CtrPre.acallG AI ACCT UNIV Cw E st ms mo r hargs wnl L RNG sta LBa aw ->
  twin_pat_ok st wnl kb = true ->
  exists p n, CtrA.win_lookup wnl kb = Some (n, CtrLib.K_BLOCK)
    /\ In (HB p (bv_unsigned (ev E kb)) (bv_unsigned (den E n))) LBa
    /\ ablock_shadow (ms_mem ms) (bv_unsigned (ev E kb)) (bv_unsigned (den E n)).
Proof.
  intros E st ms mo r hargs wnl L RNG sta LBa aw kb HS CF OK.
  unfold twin_pat_ok in OK. destruct (CtrA.win_lookup wnl kb) as [[n kd]|] eqn:WLb; [|discriminate OK].
  apply andb_prop in OK as [KD OKT]. apply weqb_eq in KD. subst kd.
  pose proof CF as CF0.
  destruct CF as (LB & ks & offs & rss & ksp & nn & md & A & nw & rest & SPR & Hksp & SPE & K16 & LOSP & FLOOR & Hf & Hc & Eh & Tnw & Nn & Ln & N255
                  & NW & AN & AJ & TS & WF & HC & AWden & (W & WOF & AR & TI)).
  destruct (twin_pat_ok_t_inv st wnl kb n OKT) as (sh & lent & TW & WLt & LEN & SHNZ & SHP).
  pose proof (so_facts _ _ _ _ _ _ HS) as HF.
  set (Ab := bv_unsigned (ev E kb)) in *. set (N := bv_unsigned (den E n)) in *.

  destruct (HeapCtrB.nonstack_windows_In E nn rest wnl kb n CtrLib.K_BLOCK NW (HeapCtrB.win_lookup_In _ _ _ _ WLb)) as (_ & _ & _ & INb).
  pose proof (proj1 (Forall_forall _ _) WF _ INb) as (W1 & W2 & W3 & KDs). cbn [w_kind w_lo w_len w_iv] in KDs, W1, W2, W3. rewrite KB1 in KDs.
  assert (HBL : In (Ab, N) LB).
  { destruct KDs as [[K _]|[[_ B]|[K _]]]; [unfold K_STACK in K; lia| exact B| unfold K_SUB in K; lia]. }
  pose proof AR as [HWw EMw]. pose proof (aw_real_holds AI ACCT UNIV _ _ _ _ _ AR) as AWH.
  destruct (aw_blocks_ok_asan AI IMGX IMGX_aci ACCT UNIV AI_fake aw LB (ms_mem ms) mo (Ab, N) AWH HBL) as (B1 & B2 & B3 & _). cbn [fst snd] in B1, B2, B3.
  unfold aw_ceiling_asan in B3. pose proof atop_range as ATR.
  assert (ESH : bv_unsigned (ev E sh) = shad Ab).
  { rewrite (CallV.twin_of_sound E _ kb sh HF TW). fold Ab. unfold shad, ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
    rewrite Z.mod_small; [lia|]. clear - B1 B2 B3 ATR. Z.div_mod_to_equations. lia. }
  assert (ELT : bv_unsigned (den E lent) = shlen (N + 7)).
  { rewrite LEN, (CallA.twin_len_den E n) by (fold N; lia). fold N. unfold shlen. rewrite Z.shiftr_div_pow2 by lia. reflexivity. }

  destruct (HeapCtrB.nonstack_windows_In E nn rest wnl sh lent K_TWIN NW (HeapCtrB.win_lookup_In _ _ _ _ WLt)) as (_ & _ & _ & INW).
  rewrite ESH, ELT, KT9 in INW.
  pose proof TI as (_ & T2 & _). destruct (T2 _ INW eq_refl) as (b & HbT & EIV). unfold w_iv, twin_iv in EIV. cbn [w_lo w_len] in EIV. injection EIV as ESA ESL.
  destruct (twin_owner_w AI ACCT UNIV AI_fake W aw LB (ms_mem ms) mo b Ab N HWw HbT HBL ESA) as (EA & EN & NR).
  destruct (twin_T_facts AI ACCT UNIV W aw LB (ms_mem ms) mo b HWw HbT) as (HbL & _ & _ & _ & (p & EB) & _).
  pose proof WOF as (_ & _ & _ & E4).
  assert (HP : In (HB p Ab N) LBa) by (rewrite EA, EN, <- EB, <- E4; exact HbL).
  exists p, n. split; [reflexivity|]. split; [exact HP|].
  exact (twin_pat_sound_t E st ms mo r hargs wnl L RNG sta LBa aw kb n p HS CF0 OKT HP).
Qed.

Theorem aw_pat_in : forall W aw LB m mo b,
  aw_holds_w AI ACCT UNIV W aw LB m mo -> vis W b -> is_heap b -> ~ In b (w_T W) ->
  ablock_shadow m (ab_addr b) (ab_size b).
Proof.
  intros W aw LB m mo b HW Vb HH NT g G0 G1. eapply shadow_in_law_w; eassumption.
Qed.

End Pat.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.AcctCore OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ITreeA OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.NodesA.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import AProto.TwinB ABase.TwinB AMalloc_iface.TwinB AMalloc_iface2.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Plan OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.PlanSound.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap.Op.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Lib OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.DefsA.
Import Ledger.TwinB Op.TwinB Adeq.TwinB.

Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St Step Plan PlanS CtrLib HeapOp.
Open Scope Z_scope.
Unset Lia Cache.

Import Actr.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64Proofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.ValProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.MemProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.StepSoundBase.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.CtrFX.

Unset Nia Cache. Unset Nra Cache.
Import ValP MemP CtrFX.
Import ActrA.
Module AP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec.

Section Pat.
Context {rc : runConstT}.
Variable AI : AMallocIface2.
Variable IMGX : list iv.
Hypothesis IMGX_aci : imgx_ok AI IMGX.
Variable ACCT : word -> alayout -> footprint -> astate -> list ablock -> Model -> Prop.
Variable UNIV : list (list Z).
Variable Cw : client_world.
Variable OPS : optable.
Hypothesis AI_fake : AI_fake_law AI.

Lemma KT9 : w2Z K_TWIN = 9. Proof. reflexivity. Qed.
Lemma KB1 : w2Z CtrLib.K_BLOCK = 1. Proof. reflexivity. Qed.

Lemma twin_shape_ok_inv : forall st sh n, twin_shape_ok st sh n = true ->
  exists r, IMap.find sh (s_regs st) = Some r
    /\ ((is_twin_region r n = true /\ size_shape_ok (s_facts st) n = true)
        \/ (is_twin_main r n = true /\ exists s2, tail_scan (s_facts st) (s_regs st) sh n = Some s2)).
Proof.
  intros st sh n H. unfold twin_shape_ok in H. destruct (IMap.find sh (s_regs st)) as [r|]; [|discriminate H]. exists r. split; [reflexivity|].
  apply orb_prop in H as [H|H]; apply andb_prop in H as [H1 H2]; [left; auto| right]. split; [exact H1|].
  destruct (tail_scan (s_facts st) (s_regs st) sh n) as [s2|]; [exists s2; reflexivity| discriminate H2].
Qed.
Lemma twin_pat_ok_t_inv : forall st wl kb n, twin_pat_ok_t st wl kb n = true ->
  exists sh lent, twin_of (s_facts st) kb = Some sh /\ CtrA.win_lookup wl sh = Some (lent, K_TWIN) /\ lent = twin_len n
    /\ PrimInt63.eqb sh 0%uint63 = false /\ twin_shape_ok st sh n = true.
Proof.
  intros st wl kb n H. unfold twin_pat_ok_t in H. destruct (twin_of (s_facts st) kb) as [sh|] eqn:TW; [|discriminate H].
  destruct (CtrA.win_lookup wl sh) as [[lent kd]|] eqn:WL; [|discriminate H].
  apply andb_prop in H as [H SHP]. apply andb_prop in H as [H NZ]. apply andb_prop in H as [KD LEN].
  apply weqb_eq in KD. subst kd. apply sv_eqb_eq in LEN. apply negb_true_iff in NZ. exists sh, lent. split; [reflexivity|]. split; [exact WL|]. split; [exact LEN|]. split; [exact NZ| exact SHP].
Qed.

Theorem twin_pat_sound_t : forall E st ms mo r hargs wnl L RNG sta LBa aw kb n p,
  st_ok bsegs OPS E st ms mo ->
  CtrPre.TwinB.acallG AI ACCT UNIV Cw E st ms mo r hargs wnl L RNG sta LBa aw ->
  twin_pat_ok_t st wnl kb n = true ->
  In (HB p (bv_unsigned (ev E kb)) (bv_unsigned (den E n))) LBa ->
  ablock_shadow (ms_mem ms) (bv_unsigned (ev E kb)) (bv_unsigned (den E n)).
Proof.
  intros E st ms mo r hargs wnl L RNG sta LBa aw kb n p HS CF OK HP.
  destruct CF as (LB & ks & offs & rss & ksp & nn & md & A & nw & rest & SPR & Hksp & SPE & K16 & LOSP & FLOOR & Hf & Hc & Eh & Tnw & Nn & Ln & N255
                  & NW & AN & AJ & TS & WF & HC & AWden & (W & WOF & AR & TI)).
  destruct (twin_pat_ok_t_inv st wnl kb n OK) as (sh & lent & TW & WLt & LEN & SHNZ & SHP).
  destruct (twin_shape_ok_inv st sh n SHP) as (rs & Frs & SHAPE).
  pose proof (so_facts _ _ _ _ _ _ HS) as HF.
  set (Ab := bv_unsigned (ev E kb)) in *. set (N := bv_unsigned (den E n)) in *.

  pose proof AR as [HWw EMw]. pose proof HWw as (AH & _). destruct WOF as (E1 & E2 & E3 & E4). rewrite E4 in AH.
  destruct (heap_block_facts AI _ _ _ _ _ (HB p Ab N) AH HP ltac:(exists p; reflexivity)) as (NN & (BK & _ & HI & _) & _). cbn [ab_addr ab_size] in NN, BK, HI.
  unfold ablk, AIMG_HI, KLS in BK. pose proof atop_range as ATR. unfold AREQMAX in NN.

  assert (ESH : bv_unsigned (ev E sh) = shad Ab).
  { rewrite (CallV.TwinB.twin_of_sound E _ kb sh HF TW). fold Ab. unfold shad, ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
    rewrite Z.mod_small; [lia|]. clear - BK HI ATR NN. Z.div_mod_to_equations. lia. }
  assert (ELT : bv_unsigned (den E lent) = shlen (N + 7)).
  { rewrite LEN, (CallA.TwinB.twin_len_den E n) by (fold N; lia). fold N. unfold shlen. rewrite Z.shiftr_div_pow2 by lia. reflexivity. }
  intros g G0 G1.

  assert (P1 : rb bsegs (ms_mem ms) (shad Ab + g) = Some (Z_to_bv 8 (if 8 * g + 8 <=? N then 0 else N - 8 * g))).
  { destruct SHAPE as [[TR SS]|[TM [s2 TSC]]].
    - pose proof (so_reg _ _ _ _ _ _ HS sh rs Frs) as RO.
      pose proof (CallA.TwinB.size_shape_sound E _ n HF SS) as SH8.
      pose proof (CallA.TwinB.is_twin_region_sound bsegs (s_priv st) E (ms_mem ms) sh rs n RO SHNZ TR) as PATR. fold N in PATR. rewrite ESH in PATR.
      apply PATR; [lia| | exact G0| exact G1]. exact SH8.
    - pose proof (CallA.TwinB.twin_pair_sound bsegs (s_priv st) E (ms_mem ms) (s_facts st) (s_regs st) sh rs n s2 HF (so_reg _ _ _ _ _ _ HS) Frs SHNZ TM TSC) as PATP.
      fold N in PATP. rewrite ESH in PATP. apply PATP; [clear - NN; lia| | exact G0| exact G1].
      unfold shad, ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. clear - BK HI ATR NN. Z.div_mod_to_equations. lia. }

  destruct (HeapCtrB.TwinB.nonstack_windows_In E nn rest wnl sh lent K_TWIN NW (HeapCtrB.TwinB.win_lookup_In _ _ _ _ WLt)) as (_ & _ & _ & INW).
  rewrite ESH, ELT, KT9 in INW.
  destruct TI as (_ & T2 & _). destruct (T2 _ INW eq_refl) as (b & HbT & EIV). unfold w_iv in EIV. cbn [w_lo w_len] in EIV.
  pose proof HWw as (_ & _ & _ & _ & _ & _ & _ & MAP & _).
  assert (MP : ms_mem ms (ALib.Mem.wa (shad Ab + g)) <> None).
  { apply MAP. apply in_ivs_In. exists (twin_iv b). split; [apply in_map; exact HbT|]. rewrite <- EIV.
    unfold in_iv. cbn [fst snd]. unfold shlen. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. clear - G0 G1. Z.div_mod_to_equations. lia. }
  unfold rb in P1. unfold ALib.Mem.wa in *. destruct (ms_mem ms (Z_to_bv 64 (shad Ab + g))) as [y|]; [exact P1| contradiction].
Qed.

Theorem twin_pat_sound : forall E st ms mo r hargs wnl L RNG sta LBa aw kb,
  st_ok bsegs OPS E st ms mo ->
  CtrPre.TwinB.acallG AI ACCT UNIV Cw E st ms mo r hargs wnl L RNG sta LBa aw ->
  twin_pat_ok st wnl kb = true ->
  exists p n, CtrA.win_lookup wnl kb = Some (n, CtrLib.K_BLOCK)
    /\ In (HB p (bv_unsigned (ev E kb)) (bv_unsigned (den E n))) LBa
    /\ ablock_shadow (ms_mem ms) (bv_unsigned (ev E kb)) (bv_unsigned (den E n)).
Proof.
  intros E st ms mo r hargs wnl L RNG sta LBa aw kb HS CF OK.
  unfold twin_pat_ok in OK. destruct (CtrA.win_lookup wnl kb) as [[n kd]|] eqn:WLb; [|discriminate OK].
  apply andb_prop in OK as [KD OKT]. apply weqb_eq in KD. subst kd.
  pose proof CF as CF0.
  destruct CF as (LB & ks & offs & rss & ksp & nn & md & A & nw & rest & SPR & Hksp & SPE & K16 & LOSP & FLOOR & Hf & Hc & Eh & Tnw & Nn & Ln & N255
                  & NW & AN & AJ & TS & WF & HC & AWden & (W & WOF & AR & TI)).
  destruct (twin_pat_ok_t_inv st wnl kb n OKT) as (sh & lent & TW & WLt & LEN & SHNZ & SHP).
  pose proof (so_facts _ _ _ _ _ _ HS) as HF.
  set (Ab := bv_unsigned (ev E kb)) in *. set (N := bv_unsigned (den E n)) in *.

  destruct (HeapCtrB.TwinB.nonstack_windows_In E nn rest wnl kb n CtrLib.K_BLOCK NW (HeapCtrB.TwinB.win_lookup_In _ _ _ _ WLb)) as (_ & _ & _ & INb).
  pose proof (proj1 (Forall_forall _ _) WF _ INb) as (W1 & W2 & W3 & KDs). cbn [w_kind w_lo w_len w_iv] in KDs, W1, W2, W3. rewrite KB1 in KDs.
  assert (HBL : In (Ab, N) LB).
  { destruct KDs as [[K _]|[[_ B]|[K _]]]; [unfold K_STACK in K; lia| exact B| unfold K_SUB in K; lia]. }
  pose proof AR as [HWw EMw]. pose proof (aw_real_holds AI ACCT UNIV _ _ _ _ _ AR) as AWH.
  destruct (aw_blocks_ok_asan AI IMGX IMGX_aci ACCT UNIV AI_fake aw LB (ms_mem ms) mo (Ab, N) AWH HBL) as (B1 & B2 & B3 & _). cbn [fst snd] in B1, B2, B3.
  unfold aw_ceiling_asan in B3. pose proof atop_range as ATR.
  assert (ESH : bv_unsigned (ev E sh) = shad Ab).
  { rewrite (CallV.TwinB.twin_of_sound E _ kb sh HF TW). fold Ab. unfold shad, ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
    rewrite Z.mod_small; [lia|]. clear - B1 B2 B3 ATR. Z.div_mod_to_equations. lia. }
  assert (ELT : bv_unsigned (den E lent) = shlen (N + 7)).
  { rewrite LEN, (CallA.TwinB.twin_len_den E n) by (fold N; lia). fold N. unfold shlen. rewrite Z.shiftr_div_pow2 by lia. reflexivity. }

  destruct (HeapCtrB.TwinB.nonstack_windows_In E nn rest wnl sh lent K_TWIN NW (HeapCtrB.TwinB.win_lookup_In _ _ _ _ WLt)) as (_ & _ & _ & INW).
  rewrite ESH, ELT, KT9 in INW.
  pose proof TI as (_ & T2 & _). destruct (T2 _ INW eq_refl) as (b & HbT & EIV). unfold w_iv, twin_iv in EIV. cbn [w_lo w_len] in EIV. injection EIV as ESA ESL.
  destruct (twin_owner_w AI ACCT UNIV AI_fake W aw LB (ms_mem ms) mo b Ab N HWw HbT HBL ESA) as (EA & EN & NR).
  destruct (twin_T_facts AI ACCT UNIV W aw LB (ms_mem ms) mo b HWw HbT) as (HbL & _ & _ & _ & (p & EB) & _).
  pose proof WOF as (_ & _ & _ & E4).
  assert (HP : In (HB p Ab N) LBa) by (rewrite EA, EN, <- EB, <- E4; exact HbL).
  exists p, n. split; [reflexivity|]. split; [exact HP|].
  exact (twin_pat_sound_t E st ms mo r hargs wnl L RNG sta LBa aw kb n p HS CF0 OKT HP).
Qed.

Theorem aw_pat_in : forall W aw LB m mo b,
  aw_holds_w AI ACCT UNIV W aw LB m mo -> vis W b -> is_heap b -> ~ In b (w_T W) ->
  ablock_shadow m (ab_addr b) (ab_size b).
Proof.
  intros W aw LB m mo b HW Vb HH NT g G0 G1. eapply shadow_in_law_w; eassumption.
Qed.

End Pat.
End TwinB.
