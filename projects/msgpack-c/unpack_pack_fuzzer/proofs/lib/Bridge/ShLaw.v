(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import AcctCore ExecF ITreeA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg AProto ABase AMalloc_iface AMalloc_iface2.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap State.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Seal Model Inv.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Ledger Actr Op.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 HeapOp St.
Open Scope Z_scope.
Unset Lia Cache.

Section ShLaw.
Context {rc : runConstT}.
Variable AI : AMallocIface2.
Variable IMGX : list iv.
Hypothesis IMGX_aci : imgx_ok AI IMGX.
Variable ACCT : word -> alayout -> footprint -> astate -> list ablock -> Model -> Prop.
Variable COVP : Model -> word -> Prop.
Variable NMAX : nat.
Hypothesis ACCT_led : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo ->
  exists A : word -> Prop, ainv (m_vm_lazy mo) A NMAX mo /\ (forall p, COVP mo p -> A p).
Hypothesis ACCT_cov : forall aw L RNG st LBa m mo b z, ACCT aw L RNG st LBa mo -> AHEAP AI L RNG st LBa m -> In b LBa ->
  (ab_addr b <= z < ab_addr b + ab_size b \/ shad (ab_addr b) <= z < shad (ab_addr b) + shlen (ab_size b + 7)) ->
  page_in_ranges (page_base_of z) (m_vm_lazy mo) = false \/ COVP mo (page_base_of z).
Hypothesis ACCT_cov_sh : forall aw L RNG st LBa mo z, ACCT aw L RNG st LBa mo -> sh_cov z ->
  page_in_ranges (page_base_of z) (m_vm_lazy mo) = false \/ COVP mo (page_base_of z).
Hypothesis ACCT_mat : forall aw L RNG st LBa mo mo', ACCT aw L RNG st LBa mo -> same_but_mat mo mo' ->
  List.NoDup (m_vm_materialized mo') ->
  (forall p, List.In p (m_vm_materialized mo') -> List.In p (m_vm_materialized mo) \/ COVP mo p) ->
  ACCT aw L RNG st LBa mo'.
Variable UNIV : list (list Z).
Hypothesis AI_frame_top : forall L RNG st LB m m',
  AHEAP AI L RNG st LB m -> (forall a, 0 <= a < 2^47 -> m' (ALib.Mem.wa a) = m (ALib.Mem.wa a)) -> Frame.wmono asegs m m' -> AHEAP AI L RNG st LB m'.
Hypothesis wmono_of : forall m m' : amem, (forall a, 0 <= a < two64 -> m (Z_to_bv 64 a) <> None -> m' (Z_to_bv 64 a) <> None) -> Frame.wmono asegs m m'.
Hypothesis AI_fake : AI_fake_law AI.
Variable Cw : client_world.
Notation OPSA := (asan_heap_optable AI IMGX IMGX_aci ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top wmono_of AI_fake Cw).
Notation AWAx := (AWA AI IMGX IMGX_aci ACCT UNIV AI_frame_top wmono_of AI_fake).

Definition CHSA (os : list oinst) (m : word -> option byte) (mo : Model) (z : Z) : Prop :=
  op_cov OPSA os z \/ Exists (fun o => semvA AI ACCT UNIV (fst o) (snd o) m mo z) os.

Lemma shadZ_shad : forall a, Seal.Seal.shadZ a = shad a.
Proof. intros a. unfold Seal.Seal.shadZ, Seal.Seal.SBz, shad, ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. lia. Qed.

Theorem asan_shlaw : forall os args md aw ws ca LB m mo cs c p,
  In (OPID, args) os -> decode args = Some (md, aw, ws, ca) ->
  aw_holds asegs IMGX AWAx aw LB ws m mo -> windows_wf ws LB (aw_ceiling asegs IMGX AWAx mo) ->
  Seal.Seal.seal_ok ws cs -> In c cs -> In (Inv.chunk_block c) LB ->
  (forall w, In w ws -> (w_kind w = K_BLOCK \/ K_GHOST <= w_kind w) -> forall a, in_iv (w_iv w) a -> ~ in_iv (Inv.chunk_block c) a) ->
  in_iv (Inv.chunk_block c) p ->
  m (Z_to_bv 64 (Seal.Seal.shadZ p)) = Some (Z_to_bv 8 0) /\ CHSA os m mo (Seal.Seal.shadZ p).
Proof.
  intros os args md aw ws ca LB m mo cs c p Hos D HA WF [SEAL S8] Hc HLB APART INP.
  cbn [aw_holds AWA] in HA. destruct HA as (W & HW & TI).
  pose proof TI as (T1 & T2 & T3 & _).
  set (v := Inv.chunk_block c) in *.
  assert (VSZ : snd v mod 8 = 0).
  { unfold v, Inv.chunk_block. cbn [snd]. specialize (S8 c Hc). unfold Model.CHUNK_HDR. clear - S8. Z.div_mod_to_equations. lia. }
  pose proof HW as (AH & HT & _).

  destruct (LB_cases AI ACCT UNIV W aw LB m mo v HW HLB) as [(b & Vb & Ev)|[(b & Hb & Ev)|(b & Vb & Ev)]].
  2:{ exfalso. pose proof (T1 b Hb) as WIN. apply (APART _ WIN ltac:(right; unfold K_GHOST, K_TWINz; cbn; lia) p); [| exact INP].
      unfold w_iv. cbn [w_lo w_len]. fold (twin_iv b). rewrite <- Ev. exact INP. }
  2:{ exfalso. destruct (T3 b Vb) as [_ WIN]. apply (APART _ WIN ltac:(right; unfold K_GHOST, K_FTWINz; cbn; lia) p); [| exact INP].
      unfold w_iv. cbn [w_lo w_len]. fold (fsh_iv b). rewrite <- Ev. exact INP. }
  destruct (kind_cases b) as [HH|HF].
  2:{ exfalso. destruct (T3 b (conj Vb HF)) as [WIN _].
      destruct (blk_facts AI AI_fake _ _ _ _ _ b AH (proj1 Vb)) as (NP & _).
      destruct (AI_fake _ _ _ _ _ b AH (proj1 Vb) HF) as (_ & _ & _ & _ & N64 & _).
      apply (APART _ WIN ltac:(right; unfold K_GHOST, K_FRAMEz; cbn; lia) (ab_addr b)).
      - unfold w_iv, in_iv. cbn [w_lo w_len fst snd]. lia.
      - rewrite Ev. unfold in_iv, user_iv. cbn [fst snd]. rewrite (usz_fake b HF). lia. }
  assert (NT : ~ In b (w_T W)).
  { intros HbT. pose proof (T1 b HbT) as WIN. apply (SEAL _ WIN eq_refl c Hc). cbn [w_lo]. rewrite shadZ_shad.
    replace (fst c) with (fst v) by reflexivity. rewrite Ev. reflexivity. }
  destruct (blk_facts AI AI_fake _ _ _ _ _ b AH (proj1 Vb)) as (NP & BK & HI & A8 & _).
  destruct (LB_user_facts AI ACCT UNIV AI_fake W aw LB m mo b HW Vb) as (_ & UB & ULO & _).
  assert (EV1 : fst v = ab_addr b /\ snd v = ab_size b) by (rewrite Ev; unfold user_iv; cbn [fst snd]; rewrite (usz_heap b HH); split; reflexivity).
  destruct EV1 as [EA ES]. unfold in_iv in INP. rewrite EA, ES in INP. rewrite ES in VSZ.
  set (g := (p - ab_addr b) / 8).
  assert (G : 0 <= g /\ 8 * g < ab_size b /\ 8 * g + 8 <= ab_size b /\ shad p = shad (ab_addr b) + g).
  { unfold g, shad. rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. clear - INP VSZ A8. Z.div_mod_to_equations. lia. }
  destruct G as (G0 & G1 & G2 & G3).
  split.
  - rewrite shadZ_shad, G3. pose proof (shadow_in_law_w AI ACCT UNIV AI_fake W aw LB m mo b g HW Vb HH NT G0 G1) as SH.
    rewrite (proj2 (Z.leb_le _ _) G2) in SH. exact SH.
  - right. apply Exists_exists. exists (OPID, args). split; [exact Hos|]. cbn [fst snd]. split; [reflexivity|].
    exists md, aw, ws, ca, LB. split; [exact D|]. split; [exists W; exact HW|].
    exists v. split; [exact HLB|]. right. split.
    + unfold user_band. rewrite EA. lia.
    + exists p. split; [unfold in_iv; rewrite EA, ES; exact INP| apply shadZ_shad].
Qed.

Theorem asan_shlaws : forall (os : list oinst) (m : word -> option byte) (mo : Model) (acc : list (word * nat)),
  op_minv OPSA mo -> Forall (fun o => op_holds OPSA (fst o) (snd o) m mo) os ->
  (forall a n j, In (a, n) acc -> 0 <= j < Z.of_nat n -> CHSA os m mo (bv_unsigned a + j)) ->
  exists mo', materialize_model_accesses mo acc = Some mo' /\ op_minv OPSA mo' /\
              Forall (fun o => op_holds OPSA (fst o) (snd o) m mo') os.
Proof.
  intros os m mo acc MI HO HC.
  exact (asan_heap_acc_user AI IMGX IMGX_aci ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top wmono_of AI_fake Cw os m mo acc MI HO HC).
Qed.
End ShLaw.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.AcctCore OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ITreeA.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import AProto.TwinB ABase.TwinB AMalloc_iface.TwinB AMalloc_iface2.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap.Op.
Import Ledger.TwinB Actr.TwinB Op.TwinB.

Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 HeapOp St.
Open Scope Z_scope.
Unset Lia Cache.

Section ShLaw.
Context {rc : runConstT}.
Variable AI : AMallocIface2.
Variable IMGX : list iv.
Hypothesis IMGX_aci : imgx_ok AI IMGX.
Variable ACCT : word -> alayout -> footprint -> astate -> list ablock -> Model -> Prop.
Variable COVP : Model -> word -> Prop.
Variable NMAX : nat.
Hypothesis ACCT_led : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo ->
  exists A : word -> Prop, ainv (m_vm_lazy mo) A NMAX mo /\ (forall p, COVP mo p -> A p).
Hypothesis ACCT_cov : forall aw L RNG st LBa m mo b z, ACCT aw L RNG st LBa mo -> AHEAP AI L RNG st LBa m -> In b LBa ->
  (ab_addr b <= z < ab_addr b + ab_size b \/ shad (ab_addr b) <= z < shad (ab_addr b) + shlen (ab_size b + 7)) ->
  page_in_ranges (page_base_of z) (m_vm_lazy mo) = false \/ COVP mo (page_base_of z).
Hypothesis ACCT_cov_sh : forall aw L RNG st LBa mo z, ACCT aw L RNG st LBa mo -> sh_cov z ->
  page_in_ranges (page_base_of z) (m_vm_lazy mo) = false \/ COVP mo (page_base_of z).
Hypothesis ACCT_mat : forall aw L RNG st LBa mo mo', ACCT aw L RNG st LBa mo -> same_but_mat mo mo' ->
  List.NoDup (m_vm_materialized mo') ->
  (forall p, List.In p (m_vm_materialized mo') -> List.In p (m_vm_materialized mo) \/ COVP mo p) ->
  ACCT aw L RNG st LBa mo'.
Variable UNIV : list (list Z).
Hypothesis AI_frame_top : forall L RNG st LB m m',
  AHEAP AI L RNG st LB m -> (forall a, 0 <= a < 2^47 -> m' (ALib.Mem.wa a) = m (ALib.Mem.wa a)) -> Frame.wmono bsegs m m' -> AHEAP AI L RNG st LB m'.
Hypothesis wmono_of : forall m m' : amem, (forall a, 0 <= a < two64 -> m (Z_to_bv 64 a) <> None -> m' (Z_to_bv 64 a) <> None) -> Frame.wmono bsegs m m'.
Hypothesis AI_fake : AI_fake_law AI.
Variable Cw : client_world.
Notation OPSA := (asan_heap_optable AI IMGX IMGX_aci ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top wmono_of AI_fake Cw).
Notation AWAx := (AWA AI IMGX IMGX_aci ACCT UNIV AI_frame_top wmono_of AI_fake).

Definition CHSA (os : list oinst) (m : word -> option byte) (mo : Model) (z : Z) : Prop :=
  op_cov OPSA os z \/ Exists (fun o => semvA AI ACCT UNIV (fst o) (snd o) m mo z) os.

Lemma shadZ_shad : forall a, Seal.Seal.shadZ a = shad a.
Proof. intros a. unfold Seal.Seal.shadZ, Seal.Seal.SBz, shad, ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. lia. Qed.

Theorem asan_shlaw : forall os args md aw ws ca LB m mo cs c p,
  In (OPID, args) os -> decode args = Some (md, aw, ws, ca) ->
  aw_holds bsegs IMGX AWAx aw LB ws m mo -> windows_wf ws LB (aw_ceiling bsegs IMGX AWAx mo) ->
  Seal.Seal.seal_ok ws cs -> In c cs -> In (Inv.chunk_block c) LB ->
  (forall w, In w ws -> (w_kind w = K_BLOCK \/ K_GHOST <= w_kind w) -> forall a, in_iv (w_iv w) a -> ~ in_iv (Inv.chunk_block c) a) ->
  in_iv (Inv.chunk_block c) p ->
  m (Z_to_bv 64 (Seal.Seal.shadZ p)) = Some (Z_to_bv 8 0) /\ CHSA os m mo (Seal.Seal.shadZ p).
Proof.
  intros os args md aw ws ca LB m mo cs c p Hos D HA WF [SEAL S8] Hc HLB APART INP.
  cbn [aw_holds AWA] in HA. destruct HA as (W & HW & TI).
  pose proof TI as (T1 & T2 & T3 & _).
  set (v := Inv.chunk_block c) in *.
  assert (VSZ : snd v mod 8 = 0).
  { unfold v, Inv.chunk_block. cbn [snd]. specialize (S8 c Hc). unfold Model.CHUNK_HDR. clear - S8. Z.div_mod_to_equations. lia. }
  pose proof HW as (AH & HT & _).

  destruct (LB_cases AI ACCT UNIV W aw LB m mo v HW HLB) as [(b & Vb & Ev)|[(b & Hb & Ev)|(b & Vb & Ev)]].
  2:{ exfalso. pose proof (T1 b Hb) as WIN. apply (APART _ WIN ltac:(right; unfold K_GHOST, K_TWINz; cbn; lia) p); [| exact INP].
      unfold w_iv. cbn [w_lo w_len]. fold (twin_iv b). rewrite <- Ev. exact INP. }
  2:{ exfalso. destruct (T3 b Vb) as [_ WIN]. apply (APART _ WIN ltac:(right; unfold K_GHOST, K_FTWINz; cbn; lia) p); [| exact INP].
      unfold w_iv. cbn [w_lo w_len]. fold (fsh_iv b). rewrite <- Ev. exact INP. }
  destruct (kind_cases b) as [HH|HF].
  2:{ exfalso. destruct (T3 b (conj Vb HF)) as [WIN _].
      destruct (blk_facts AI AI_fake _ _ _ _ _ b AH (proj1 Vb)) as (NP & _).
      destruct (AI_fake _ _ _ _ _ b AH (proj1 Vb) HF) as (_ & _ & _ & _ & N64 & _).
      apply (APART _ WIN ltac:(right; unfold K_GHOST, K_FRAMEz; cbn; lia) (ab_addr b)).
      - unfold w_iv, in_iv. cbn [w_lo w_len fst snd]. lia.
      - rewrite Ev. unfold in_iv, user_iv. cbn [fst snd]. rewrite (usz_fake b HF). lia. }
  assert (NT : ~ In b (w_T W)).
  { intros HbT. pose proof (T1 b HbT) as WIN. apply (SEAL _ WIN eq_refl c Hc). cbn [w_lo]. rewrite shadZ_shad.
    replace (fst c) with (fst v) by reflexivity. rewrite Ev. reflexivity. }
  destruct (blk_facts AI AI_fake _ _ _ _ _ b AH (proj1 Vb)) as (NP & BK & HI & A8 & _).
  destruct (LB_user_facts AI ACCT UNIV AI_fake W aw LB m mo b HW Vb) as (_ & UB & ULO & _).
  assert (EV1 : fst v = ab_addr b /\ snd v = ab_size b) by (rewrite Ev; unfold user_iv; cbn [fst snd]; rewrite (usz_heap b HH); split; reflexivity).
  destruct EV1 as [EA ES]. unfold in_iv in INP. rewrite EA, ES in INP. rewrite ES in VSZ.
  set (g := (p - ab_addr b) / 8).
  assert (G : 0 <= g /\ 8 * g < ab_size b /\ 8 * g + 8 <= ab_size b /\ shad p = shad (ab_addr b) + g).
  { unfold g, shad. rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. clear - INP VSZ A8. Z.div_mod_to_equations. lia. }
  destruct G as (G0 & G1 & G2 & G3).
  split.
  - rewrite shadZ_shad, G3. pose proof (shadow_in_law_w AI ACCT UNIV AI_fake W aw LB m mo b g HW Vb HH NT G0 G1) as SH.
    rewrite (proj2 (Z.leb_le _ _) G2) in SH. exact SH.
  - right. apply Exists_exists. exists (OPID, args). split; [exact Hos|]. cbn [fst snd]. split; [reflexivity|].
    exists md, aw, ws, ca, LB. split; [exact D|]. split; [exists W; exact HW|].
    exists v. split; [exact HLB|]. right. split.
    + unfold user_band. rewrite EA. lia.
    + exists p. split; [unfold in_iv; rewrite EA, ES; exact INP| apply shadZ_shad].
Qed.

Theorem asan_shlaws : forall (os : list oinst) (m : word -> option byte) (mo : Model) (acc : list (word * nat)),
  op_minv OPSA mo -> Forall (fun o => op_holds OPSA (fst o) (snd o) m mo) os ->
  (forall a n j, In (a, n) acc -> 0 <= j < Z.of_nat n -> CHSA os m mo (bv_unsigned a + j)) ->
  exists mo', materialize_model_accesses mo acc = Some mo' /\ op_minv OPSA mo' /\
              Forall (fun o => op_holds OPSA (fst o) (snd o) m mo') os.
Proof.
  intros os m mo acc MI HO HC.
  exact (asan_heap_acc_user AI IMGX IMGX_aci ACCT COVP NMAX ACCT_led ACCT_cov ACCT_cov_sh ACCT_mat UNIV AI_frame_top wmono_of AI_fake Cw os m mo acc MI HO HC).
Qed.
End ShLaw.
End TwinB.
