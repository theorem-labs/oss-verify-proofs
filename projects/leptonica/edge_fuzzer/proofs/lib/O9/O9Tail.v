(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require StackLayout.
From LinuxProcessSemantics.LinuxProcessSem Require Fs.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Monad.
From LinuxProcessSemantics.LinuxProcessSem Require Specs.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.leptonica.edge_fuzzer.images Require Plain.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common Require PropExec.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common Require CatExec.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common Require CatSim.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common Require StepTac.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common Require Hoare.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common Require ShapeAlg.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common Require AllocIface.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common Require PureModel.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common Require VmLedger.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common Require StoreOk.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common Require MemSplit.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common Require RefMemcpyLib.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common Require StartupTac.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common Require WalkTac.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common Require FPSteps.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng Require AllocBase.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng Require AllocCalloc.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng Require AllocSure.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica Require SumWalkTac.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica Require SumSpecs.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica Require WalksLib.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica Require W2Lib.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica Require LibAtomic.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica Require LeptDefs.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica Require LeptStructs.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica Require LeptArith.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica Require LeptArith2.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica Require LeptNuma.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica Require LeptRoom.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica Require LeptRoom9.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.O9 Require O9Drv1.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.O9 Require O9LeptStderr.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.O9 Require O9LeptBase.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.O9 Require O9CL7a.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.O9 Require O9CL8a.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.O9 Require O9LeptCmapValid.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.O9 Require O9CL9a.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.O9 Require O9LeptDeser.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.O9 Require O9LeptCmap2.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.O9 Require O9LeptPixCopy.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.O9 Require O9LeptEdge_iface.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.O9 Require O9LeptEdgeSegs.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.O9 Require O9LeptEdgeSegs2.
Module O9LeptFuzz.
Import Stdlib.ZArith.ZArith.
Import Stdlib.NArith.NArith.
Import Stdlib.Lists.List.
Import Stdlib.micromega.Lia.
Import Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.LinuxProcessSem.StackLayout.
Import LinuxProcessSemantics.LinuxProcessSem.Fs.
Import LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.LinuxProcessSem.Monad.
Import LinuxProcessSemantics.LinuxProcessSem.Specs.
Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import LinuxProcessSemantics.Riscv.Instr.
Import LinuxProcessSemantics.Riscv.Decode.
Import LinuxProcessSemantics.Riscv.DecodeC.
Import LinuxProcessSemantics.Riscv.Sem.
Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.leptonica.edge_fuzzer.images.Plain.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.CatExec.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.CatSim.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.StepTac.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.AllocIface.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.PureModel.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.VmLedger.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.StoreOk.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.MemSplit.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.RefMemcpyLib.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.StartupTac.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.WalkTac.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.FPSteps.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng.AllocBase.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng.AllocSure.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica.SumWalkTac.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica.SumSpecs.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica.WalksLib.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica.W2Lib.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica.LibAtomic.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica.LeptDefs.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica.LeptStructs.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica.LeptArith.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica.LeptArith2.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica.LeptNuma.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica.LeptRoom.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica.LeptRoom9.
Import O9Drv1.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.O9.O9LeptStderr.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.O9.O9LeptBase.
Import O9CL7a.
Import O9CL8a.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.O9.O9LeptCmapValid.
Import O9CL9a.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.O9.O9LeptDeser.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.O9.O9LeptCmap2.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.O9.O9LeptPixCopy.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.O9.O9LeptEdge_iface.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.O9.O9LeptEdgeSegs.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.O9.O9LeptEdgeSegs2.
(* [comment removed for export] *)








Import O9Drv1.O9FuzzIface.


Import O9CL7a.O9LeptErr.

Import O9CL8a.O9LeptPixHdr.


Import O9CL9a.O9LeptPixDestroy.

Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac nin_cs Hx := let H := fresh in pose proof Hx as H; unfold cs_rest in H; cbn in H; repeat (destruct H as [<-|H]; [notin_list|]); destruct H.

Section Final.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LL16} {P16 : O9Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
Lemma fuzz_covers : (RK_edge <= FUZZ_CALLS)%Z /\ (forall size h, (1 <= h <= 20000)%Z -> (RB_edge h <= fuzz_margin size)%Z).
Proof. split; [rewrite RK_edge_val; unfold FUZZ_CALLS; lia | intros size h Hh; unfold fuzz_margin; exact (proj2 (RB_edge_le h Hh))]. Qed.

Theorem lept_fuzz_call : pixMeasureEdgeSmoothness_contract -> @fuzz_call_contract AL CL ASR.
Proof.
  intros HPM. unfold pixMeasureEdgeSmoothness_contract in HPM. unfold fuzz_call_contract.
  intros fx A m md regs dptr size pl ret sp0 argv envp S Hz Hinv Hpure Henv Ha0 Ha1 Hsz Hsz26 Hlive Hpl Hempty Hal16 Hra Hret H3 H4 Hsp16 Htop Hsp0 Hsp0hi Hisw Hwin Hsev Hpmm Hhdl Hgot kR bR Hrm Hrk Hrb K.
  pose proof fuzz_calls_nonneg as FZc. pose proof fuzz_covers as [FZk FZb].
  pose proof (fuzz_margin_bound size ltac:(lia)) as FZm.
  assert (FZd : (RK_deser + RK_pmes <= FUZZ_CALLS)%Z) by exact FZk.
  rewrite p16_segs in Hhdl, K |- *. rewrite p16_tp in H4.
  unfold LEPT_STACK, A_LEPT_SEV, A_LEPT_PMM, A_LEPT_HANDLER, A_GOT_LO, A_GOT_HI, PC_FUZZ in *.
  pose proof (alloc_top_win_vals _ Hisw) as ATW. unfold sp_window_hi in Hsp0hi.
  replace (Z_to_bv 64 0x5cd50) with (0x5cd50 : word) by (apply bv_eq; reflexivity).
  pose proof (u64_range (getr regs 2)) as Hs. pose proof (u64_range dptr) as Hdp. pose proof (u64_range sp0) as Hsp0r.
  set (s := u (getr regs 2)) in *.
  assert (H2 : getr regs 2 = Z_to_bv 64 s) by (subst s; rewrite zbv_self; reflexivity). clearbody s.
  set (dp := u dptr) in *.
  assert (Edp : dptr = Z_to_bv 64 dp) by (subst dp; rewrite zbv_self; reflexivity). clearbody dp. rewrite Edp in Ha0, Hlive, Hempty.
  set (C := LCTX sp0 argv envp s (m_vmmaps md) m A).
  assert (Etop : c_top C = s) by reflexivity. assert (Evm : c_vm C = m_vmmaps md) by reflexivity.
  assert (CK : Cok C) by (constructor; cbn; rewrite ?LSTK_val; lia).
  pose proof LSTK_val as LV.
  (* [comment removed for export] *)
  assert (SOK : store_ok SEGS m (Z_to_bv 64 (s - 48)) 48 = true).
  { rewrite <- p16_segs. apply store_ok_of_all; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx.
    destruct (Hwin x ltac:(lia)) as (D & _). unfold wview. destruct (m x) eqn:E; [discriminate | exfalso; exact (D eq_refl)]. }
  assert (OUT3 : forall a : word, ~ (s - 24 <= u a < s)%Z -> FR3 m s ret regs a = m a).
  { intros a Ha. unfold FR3. rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity. }
  assert (GR3 : mem_grows m (FR3 m s ret regs)) by (unfold FR3; repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl).
  assert (BLK : forall q k i, live A q = Some k -> (0 <= i < k)%Z -> owned A (at_ q i) /\ ~ (s - 16384 <= u (at_ q i) < s)%Z).
  { intros q k i L Hi. pose proof (ai_live_hull A m (m_vmmaps md) q k Hinv L) as (Hk0 & _ & _ & OWN). pose proof (round16_ge k Hk0).
    destruct (OWN i ltac:(lia)) as (Ho & _). split; [exact Ho|]. intros R. exact (proj1 (proj2 (Hwin _ R)) Ho). }
  destruct (Z_lt_ge_dec size 3) as [SM|BG].
  { (* [comment removed for export] *)
    destruct (fz_small al_rom fx regs m s size (Z_to_bv 64 dp) ret ltac:(lia) ltac:(lia) ltac:(lia) Hret SOK H2 Hra Ha0 Ha1) as (r1 & RUN1 & Q2 & Q1 & Q10 & Q8 & Q9 & AG1).
    eapply rz_msteps; [exact (mp_halted _ Hpure) | exact (mp_lazy _ Hpure) | exact RUN1 |].
    rewrite <- (with_vmmaps_same md). apply (K fx A (FR3 m s ret regs) (m_vmmaps md) r1 Hz).
    - apply (ai_frame A m _ _ Hinv).
      + intros a Ho _. apply OUT3. intros R. exact (proj1 (proj2 (Hwin a ltac:(lia))) Ho).
      + intros a _ Hx. exact (GR3 a Hx).
      + intros a _ Hx. destruct (Z_lt_ge_dec (u a) (s - 24)); [rewrite OUT3 in Hx by lia; exact Hx|].
        destruct (Z_lt_ge_dec (u a) s); [exact (proj1 (Hwin a ltac:(lia))) | rewrite OUT3 in Hx by lia; exact Hx].
    - intros q; reflexivity.
    - exact Q10.
    - apply cs_kept_intro; csr; reflexivity.
    - intros a _ _ _ _ NW. apply OUT3. lia.
    - intros q k i L Hi. apply OUT3. destruct (BLK q k i L Hi) as [_ X]. lia.
    - intros a Hx. right; right. exact (GR3 a Hx).
    - reflexivity. - reflexivity. - reflexivity. - reflexivity.
    - apply (aroom_mono _ _ _ _ _ _ Hrm); lia. }
  (* [comment removed for export] *)
  assert (SOKh : store_ok SEGS m (Z_to_bv 64 0xef758) 8 = true) by exact Hhdl.
  destruct (fz_big al_rom fx regs m s size (Z_to_bv 64 dp) ret ltac:(lia) ltac:(lia) ltac:(lia) SOK SOKh H2 Hra Ha0 Ha1) as (r1 & RUN1 & Q2 & Q1 & Q10 & Q11 & Q8 & Q9 & AG1).
  eapply rz_msteps; [exact (mp_halted _ Hpure) | exact (mp_lazy _ Hpure) | exact RUN1 |].
  set (m1 := wbytes (FR3 m s ret regs) (Z_to_bv 64 0xef758) (word_to_le_bytes 8 (Z_to_bv 64 0x5cdd0))) in *.
  assert (OUT1 : forall a : word, ~ (s - 24 <= u a < s)%Z -> ~ (0xef758 <= u a < 0xef760)%Z -> m1 a = m a).
  { intros a H1' H2'. subst m1. rewrite wbytes_outside; [apply OUT3; exact H1' | rewrite length_N_to_le_bytes, u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]. }
  assert (GR1 : mem_grows m m1) by (subst m1; eapply mem_grows_trans; [exact GR3 | apply wbytes_grows]).
  assert (HW1 : W C A m1 md).
  { apply (W_entry C md m1 CK eq_refl Hinv Hpure Henv).
    - intros a Hw. unfold win in Hw; cbn in Hw. destruct (Hwin a ltac:(lia)) as (D & NO & _). split; [exact D | exact NO].
    - intros a Hc. cbn [inZs ll_clr LL16] in Hc. unfold inZ in Hc. cbn [fst snd] in Hc. destruct Hc as [Hc|[Hc|[Hc|[]]]]; [apply Hgot; lia | apply Hsev; lia | apply Hpmm; lia].
    - intros a NE. destruct (Z_lt_ge_dec (u a) (s - 24)); [| destruct (Z_lt_ge_dec (u a) s); [left; unfold win; cbn; lia|]].
      all: destruct (Z_lt_ge_dec (u a) 0xef758); [exfalso; apply NE; apply OUT1; lia|].
      all: destruct (Z_lt_ge_dec (u a) 0xef760); [right; unfold hcell; cbn; lia | exfalso; apply NE; apply OUT1; lia].
    - exact GR1.
    - rewrite p16_segs. subst m1. cbn [ll_hcell ll_devnull LL16]. apply rdn_wbytes_hit8. rewrite u_Z2bv by lia. lia. }
  assert (Ldp : live A (Z_to_bv 64 dp) = Some size) by (apply Hlive; lia).
  destruct (blk_range C A m1 md (Z_to_bv 64 dp) size CK HW1 Ldp ltac:(lia)) as [Gdp Tdp]. rewrite u_Z2bv in Gdp, Tdp by lia. rewrite Evm in Tdp.
  assert (PLD : payload C dp pl).
  { split; [cbn; rewrite <- Hsz; exact Ldp|]. split; [intros i Hi; cbn; apply Hpl; lia|]. split; [lia | rewrite <- Hsz; lia]. }
  (* [comment removed for export] *)
  assert (KF : forall (fx' : FPState) A' mf vm' rr kf bf, frm_zero (@fp_csr fx') -> W C A' mf (with_vmmaps vm' md) -> (forall q, live A' q = live A q) -> getr rr 10 = Z_to_bv 64 0 ->
               cs_kept regs rr -> aroom A' vm' kf bf -> (kR - FUZZ_CALLS <= kf)%Z -> (bR - fuzz_margin size <= bf)%Z ->
               realizes SEGS (mkCfg (@mkst fx' rr ret mf al_rom) (with_vmmaps vm' md)) S).
  { intros fx' A' mf vm' rr kf bf Hz' HWf LQ A0 CS HRf Hkf Hbf. apply (K fx' A' mf vm' rr Hz').
    - pose proof (w_inv _ _ _ _ HWf) as X. rewrite with_vmmaps_vmmaps in X. exact X.
    - exact LQ.
    - exact A0.
    - exact CS.
    - intros a N1 N2 N3 N4 N5. apply (w_frm _ _ _ _ HWf a); [exact N1 | exact N2 | exact N3 | unfold hcell; cbn; exact N4 | unfold scratch; cbn; rewrite LV; lia].
    - intros q k i Lq Hi. exact (w_live0 _ _ _ _ HWf q k i Lq Hi).
    - intros a Hx. exact (w_def _ _ _ _ HWf a Hx).
    - destruct (w_vm _ _ _ _ HWf) as (V1 & V2 & V3 & V4). rewrite with_vmmaps_vmmaps in V1. exact V1.
    - destruct (w_vm _ _ _ _ HWf) as (V1 & V2 & V3 & V4). rewrite with_vmmaps_vmmaps in V2. exact V2.
    - destruct (w_vm _ _ _ _ HWf) as (V1 & V2 & V3 & V4). rewrite with_vmmaps_vmmaps in V3. exact V3.
    - destruct (w_vm _ _ _ _ HWf) as (V1 & V2 & V3 & V4). rewrite with_vmmaps_vmmaps in V4. exact V4.
    - apply (aroom_mono _ _ _ _ _ _ HRf); lia. }
  assert (Q4 : getr r1 4 = Z_to_bv 64 0xffca8) by (rewrite (AG1 4) by notin_list; exact H4).
  assert (RKd : (RK_deser <= kR)%Z) by (pose proof RK_pmes_val; lia).
  assert (RBd : (RB_deser <= bR)%Z) by (pose proof (FZb size 1%Z ltac:(lia)) as X; unfold RB_edge in X; pose proof (RB_pmes_nonneg 1 ltac:(lia)); lia).
  apply (pixDeserialize_W C A m1 md r1 (s - 48) dp pl (Z_to_bv 64 0x5cd88) S CK HW1 Q2 ltac:(rewrite <- Zminus_mod_idemp_l, Hsp16; reflexivity)
           ltac:(rewrite Etop; unfold LSF; rewrite LV; lia) ltac:(rewrite Etop; lia) Q1 ltac:(red; apply bv_eq; reflexivity) Q4 Q10
           ltac:(rewrite Q11, Hsz; reflexivity) PLD ltac:(rewrite <- Hsz; lia)
           kR bR Hrm RKd RBd).
  unfold DK. intros A' m' vm' r2 HW' CS' PM' RES Hrm'.
  replace (Z_to_bv 64 0x5cd88) with (0x5cd88 : word) by (apply bv_eq; reflexivity).
  pose proof PM' as [F' L']. cbn [c_A0] in L'.
  assert (C1 : rdn SEGS m' (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret)).
  { rewrite (FRM_rdn16 C (s - 48) m1 m' (s - 8) 8 CK F') by (rewrite ?Etop, ?LV; lia). subst m1. unfold FR3. rdn_solve. }
  assert (C2 : rdn SEGS m' (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 8))).
  { rewrite (FRM_rdn16 C (s - 48) m1 m' (s - 16) 8 CK F') by (rewrite ?Etop, ?LV; lia). subst m1. unfold FR3. rdn_solve. }
  assert (C3 : rdn SEGS m' (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (getr regs 9))).
  { rewrite (FRM_rdn16 C (s - 48) m1 m' (s - 24) 8 CK F') by (rewrite ?Etop, ?LV; lia). subst m1. unfold FR3. rdn_solve. }
  assert (Y2 : getr r2 2 = Z_to_bv 64 (s - 48)) by (csr; reflexivity).
  pose proof (W_sok_win C A' m' _ (s - 48) 48 CK HW' ltac:(rewrite Etop, LV; lia) ltac:(rewrite Etop; cbn; lia)) as SOK'.
  destruct RES as [[A0 LQ] | (pix & v & cv & A2p & PO & PF)].
  - (* [comment removed for export] *)
    destruct (fz_B0 al_rom fx r2 m' s ret (getr regs 8) (getr regs 9) ltac:(lia) ltac:(lia) Hret SOK' C1 C2 C3 Y2 A0) as (r3 & RUN3 & V2 & V1 & V10 & V8 & V9 & AG3).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW')) | exact (mp_lazy _ (w_pure _ _ _ _ HW')) | exact RUN3 |].
    assert (HWf : W C A' (wbytes m' (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (with_vmmaps vm' md)).
    { apply (W_store_win C A' m' _ _ _ CK HW'); rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; rewrite ?LV; lia. }
    apply (KF fx A' _ vm' r3 _ _ Hz HWf LQ V10 ltac:(apply cs_kept_intro; csr; reflexivity) Hrm'); pose proof RK_pmes_val; [lia|].
    pose proof (FZb size 1%Z ltac:(lia)) as X. unfold RB_edge in X. pose proof (RB_pmes_nonneg 1 ltac:(lia)). lia.
  - (* [comment removed for export] *)
    pose proof PO as (PX & Rrc & Rtx & Hn4 & Lp & LpA & Lp0 & Ld & LdA & Ld0 & NEdp & RC & RQ).
    pose proof PF as (Ev & HOK & Hw & Hh & CMOK).
    destruct v as [w h d spp wpl rc xres yres fmt spec text cm datas].
    cbn [p_w p_h p_d p_spp p_wpl p_rc p_xres p_yres p_fmt p_spec p_text p_cmap p_data] in PX, Rrc, Rtx, Hn4, Ld, LdA, Ld0, NEdp, RC, RQ, Ev, HOK, Hw, Hh, CMOK.
    injection Ev as E8 E7 E6 E5 E4 E3 E2 E1. subst spp wpl rc xres yres fmt spec text.
    change (PIXV w h d (spp_of d) (wpl_of w d) 1%Z 0%Z 0%Z 0%Z 0%Z 0%Z cm datas) with (hdv w h d cm datas) in PX.
    pose proof PX as (Hp0 & Hp64 & WF & _).
    assert (Hh2 : (h <= 20000)%Z) by (destruct HOK as (_ & _ & X & _); exact X).
    destruct (blk_range C A' m' _ (Z_to_bv 64 pix) 64 CK HW' Lp ltac:(lia)) as [Gp TOPp]. rewrite u_Z2bv in Gp, TOPp by lia. rewrite Evm in TOPp.
    pose proof (alloc_top_lt (m_vmmaps md)) as ATL. unfold two_pow_64 in ATL.
    destruct (fz_B1 al_rom fx r2 m' s pix ltac:(lia) ltac:(lia) ltac:(lia) SOK' Y2 A2p) as (r3 & RUN3 & V2 & V1 & V10 & V11 & V12 & V13 & V14 & V15 & V16 & V17 & AG3).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW')) | exact (mp_lazy _ (w_pure _ _ _ _ HW')) | exact RUN3 |].
    set (m2 := wbytes m' (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (Z_to_bv 64 pix))).
    assert (HW2 : W C A' m2 (with_vmmaps vm' md)).
    { subst m2. apply (W_store_win C A' m' _ _ _ CK HW'); rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; rewrite ?LV; lia. }
    assert (OUT2 : forall x : word, ~ (s - 32 <= u x < s - 24)%Z -> m2 x = m' x).
    { intros x Hx. subst m2. apply wbytes_outside; rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; lia. }
    assert (PX2 : PIXat m2 pix (hdv w h d cm datas)) by (apply (PIXat_frame m'); [exact PX | intros x Hx; apply OUT2; lia]).
    assert (R8 : rdn SEGS m2 (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret)).
    { subst m2. rewrite rdn_wbytes_out_Z by (rewrite ?length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia). exact C1. }
    assert (R16 : rdn SEGS m2 (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 8))).
    { subst m2. rewrite rdn_wbytes_out_Z by (rewrite ?length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia). exact C2. }
    assert (R24 : rdn SEGS m2 (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (getr regs 9))).
    { subst m2. rewrite rdn_wbytes_out_Z by (rewrite ?length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia). exact C3. }
    assert (R32 : rdn SEGS m2 (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 pix))).
    { subst m2. apply rdn_wbytes_hit8. rewrite u_Z2bv by lia. lia. }
    assert (T4 : getr r3 4 = Z_to_bv 64 TP9) by (unfold TP9; csr; reflexivity).
    pose proof (RB_pmes_nonneg h ltac:(lia)) as RBn. pose proof (FZb size h ltac:(lia)) as RBe. unfold RB_edge in RBe. pose proof RK_pmes_val as RKv.
    replace (0x77a8c : word) with (Z_to_bv 64 PC_pixMeasureEdgeSmoothness) by (apply bv_eq; reflexivity).
    apply (HPM fx C A' m2 (with_vmmaps vm' md) r3 (s - 48)%Z pix w h d cm datas (Z_to_bv 64 0x5cdb0) S Hz CK HW2 V2
             ltac:(rewrite <- Zminus_mod_idemp_l, Hsp16; reflexivity)
             ltac:(rewrite Etop; unfold PMES_STACK, GEP_STACK, NAN_STACK, NEX_STACK, RNW_STACK, CALLOC_STACK, ALLOC_STACK, LSF; rewrite LV; lia)
             ltac:(rewrite Etop; lia) V1 ltac:(red; apply bv_eq; reflexivity) T4 V10 V11 V12 V13
             ltac:(rewrite V14; f_equal; lia) ltac:(rewrite V15; f_equal; lia) ltac:(rewrite V16; f_equal; lia) V17
             PX2 HOK Hw Hh Lp Ld (kR - RK_deser)%Z (bR - RB_deser)%Z Hrm' ltac:(lia) ltac:(lia)).
    intros fx2 A3 m3 vm3 r4 Hz2 HW3 CS3 PM3 LQ3 Hrm3. rewrite ?with_vmmaps_twice in HW3 |- *.
    replace (Z_to_bv 64 0x5cdb0) with (0x5cdb0 : word) by (apply bv_eq; reflexivity).
    pose proof PM3 as [F3 L3].
    replace (s - 48 + 16)%Z with (s - 32)%Z in F3 by lia.
    assert (Y3 : getr r4 2 = Z_to_bv 64 (s - 48)) by (csr; reflexivity).
    destruct (fz_C al_rom fx2 r4 m3 s ltac:(lia) ltac:(lia) Y3) as (r5 & RUN5 & X2 & X1 & X10 & AG5).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW3)) | exact (mp_lazy _ (w_pure _ _ _ _ HW3)) | exact RUN5 |].
    assert (KEEP : forall (p k : Z) (x : word), live A' (Z_to_bv 64 p) = Some k -> (0 <= p)%Z -> (p + k <= 2 ^ 64)%Z -> (p <= u x < p + k)%Z -> m3 x = m2 x).
    { intros p k x Lx G0 TPx Hx. exact (LIVK_at A' m2 m3 p k x L3 Lx G0 TPx Hx). }
    assert (PX3 : PIXat m3 pix (hdv w h d cm datas)).
    { apply (PIXat_frame m2); [exact PX2 | intros x Hx; apply (KEEP pix 64%Z x Lp); lia]. }
    assert (D8 : rdn SEGS m3 (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret)).
    { rewrite (FRM_rdn16 C (s - 32) m2 m3 (s - 8) 8 CK F3) by (rewrite ?Etop, ?LV; lia). exact R8. }
    assert (D16 : rdn SEGS m3 (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 8))).
    { rewrite (FRM_rdn16 C (s - 32) m2 m3 (s - 16) 8 CK F3) by (rewrite ?Etop, ?LV; lia). exact R16. }
    assert (D24 : rdn SEGS m3 (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (getr regs 9))).
    { rewrite (FRM_rdn16 C (s - 32) m2 m3 (s - 24) 8 CK F3) by (rewrite ?Etop, ?LV; lia). exact R24. }
    assert (D32 : rdn SEGS m3 (Z_to_bv 64 (s - 32)) 8 = Some (Z_to_le_bytes 8 pix)).
    { rewrite (FRM_rdn16 C (s - 32) m2 m3 (s - 32) 8 CK F3) by (rewrite ?Etop, ?LV; lia). rewrite R32. unfold word_to_le_bytes. rewrite u_Z2bv by lia. reflexivity. }
    assert (Lp3 : live A3 (Z_to_bv 64 pix) = Some 64%Z) by (rewrite LQ3; exact Lp).
    assert (T5 : getr r5 4 = Z_to_bv 64 0xffca8) by (csr; reflexivity).
    apply (pixDestroy_W C A3 m3 (with_vmmaps vm3 md) r5 (s - 48) (s - 32) pix cm (4 * c_nalloc cv) (4 * (wpl_of w d * h)) (hdv w h d cm datas) cv (Z_to_bv 64 0x5cdb8) S CK HW3 X2
             ltac:(rewrite <- Zminus_mod_idemp_l, Hsp16; reflexivity) ltac:(rewrite Etop; unfold ALLOC_STACK; rewrite LV; lia) ltac:(lia) ltac:(rewrite Etop; lia)
             X1 ltac:(red; apply bv_eq; reflexivity) T5 X10 D32 PX3 eq_refl eq_refl eq_refl Lp3 Lp0).
    + right. cbn [p_data hdv]. rewrite LQ3. split; [exact Ld|]. split; [exact Ld0|]. split; [lia|]. split; [exact NEdp|].
      intros NZ. destruct RC as [Z0 | (Hc1 & CM & Lc & La & Hna & LcA & LaA & Lc0 & La0 & N1 & N2 & N3 & N4 & N5)]; [lia | split; assumption].
    + destruct RC as [Z0 | (Hc1 & CM & Lc & La & Hna & LcA & LaA & Lc0 & La0 & N1 & N2 & N3 & N4 & N5)]; [left; exact Z0 | right].
      pose proof CM as (Hc0 & Hc64 & _).
      destruct (blk_range C A' m' _ (Z_to_bv 64 cm) 24 CK HW' Lc ltac:(lia)) as [Gc TOPc]. rewrite u_Z2bv in Gc, TOPc by lia. rewrite Evm in TOPc.
      split; [apply (CMAPat_frame m2); [apply (CMAPat_frame m'); [exact CM | intros x Hx; apply OUT2; lia] | intros x Hx; apply (KEEP cm 24%Z x Lc); lia]|].
      rewrite !LQ3. repeat (split; [assumption|]). exact Hna.
    + intros A4 m4 vm4 r6 HW4 CS4 PD4 PM4 Z4 RT4. rewrite ?with_vmmaps_twice in HW4 |- *.
      replace (Z_to_bv 64 0x5cdb8) with (0x5cdb8 : word) by (apply bv_eq; reflexivity).
      pose proof PM4 as [F4 L4]. replace (s - 32 + 8)%Z with (s - 24)%Z in F4 by lia.
      assert (G8 : rdn SEGS m4 (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret)).
      { rewrite (FRM_rdn16 C (s - 24) m3 m4 (s - 8) 8 CK F4) by (rewrite ?Etop, ?LV; lia). exact D8. }
      assert (G16 : rdn SEGS m4 (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 8))).
      { rewrite (FRM_rdn16 C (s - 24) m3 m4 (s - 16) 8 CK F4) by (rewrite ?Etop, ?LV; lia). exact D16. }
      assert (G24 : rdn SEGS m4 (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (getr regs 9))).
      { rewrite (FRM_rdn16 C (s - 24) m3 m4 (s - 24) 8 CK F4) by (rewrite ?Etop, ?LV; lia). exact D24. }
      assert (Y6 : getr r6 2 = Z_to_bv 64 (s - 48)) by (csr; reflexivity).
      destruct (fz_E al_rom fx2 r6 m4 s ret (getr regs 8) (getr regs 9) ltac:(lia) ltac:(lia) Hret G8 G16 G24 Y6) as (r7 & RUN7 & U2 & U1 & U10 & U8 & U9 & AG7).
      eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW4)) | exact (mp_lazy _ (w_pure _ _ _ _ HW4)) | exact RUN7 |].
      destruct PD4 as (P1 & P2 & P3 & P4). cbn [p_data hdv] in P2, P4.
      assert (LQf : forall q, live A4 q = live A q).
      { intros q.
        destruct (bv_eq_dec _ q (Z_to_bv 64 pix)) as [->|N1]; [rewrite P1, LpA; reflexivity|].
        destruct (bv_eq_dec _ q (Z_to_bv 64 datas)) as [->|N2].
        { rewrite LdA. apply P2. pose proof (wf_data _ WF) as Rdat. cbn [p_data hdv] in Rdat.
          destruct (blk_range C A' m' _ (Z_to_bv 64 datas) _ CK HW' Ld ltac:(lia)) as [Gd _]. rewrite u_Z2bv in Gd by lia. lia. }
        destruct RC as [Z0 | (Hc1 & CM & Lc & La & Hna & LcA & LaA & Lc0 & La0 & M1 & M2 & M3 & M4 & M5)].
        - rewrite (P4 q N1 ltac:(intros _; exact N2) ltac:(intros X; exfalso; exact (X Z0))), LQ3. apply RQ; [exact N1 | exact N2 | intros X; exfalso; exact (X Z0)].
        - destruct (P3 ltac:(lia)) as [P3a P3b].
          destruct (bv_eq_dec _ q (Z_to_bv 64 cm)) as [->|N3]; [rewrite P3a, LcA; reflexivity|].
          destruct (bv_eq_dec _ q (Z_to_bv 64 (c_arr cv))) as [->|N4]; [rewrite P3b, LaA; reflexivity|].
          rewrite (P4 q N1 ltac:(intros _; exact N2) ltac:(intros _; split; [exact N3 | exact N4])), LQ3. apply RQ; [exact N1 | exact N2 | intros _; split; [exact N3 | exact N4]]. }
      rewrite with_vmmaps_vmmaps in RT4.
      pose proof (RT4 _ _ Hrm3 (proj1 (aroom_nonneg _ _ _ _ Hrm3)) (proj2 (aroom_nonneg _ _ _ _ Hrm3))) as Hrm4. rewrite !Z.sub_0_r in Hrm4.
      apply (KF fx2 A4 m4 vm4 r7 _ _ Hz2 HW4 LQf U10 ltac:(apply cs_kept_intro; csr; reflexivity) Hrm4); lia.
Qed.
End Final.
End O9LeptFuzz.

From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng Require MallocLayout.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng Require MallocInv_auxv.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng Require MallocAllocLayout.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.O9 Require O9Kit.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.O9 Require O9LeptNuma.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.O9 Require O9LeptNfe.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.O9 Require O9LeptProfW.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.O9 Require O9LeptEdge.
Module O9LeptPinsI.
Import Stdlib.ZArith.ZArith.
Import Stdlib.NArith.NArith.
Import Stdlib.Lists.List.
Import Stdlib.micromega.Lia.
Import Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.LinuxProcessSem.StackLayout.
Import LinuxProcessSemantics.LinuxProcessSem.Fs.
Import LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.LinuxProcessSem.Monad.
Import LinuxProcessSemantics.LinuxProcessSem.Specs.
Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.leptonica.edge_fuzzer.images.Plain.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.CatExec.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.CatSim.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.StepTac.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.AllocIface.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.PureModel.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.VmLedger.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.StoreOk.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng.MallocLayout.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng.MallocInv_auxv.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng.AllocBase.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng.MallocAllocLayout.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica.WalksLib.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica.LeptDefs.
Import O9Kit.
Import O9Drv1.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.O9.O9LeptBase.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng.AllocSure.
(* [comment removed for export] *)







Import O9Kit.O9MallocLayout.

Import O9Drv1.O9FuzzIface.



Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

#[local] Notation "'u'" := bv_unsigned (only parsing).

Lemma rdn_agree_on : forall segs (M M' : word -> option byte) (a : Z) (n : nat),
  0 <= a < 2 ^ 64 -> a + Z.of_nat n <= 2 ^ 64 -> (forall x : word, a <= u x < a + Z.of_nat n -> M' x = M x) ->
  rdn segs M' (Z_to_bv 64 a) n = rdn segs M (Z_to_bv 64 a) n.
Proof.
  intros segs M M' a n Ha Hn E. apply rdn_ext; rewrite u_Z2bv by lia; [lia|]. intros x Hx. apply E. lia.
Qed.

#[export] Instance s16_lept_pins : @LeptPins (@mallocng_alloc_layout LS16) LL16.
Proof.
  constructor; cbn [al_segs al_rom al_malloc_pc al_free_pc al_gp al_globals al_grantable al_errno_slot al_in_ro al_in_rw
                    al_image_hi al_ret_ok al_mmap_threshold al_env mallocng_alloc_layout
                    ll_ro ll_clr ll_lg ll_errno ll_ag ll_img ll_hcell ll_devnull LL16 fst snd inZs]; unfold inZ; cbn [fst snd].
  - (* [comment removed for export] *) intros sp0 argv envp M a (_ & _ & RO & _) Ha. rewrite <- (WalksLib.zbv_self a). apply RO. cbn [IMG_LO RW_LO LS16]. exact Ha.
  - (* [comment removed for export] *) intros sp0 argv envp M M' (NL & PS & RO & AUX & GOT) E. pose proof (u64_range sp0) as Rsp.
    unfold mallocng_env. cbn [ml_segs A_NEED_LOCKS A_PAGE_SIZE A_LIBC A_GOT_SSP IMG_LO RW_LO LS16] in *.
    split; [| split; [| split; [| split]]].
    + rewrite (rdn_agree_on _ M M' 0x11ff3b 1); [exact NL | lia | cbn; lia |]. intros x Hx. apply E. right; right; left. cbn in Hx. lia.
    + rewrite (rdn_agree_on _ M M' 0x11ff68 8); [exact PS | lia | cbn; lia |]. intros x Hx. apply E. right; right; left. cbn in Hx. lia.
    + intros a Ha. rewrite E; [exact (RO a Ha) | left; rewrite u_Z2bv by lia; lia].
    + apply (aux_env_frame sp0 argv envp M M' AUX). intros a Ha. unfold aux_addr in Ha. cbn [A_LIBC LS16] in Ha. rewrite u_Z2bv in Ha by lia.
      apply E. destruct Ha as [Ha|Ha]; [right; right; left; lia | right; right; right; exact Ha].
    + intros a Ha. rewrite u_Z2bv in Ha by lia. rewrite E; [apply GOT; rewrite u_Z2bv by lia; exact Ha | right; left; left; rewrite u_Z2bv by lia; lia].
  - (* [comment removed for export] *) intros a Hg. unfold mallocng_globals in Hg. cbn [A_LOCK A_MALLOC_REPLACED LS16] in Hg. rewrite !u_Z2bv in Hg by lia. unfold CTX_SIZE in Hg. lia.
  - (* [comment removed for export] *) intros a He. unfold mallocng_errno_slot in He. cbn [A_ERRNO LS16] in He. rewrite !u_Z2bv in He by lia. lia.
  - (* [comment removed for export] *) intros a [G1 G2]. cbn [IMG_LO IMG_HI LS16] in G2. lia.
  - intros a H. unfold mallocng_in_ro in H. cbn [IMG_LO RW_LO LS16] in H. lia.
  - intros a H. unfold mallocng_in_rw in H. cbn [RW_LO IMG_HI LS16] in H. lia.
  - intros r H. exact H.
  - reflexivity.
  - intros z Hz. lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - intros z Hz. lia.
  - split; [lia|]. split; [lia|]. intros z Hz. lia.
  - lia.
Qed.

#[export] Instance s16_pins16 : @O9Pins (@mallocng_alloc_layout LS16) (@mallocng_calloc_layout LS16).
Proof. constructor; cbn; try reflexivity; apply bv_eq; reflexivity. Qed.

(* [comment removed for export] *)
Theorem s16_fuzz_call : forall ASR : @AllocSure (@mallocng_alloc_layout LS16) (@mallocng_calloc_layout LS16),
  @fuzz_call_contract (@mallocng_alloc_layout LS16) (@mallocng_calloc_layout LS16) ASR.
Proof.
  intros ASR.
  apply (@O9LeptFuzz.lept_fuzz_call _ _ ASR s16_lept_pins s16_pins16).
  apply (@O9LeptEdge.pixMeasureEdgeSmoothness_W _ _ ASR s16_lept_pins s16_pins16).
  - exact (@O9LeptNuma.numaDestroy_W _ _ ASR s16_lept_pins s16_pins16).
  - exact (@O9LeptProfW.pixGetEdgeProfile_W _ _ ASR s16_lept_pins s16_pins16 (@O9LeptNuma.numaCreate_W _ _ ASR s16_lept_pins s16_pins16) (@O9LeptNuma.numaAddNumber_store_W _ _ ASR s16_lept_pins s16_pins16)).
  - exact (@O9LeptNfe.numaFindExtrema_W _ _ ASR s16_lept_pins s16_pins16).
Qed.
End O9LeptPinsI.

From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.CliDriver Require Amb.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.CliDriver Require SymExec2.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.CliDriver Require SymExec2Sound.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.CliDriver Require SymDrive.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.CliDriver Require SymDriveX.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common Require RefLayout.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.O9 Require O9Main.
Module O9Pins.
Import Stdlib.ZArith.ZArith.
Import Stdlib.Lists.List.
Import Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.LinuxProcessSem.StackLayout.
Import LinuxProcessSemantics.LinuxProcessSem.Fs.
Import LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.leptonica.edge_fuzzer.images.Plain.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.CliDriver.Amb.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.CliDriver.SymExec2.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.CliDriver.SymExec2Sound.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.CliDriver.SymDrive.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.CliDriver.SymDriveX.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.AllocIface.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.MemSplit.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.RefLayout.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng.MallocLayout.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng.MallocInv_auxv.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng.AllocBase.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng.MallocAllocLayout.
Import O9Kit.
Import O9Drv1.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.O9.O9Main.
(* [comment removed for export] *)
(* [comment removed for export] *)







Import O9Kit.O9MallocLayout. Import O9Kit.O9Startup. Import O9Kit.O9StartupDefs. Import O9Kit.O9StartupFacts.

Import O9Drv1.O9MainEntry. Import O9Drv1.O9Open. Import O9Drv1.O9Malloc65536.

Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.

Abbreviation RSEGS := Plain.M.loaded_segments.

Lemma need_locks_img : rdn RSEGS (fun _ => None) (Z_to_bv 64 0x11ff3b) 1 = Some [Z_to_bv 8 0].
Proof. vm_compute. reflexivity. Qed.

Theorem s16_pins : @O9Main.pins (@mallocng_alloc_layout LS16).
Proof.
  constructor; cbn [al_segs al_rom al_malloc_pc al_free_pc al_gp al_globals al_grantable al_errno_slot al_in_ro al_in_rw
                    al_image_hi al_ret_ok al_mmap_threshold al_env mallocng_alloc_layout].
  - reflexivity.
  - reflexivity.
  - apply bv_eq. reflexivity.
  - apply bv_eq. reflexivity.
  - reflexivity.
  - intros a Hg. unfold mallocng_globals in Hg. cbn [A_LOCK A_MALLOC_REPLACED LS16] in Hg.
    rewrite !u_small in Hg by lia. unfold CTX_SIZE in Hg. lia.
  - intros a Hg. unfold mallocng_grantable in Hg. cbn [IMG_LO IMG_HI LS16] in Hg. exact Hg.
  - intros a He. unfold mallocng_errno_slot in He. cbn [A_ERRNO LS16] in He. rewrite !u_small in He by lia. lia.
  - intros a H. unfold mallocng_in_ro in H. cbn [IMG_LO RW_LO LS16] in H. lia.
  - intros a H. unfold mallocng_in_rw in H. cbn [RW_LO IMG_HI LS16] in H. lia.
  - cbn. lia.
  - intros k Hk. exact Hk.
  - unfold mallocng_mmap_threshold. lia.
  - intros AMB sp0 a0s path envv tid regs0 mem0 Hvsp Hva Hve ME M (HEa & HEl & HEr).
    assert (Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z) by exact (proj1 Hvsp).
    assert (Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z) by exact (proj1 (proj2 Hvsp)).
    assert (Hal : (bv_unsigned sp0 mod 16 = 0)%Z) by exact (proj2 (proj2 Hvsp)).
    assert (LIBC : forall (a : Z) n, (0xffbd8 <= a)%Z -> (a + Z.of_nat n <= 0x11ffa8)%Z -> (a + Z.of_nat n <= 0xffc04 \/ 0xffc08 <= a)%Z ->
              (a + Z.of_nat n <= 0x11fcf0 \/ 0x11ff10 <= a)%Z ->   (* [comment removed for export] *)
              rdn RSEGS M (Z_to_bv 64 a) n = rdn RSEGS (D_main sp0 [a0s; path] envv a_hwcap a_draw tid) (Z_to_bv 64 a) n).
    { intros a n H1 H2 H3 H4. apply rdn_agree. intros j Hj. rewrite u_small by lia.
      rewrite HEl by (rewrite u_small by lia; lia).
      apply (main_entry_mem_data sp0 [a0s; path] envv tid regs0 mem0 ME). rewrite u_small, stack_max_size_val by lia. lia. }
    unfold mallocng_env. cbn [ml_segs A_NEED_LOCKS A_PAGE_SIZE A_LIBC A_GOT_SSP IMG_LO RW_LO LS16].
    split; [| split; [| split; [| split]]].
    + assert (NL : D_main sp0 [a0s; path] envv a_hwcap a_draw tid (Z_to_bv 64 0x11ff3b) = None).
      { apply (D_main_none sp0 [a0s; path] envv a_hwcap a_draw tid 0x11ff3b%Z Hva Hlo Hhi). vm_compute. reflexivity. }
      rewrite (LIBC 0x11ff3b%Z 1%nat) by (cbn; lia). rewrite <- need_locks_img. apply rdn_agree.
      intros j Hj. destruct j as [|j]; [| exfalso; lia].
      replace (bv_unsigned (Z_to_bv 64 0x11ff3b) + Z.of_nat 0)%Z with 0x11ff3b%Z by (rewrite u_small by lia; reflexivity).
      rewrite NL. reflexivity.
    + rewrite (LIBC 0x11ff68%Z 8%nat) by (cbn; lia). rewrite (D_main_pagesize sp0 [a0s; path] envv tid Hva). reflexivity.
    + intros a Ha. apply HEr. left. rewrite u_small by lia. lia.
    + apply (aux_env_intro RPH sp0 [a0s; path] envv a_uid a_hwcap a_draw M Hva Hve Hlo Hhi Hal).
      * intros a Ha. rewrite HEa by exact Ha.
        rewrite (main_entry_mem_above sp0 [a0s; path] envv tid regs0 mem0 ME a Ha). apply wrap_above_sp. exact Ha.
      * cbn [ml_segs A_LIBC LS16]. change (bv_unsigned (Z_to_bv 64 0x11ff38) + 8)%Z with 0x11ff40%Z.
        rewrite (LIBC 0x11ff40%Z 8%nat) by (cbn; lia). rewrite n_to_le_8_spec.
        rewrite (D_main_auxvp sp0 a0s path envv tid Hvsp), (auxvp_eq sp0 a0s path envv). reflexivity.
    + intros a Ha. change (bv_unsigned (Z_to_bv 64 0xee6f8)) with 0xee6f8%Z in Ha. apply HEr. right. rewrite u_small by lia. lia.
Qed.
End O9Pins.

From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.CliDriver Require Spec.
Module O9Closed.
Import Stdlib.ZArith.ZArith.
Import Stdlib.Lists.List.
Import Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.LinuxProcessSem.StackLayout.
Import LinuxProcessSemantics.LinuxProcessSem.Fs.
Import LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.leptonica.edge_fuzzer.images.Plain.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.AllocIface.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng.MallocLayout.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng.MallocAllocLayout.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng.AllocBase.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng.AllocSure.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.CliDriver.Spec.
Import O9Kit.
Import O9Pins.
Import O9Drv1.
Import O9LeptPinsI.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.O9.O9Main.
(* [comment removed for export] *)







Import O9Kit.O9MallocLayout. Import O9Kit.O9Alloc. Import O9Kit.O9Sure.


Import O9Drv1.O9FuzzIface.

Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem s16_realizes :
  forall sp brk mbase draw lim (inp : ProcInput),
    valid_sp sp -> valid_brk Plain.M.loaded_segments brk -> (2 ^ 34 <= lim)%Z ->
    valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
    entry_stack_fits sp (in_argv inp) (in_envp inp) ->
    realizes Plain.M.loaded_segments
      (init_config Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs sp brk mbase draw lim inp)
      (spec (in_argv inp) (in_fs inp)).
Proof.
  exact (@O9Main.ref_realizes_spec_pins _ _ s16_sure O9Pins.s16_pins (s16_fuzz_call s16_sure)).
Qed.
End O9Closed.
