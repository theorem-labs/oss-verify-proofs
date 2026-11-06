(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode SysStep InitMem.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import MM_syscalls.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import SysStepF.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg AProto ABase AKit AKit2 ARep ARepKit ABytes AFrameD RT_stubs. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_ammap. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_ammap.F_ammap. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AMalloc_iface AEmbRep.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.W2 Require Import PrintfFmt2 PrintfRegs PrintfEmb ExhSoc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC2. Context {rc : runConstT}.

Lemma disjoint_from_sub : forall W A n A' n', disjoint_from W A n -> A <= A' -> A' + n' <= A + n -> disjoint_from W A' n'.
Proof. induction W as [|[lo hi] W IH]; cbn; intros A n A' n' H H1 H2; [exact I|]. destruct H as [H H']. split; [lia| eapply IH; eauto]. Qed.

Lemma avoid_drop : forall a n RESV X st, avoids_all a n (RESV ++ asec_ranges X) = true -> achunks X = achunks st ->
  avoids_all a n (RESV ++ flat_map sec_iv (achunks st)) = true.
Proof.
  intros a n RESV X st H E. unfold avoids_all, asec_ranges in *. rewrite !forallb_app in *. rewrite E in H.
  apply andb_prop in H as [H1 H2]. apply andb_prop in H2 as [H2 _]. rewrite H1, H2. reflexivity.
Qed.

Lemma emb_cells_transport : forall st m m' W, emb_cells st m -> munch W m m' -> wmono asegs m m' ->
  disjoint_from W AEMB 56 -> (let '(d, cap, _) := a_emb st in cap = 0 \/ disjoint_from W d cap) -> emb_cells st m'.
Proof.
  intros st m m' W EC MU WM DA DB. unfold emb_cells in *. destruct (a_emb st) as [[d cap] sz].
  assert (T : forall A cs, rw_cells asegs m A cs -> AEMB <= A -> A + Z.of_nat (cells_size cs) <= AEMB + 56 -> rw_cells asegs m' A cs).
  { intros A cs H H1 H2. eapply rw_cells_transport; [exact H| exact MU| exact WM|]. eapply disjoint_from_sub; [exact DA| exact H1| exact H2]. }
  destruct EC as [MTX EC]. split; [apply T; [exact MTX| unfold AEMB; lia| unfold AEMB; cbn; lia]|].
  destruct (cap =? 0) eqn:C0.
  - destruct EC as (PTR & SZ & VEC). split; [apply T; [exact PTR| lia| unfold AEMB; cbn; lia]|]. split; [exact SZ|]. apply T; [exact VEC| lia| unfold AEMB; cbn; lia].
  - apply Z.eqb_neq in C0. destruct DB as [DB|DB]; [contradiction|].
    destruct EC as (PTR & VEC & P1 & P2 & P3 & P4 & P5 & P6 & (junk & OLD)).
    split; [apply T; [exact PTR| lia| unfold AEMB; cbn; lia]|]. split; [apply T; [exact VEC| lia| unfold AEMB; cbn; lia]|].
    repeat (split; [assumption|]). exists junk. eapply rw_cells_transport; [exact OLD| exact MU| exact WM|].
    cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by (unfold EMB_INIT in P2; lia). exact DB.
Qed.

Theorem exh_first : exh_first_stmt.
Proof.
  unfold exh_first_stmt.
  intros RNG R RESV k' Q ra sp gp tp t0 t1 t2 s1 a0 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L st c lo.
  remember (aregion_info L c) as RI eqn:ERI.
  intros ST CEIL LO SPHI MI TP RELRO FC XC EC CAPB ROK RILO RIHI RIRES RIOLD FLAG CR EXM RIMG RSTK RRI RBUF KONT.
  unfold EXH_STACK in *. unfold AIMG_HI in RILO. word_range sp SPR. pose proof atop_range as ATR.
  pose proof XC as XC0. destruct XC0 as (RC & TN & CF64 & CBC). destruct RC as (GPG & PGSZ & GOT & DPM & MLIM).
  pose proof (relro_word m 0xd1550 0xd3470 RELRO ltac:(unfold ARELRO_LO; clear; lia) ltac:(unfold ARELRO_HI; clear; lia) ltac:(vm_compute; reflexivity)) as G1208.
  pose proof (munch_refl [(RI + 68, RI + 69)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (RIR : 0 <= RI /\ RI + 128 <= 2^64) by (destruct RRI as (A & B & _); split; assumption).
  iprefix.
  step. step. step.
  step. step.
  step. step. step.
  step.
  apply evtF_done.

  lazymatch goal with |- implS _ _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
  assert (RELRO1 : arelro m1).
  { intros i Hi. rewrite (MU (wa i)); [apply RELRO; exact Hi|]. cbn [outside]. unfold ARELRO_LO, ARELRO_HI in Hi.
    split; [| exact I]. unfold wa. rewrite unsigned_lit by (clear -Hi; lia). clear -Hi RILO. lia. }
  assert (XC1 : exh_cells m1) by (unfold exh_cells; split; [unfold rmap_cells; repeat (split; [assumption|]); assumption|]; repeat (split; [assumption|]); assumption).
  assert (EC1 : emb_cells (exh_set c st) m1).
  { apply (emb_cells_transport st m m1 [(RI + 68, RI + 69)]%Z EC MU WM).
    - cbn [disjoint_from fst snd]. unfold AEMB. clear -RILO. lia.
    - destruct (a_emb st) as [[d0 cap0] sz0]. destruct RIOLD as [Z0|RIOLD]; [left; exact Z0| right]. cbn [disjoint_from fst snd]. clear -RIOLD. lia. }
  change EXH_LEN1 with (Z.of_nat 33).
  eapply (printf_emb_spec RNG RESV _ Q PrintfFmt2.RA1 PrintfFmt2.FMT1 33%nat PrintfFmt2.XF1 L) with (st := exh_set c st) (lo := lo).
  { exact PrintfFmt2.check1. }
  { reflexivity. }
  { clear; lia. }
  { apply PrintfRegs.xf1_regs. }
  { exact FC. }
  { exact SPHI. }
  { assumption. }
  { exact CEIL. }
  { exact LO. }
  { assumption. }
  { exact RELRO1. }
  { exact XC1. }
  { exact EC1. }
  { exact ROK. }
  { change (a_emb (exh_set c st)) with (a_emb st). destruct (a_emb st) as [[d0 cap0] sz0]. clear -CAPB. lia. }
  { exact RIMG. }
  { exact RSTK. }
  { exact RBUF. }

  intros st1 RNG1 m2 t0x t1x t2x a0x a1x a2x a3x a4x a5x a6x a7x t3x t4x t5x t6x PR1.
  unfold pr_ret in PR1. change (a_emb (exh_set c st)) with (a_emb st) in PR1.
  destruct (a_emb st) as [[d0 cap0] sz0] eqn:EA. destruct (a_emb st1) as [[d1 cap1] sz1] eqn:EA1.
  destruct PR1 as (FP1 & (e1 & ES1) & EC2 & RB2 & XC2 & RELRO2 & MU2 & MI2 & ST2 & CB2 & PROV1).

  assert (CL1 : cap1 = 0 \/ RI + 128 <= d1 \/ d1 + cap1 <= RI).
  { destruct PROV1 as [(-> & -> & _)|AV]; [exact RIOLD|].
    destruct (Z.eq_dec cap1 0) as [Z0|NZ]; [left; exact Z0| right].
    assert (CP : 0 < cap1). { unfold emb_cells in EC2. rewrite EA1 in EC2. destruct EC2 as [_ EC2]. replace (cap1 =? 0) with false in EC2 by (symmetry; apply Z.eqb_neq; exact NZ).
                              destruct EC2 as (_ & _ & _ & P2 & _). unfold EMB_INIT in P2. clear -P2. lia. }
    unfold avoids_all in AV. rewrite forallb_app in AV. apply andb_prop in AV as [AV _].
    pose proof (pcov_clear _ _ _ _ _ RIRES AV ltac:(clear; lia) CP) as C. clear -C. lia. }
  eapply cells_frameD in FLAG; [| exact MU2 | cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ fst snd length]; unfold AEMB; clear -RILO RIHI CEIL LO RIOLD CL1; lia].
  apply (rng_fp_le _ _ _ _ FP1) in RIMG. apply (rng_fp_le _ _ _ _ FP1) in RSTK.
  change (Uint63.to_Z PrintfFmt2.RA1) with 0x42264.
  replace (ret_pc (Z_to_bv 64 0x42264)) with (Z_to_bv 64 0x42264 : word) by (symmetry; apply ret_pc_even; [clear; lia|reflexivity]).
  iprefix.
  eapply evtF_cut; [eapply (soc_seg RNG1) with (c := c); exact CR|].
  intros ms3 PO3. unfold soc_post in PO3. subst ms3.
  step.
  apply evtF_done.
  destruct (PrintfFmt2.check2_all c CR) as (ci & szi & len2 & ECI & ESZ & ELEN & LB2 & CHK2).
  pose proof (PrintfRegs.xf2_regs ci szi) as XR. rewrite ECI, ESZ in XR.
  rewrite <- ELEN.
  eapply (printf_emb_spec RNG1 RESV k' Q PrintfFmt2.RA2 PrintfFmt2.FMT2 len2 (PrintfFmt2.XF2 ci szi) L) with (st := st1) (lo := lo).
  { exact CHK2. }
  { reflexivity. }
  { exact LB2. }
  { apply XR. }
  { exact FC. }
  { exact SPHI. }
  { assumption. }
  { exact CEIL. }
  { exact LO. }
  { assumption. }
  { exact RELRO2. }
  { exact XC2. }
  { exact EC2. }
  { exact ROK. }
  { rewrite EA1. clear -CB2 CAPB. lia. }
  { exact RIMG. }
  { exact RSTK. }
  { exact RB2. }

  intros st2 RNG2 m3 t0y t1y t2y a0y a1y a2y a3y a4y a5y a6y a7y t3y t4y t5y t6y PR2.
  unfold pr_ret in PR2. rewrite EA1 in PR2. destruct (a_emb st2) as [[d2 cap2] sz2] eqn:EA2.
  destruct PR2 as (FP2 & (e2 & ES2) & EC3 & RB3 & XC3 & RELRO3 & MU3 & MI3 & ST3 & CB3 & PROV2).
  assert (CL2 : cap2 = 0 \/ RI + 128 <= d2 \/ d2 + cap2 <= RI).
  { destruct PROV2 as [(-> & -> & _)|AV]; [exact CL1|].
    destruct (Z.eq_dec cap2 0) as [Z0|NZ]; [left; exact Z0| right].
    assert (CP : 0 < cap2). { unfold emb_cells in EC3. rewrite EA2 in EC3. destruct EC3 as [_ EC3]. replace (cap2 =? 0) with false in EC3 by (symmetry; apply Z.eqb_neq; exact NZ).
                              destruct EC3 as (_ & _ & _ & P2 & _). unfold EMB_INIT in P2. clear -P2. lia. }
    unfold avoids_all in AV. rewrite forallb_app in AV. apply andb_prop in AV as [AV _].
    pose proof (pcov_clear _ _ _ _ _ RIRES AV ltac:(clear; lia) CP) as C. clear -C. lia. }
  eapply cells_frameD in FLAG; [| exact MU3 | cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ fst snd length]; unfold AEMB; clear -RILO RIHI CEIL LO CL1 CL2; lia].
  change (Uint63.to_Z PrintfFmt2.RA2) with 0x422d8.
  replace (ret_pc (Z_to_bv 64 0x422d8)) with (Z_to_bv 64 0x422d8 : word) by (symmetry; apply ret_pc_even; [clear; lia|reflexivity]).
  apply KONT.
  unfold exh_first_ret. rewrite <- ERI. rewrite EA, EA2.
  split; [exact (fp_le_trans _ _ _ FP1 FP2)|].
  split. { exists e2. rewrite ES2, ES1. reflexivity. }
  split; [exact EC3|]. split; [exact RB3|]. split; [exact XC3|]. split; [exact FLAG|].
  split.
  { exists d1, cap1. split; [| split; [| split]].
    - unfold EXH_STACK. eapply munch_trans; [eapply munch_trans; [eapply munch_weaken; [| exact MU] | eapply munch_weaken; [| exact MU2]] | eapply munch_weaken; [| exact MU3]];
        unfold sub_fp; cbn [outside]; clear; intros q Hq; lia.
    - destruct PROV1 as [(E1 & E2 & _)|AV]; [left; split; assumption| right]. exact (avoid_drop _ _ _ _ st AV eq_refl).
    - assert (P1 : emb_prov RESV st d0 cap0 d1 cap1).
      { destruct PROV1 as [(E1 & E2 & _)|AV]; [left; split; assumption| right]. exact (avoid_drop _ _ _ _ st AV eq_refl). }
      destruct PROV2 as [(E1 & E2 & _)|AV]; [subst d2 cap2; exact P1| right]. apply (avoid_drop _ _ _ st1 st AV). rewrite ES1. reflexivity.
    -
      destruct (Z.eq_dec cap1 0) as [Z0|NZ]; [left; exact Z0| right]. unfold emb_cells in EC2. rewrite EA1 in EC2. destruct EC2 as [_ EC2].
      replace (cap1 =? 0) with false in EC2 by (symmetry; apply Z.eqb_neq; exact NZ). destruct EC2 as (_ & _ & _ & _ & _ & _ & _ & P7 & _). exact P7. }
  split; [exact MI3| exact ST3].
Qed.
End CANSEC2.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Exec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Tac OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.SysStep OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.InitMem.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.MM_syscalls.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.SysStepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import AProto.TwinB ABase.TwinB AKit.TwinB AKit2.TwinB ARep.TwinB ARepKit.TwinB ABytes.TwinB AFrameD.TwinB RT_stubs.TwinB.

  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_ammap.TwinB.F_ammap. Import AMalloc_iface.TwinB AEmbRep.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Import PrintfFmt2.TwinB PrintfRegs.TwinB PrintfEmb.TwinB ExhSoc.TwinB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC2. Context {rc : runConstT}.

Lemma disjoint_from_sub : forall W A n A' n', disjoint_from W A n -> A <= A' -> A' + n' <= A + n -> disjoint_from W A' n'.
Proof. induction W as [|[lo hi] W IH]; cbn; intros A n A' n' H H1 H2; [exact I|]. destruct H as [H H']. split; [lia| eapply IH; eauto]. Qed.

Lemma avoid_drop : forall a n RESV X st, avoids_all a n (RESV ++ asec_ranges X) = true -> achunks X = achunks st ->
  avoids_all a n (RESV ++ flat_map sec_iv (achunks st)) = true.
Proof.
  intros a n RESV X st H E. unfold avoids_all, asec_ranges in *. rewrite !forallb_app in *. rewrite E in H.
  apply andb_prop in H as [H1 H2]. apply andb_prop in H2 as [H2 _]. rewrite H1, H2. reflexivity.
Qed.

Lemma emb_cells_transport : forall st m m' W, emb_cells st m -> munch W m m' -> wmono bsegs m m' ->
  disjoint_from W AEMB 56 -> (let '(d, cap, _) := a_emb st in cap = 0 \/ disjoint_from W d cap) -> emb_cells st m'.
Proof.
  intros st m m' W EC MU WM DA DB. unfold emb_cells in *. destruct (a_emb st) as [[d cap] sz].
  assert (T : forall A cs, rw_cells bsegs m A cs -> AEMB <= A -> A + Z.of_nat (cells_size cs) <= AEMB + 56 -> rw_cells bsegs m' A cs).
  { intros A cs H H1 H2. eapply rw_cells_transport; [exact H| exact MU| exact WM|]. eapply disjoint_from_sub; [exact DA| exact H1| exact H2]. }
  destruct EC as [MTX EC]. split; [apply T; [exact MTX| unfold AEMB; lia| unfold AEMB; cbn; lia]|].
  destruct (cap =? 0) eqn:C0.
  - destruct EC as (PTR & SZ & VEC). split; [apply T; [exact PTR| lia| unfold AEMB; cbn; lia]|]. split; [exact SZ|]. apply T; [exact VEC| lia| unfold AEMB; cbn; lia].
  - apply Z.eqb_neq in C0. destruct DB as [DB|DB]; [contradiction|].
    destruct EC as (PTR & VEC & P1 & P2 & P3 & P4 & P5 & P6 & (junk & OLD)).
    split; [apply T; [exact PTR| lia| unfold AEMB; cbn; lia]|]. split; [apply T; [exact VEC| lia| unfold AEMB; cbn; lia]|].
    repeat (split; [assumption|]). exists junk. eapply rw_cells_transport; [exact OLD| exact MU| exact WM|].
    cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by (unfold EMB_INIT in P2; lia). exact DB.
Qed.

Theorem exh_first : exh_first_stmt.
Proof.
  unfold exh_first_stmt.
  intros RNG R RESV k' Q ra sp gp tp t0 t1 t2 s1 a0 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L st c lo.
  remember (aregion_info L c) as RI eqn:ERI.
  intros ST CEIL LO SPHI MI TP RELRO FC XC EC CAPB ROK RILO RIHI RIRES RIOLD FLAG CR EXM RIMG RSTK RRI RBUF KONT.
  unfold EXH_STACK in *. unfold AIMG_HI in RILO. word_range sp SPR. pose proof atop_range as ATR.
  pose proof XC as XC0. destruct XC0 as (RC & TN & CF64 & CBC). destruct RC as (GPG & PGSZ & GOT & DPM & MLIM).
  pose proof (relro_word m 0xd3668 0xd5588 RELRO ltac:(unfold ARELRO_LO; clear; lia) ltac:(unfold ARELRO_HI; clear; lia) ltac:(vm_compute; reflexivity)) as G1208.
  pose proof (munch_refl [(RI + 68, RI + 69)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (RIR : 0 <= RI /\ RI + 128 <= 2^64) by (destruct RRI as (A & B & _); split; assumption).
  iprefix.
  step. step. step.
  step. step.
  step. step. step.
  step.
  apply evtF_done.

  lazymatch goal with |- implS _ _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
  assert (RELRO1 : arelro m1).
  { intros i Hi. rewrite (MU (wa i)); [apply RELRO; exact Hi|]. cbn [outside]. unfold ARELRO_LO, ARELRO_HI in Hi.
    split; [| exact I]. unfold wa. rewrite unsigned_lit by (clear -Hi; lia). clear -Hi RILO. lia. }
  assert (XC1 : exh_cells m1) by (unfold exh_cells; split; [unfold rmap_cells; repeat (split; [assumption|]); assumption|]; repeat (split; [assumption|]); assumption).
  assert (EC1 : emb_cells (exh_set c st) m1).
  { apply (emb_cells_transport st m m1 [(RI + 68, RI + 69)]%Z EC MU WM).
    - cbn [disjoint_from fst snd]. unfold AEMB. clear -RILO. lia.
    - destruct (a_emb st) as [[d0 cap0] sz0]. destruct RIOLD as [Z0|RIOLD]; [left; exact Z0| right]. cbn [disjoint_from fst snd]. clear -RIOLD. lia. }
  change EXH_LEN1 with (Z.of_nat 33).
  eapply (printf_emb_spec RNG RESV _ Q PrintfFmt2.TwinB.PrintfFmt2.RA1 PrintfFmt2.TwinB.PrintfFmt2.FMT1 33%nat PrintfFmt2.TwinB.PrintfFmt2.XF1 L) with (st := exh_set c st) (lo := lo).
  { exact PrintfFmt2.TwinB.PrintfFmt2.check1. }
  { reflexivity. }
  { clear; lia. }
  { apply PrintfRegs.TwinB.PrintfRegs.xf1_regs. }
  { exact FC. }
  { exact SPHI. }
  { assumption. }
  { exact CEIL. }
  { exact LO. }
  { assumption. }
  { exact RELRO1. }
  { exact XC1. }
  { exact EC1. }
  { exact ROK. }
  { change (a_emb (exh_set c st)) with (a_emb st). destruct (a_emb st) as [[d0 cap0] sz0]. clear -CAPB. lia. }
  { exact RIMG. }
  { exact RSTK. }
  { exact RBUF. }

  intros st1 RNG1 m2 t0x t1x t2x a0x a1x a2x a3x a4x a5x a6x a7x t3x t4x t5x t6x PR1.
  unfold pr_ret in PR1. change (a_emb (exh_set c st)) with (a_emb st) in PR1.
  destruct (a_emb st) as [[d0 cap0] sz0] eqn:EA. destruct (a_emb st1) as [[d1 cap1] sz1] eqn:EA1.
  destruct PR1 as (FP1 & (e1 & ES1) & EC2 & RB2 & XC2 & RELRO2 & MU2 & MI2 & ST2 & CB2 & PROV1).

  assert (CL1 : cap1 = 0 \/ RI + 128 <= d1 \/ d1 + cap1 <= RI).
  { destruct PROV1 as [(-> & -> & _)|AV]; [exact RIOLD|].
    destruct (Z.eq_dec cap1 0) as [Z0|NZ]; [left; exact Z0| right].
    assert (CP : 0 < cap1). { unfold emb_cells in EC2. rewrite EA1 in EC2. destruct EC2 as [_ EC2]. replace (cap1 =? 0) with false in EC2 by (symmetry; apply Z.eqb_neq; exact NZ).
                              destruct EC2 as (_ & _ & _ & P2 & _). unfold EMB_INIT in P2. clear -P2. lia. }
    unfold avoids_all in AV. rewrite forallb_app in AV. apply andb_prop in AV as [AV _].
    pose proof (pcov_clear _ _ _ _ _ RIRES AV ltac:(clear; lia) CP) as C. clear -C. lia. }
  eapply cells_frameD in FLAG; [| exact MU2 | cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ fst snd length]; unfold AEMB; clear -RILO RIHI CEIL LO RIOLD CL1; lia].
  apply (rng_fp_le _ _ _ _ FP1) in RIMG. apply (rng_fp_le _ _ _ _ FP1) in RSTK.
  change (Uint63.to_Z PrintfFmt2.TwinB.PrintfFmt2.RA1) with 0x42bf4.
  replace (ret_pc (Z_to_bv 64 0x42bf4)) with (Z_to_bv 64 0x42bf4 : word) by (symmetry; apply ret_pc_even; [clear; lia|reflexivity]).
  iprefix.
  eapply evtF_cut; [eapply (soc_seg RNG1) with (c := c); exact CR|].
  intros ms3 PO3. unfold soc_post in PO3. subst ms3.
  step.
  apply evtF_done.
  destruct (PrintfFmt2.TwinB.PrintfFmt2.check2_all c CR) as (ci & szi & len2 & ECI & ESZ & ELEN & LB2 & CHK2).
  pose proof (PrintfRegs.TwinB.PrintfRegs.xf2_regs ci szi) as XR. rewrite ECI, ESZ in XR.
  rewrite <- ELEN.
  eapply (printf_emb_spec RNG1 RESV k' Q PrintfFmt2.TwinB.PrintfFmt2.RA2 PrintfFmt2.TwinB.PrintfFmt2.FMT2 len2 (PrintfFmt2.TwinB.PrintfFmt2.XF2 ci szi) L) with (st := st1) (lo := lo).
  { exact CHK2. }
  { reflexivity. }
  { exact LB2. }
  { apply XR. }
  { exact FC. }
  { exact SPHI. }
  { assumption. }
  { exact CEIL. }
  { exact LO. }
  { assumption. }
  { exact RELRO2. }
  { exact XC2. }
  { exact EC2. }
  { exact ROK. }
  { rewrite EA1. clear -CB2 CAPB. lia. }
  { exact RIMG. }
  { exact RSTK. }
  { exact RB2. }

  intros st2 RNG2 m3 t0y t1y t2y a0y a1y a2y a3y a4y a5y a6y a7y t3y t4y t5y t6y PR2.
  unfold pr_ret in PR2. rewrite EA1 in PR2. destruct (a_emb st2) as [[d2 cap2] sz2] eqn:EA2.
  destruct PR2 as (FP2 & (e2 & ES2) & EC3 & RB3 & XC3 & RELRO3 & MU3 & MI3 & ST3 & CB3 & PROV2).
  assert (CL2 : cap2 = 0 \/ RI + 128 <= d2 \/ d2 + cap2 <= RI).
  { destruct PROV2 as [(-> & -> & _)|AV]; [exact CL1|].
    destruct (Z.eq_dec cap2 0) as [Z0|NZ]; [left; exact Z0| right].
    assert (CP : 0 < cap2). { unfold emb_cells in EC3. rewrite EA2 in EC3. destruct EC3 as [_ EC3]. replace (cap2 =? 0) with false in EC3 by (symmetry; apply Z.eqb_neq; exact NZ).
                              destruct EC3 as (_ & _ & _ & P2 & _). unfold EMB_INIT in P2. clear -P2. lia. }
    unfold avoids_all in AV. rewrite forallb_app in AV. apply andb_prop in AV as [AV _].
    pose proof (pcov_clear _ _ _ _ _ RIRES AV ltac:(clear; lia) CP) as C. clear -C. lia. }
  eapply cells_frameD in FLAG; [| exact MU3 | cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ fst snd length]; unfold AEMB; clear -RILO RIHI CEIL LO CL1 CL2; lia].
  change (Uint63.to_Z PrintfFmt2.TwinB.PrintfFmt2.RA2) with 0x42c68.
  replace (ret_pc (Z_to_bv 64 0x42c68)) with (Z_to_bv 64 0x42c68 : word) by (symmetry; apply ret_pc_even; [clear; lia|reflexivity]).
  apply KONT.
  unfold exh_first_ret. rewrite <- ERI. rewrite EA, EA2.
  split; [exact (fp_le_trans _ _ _ FP1 FP2)|].
  split. { exists e2. rewrite ES2, ES1. reflexivity. }
  split; [exact EC3|]. split; [exact RB3|]. split; [exact XC3|]. split; [exact FLAG|].
  split.
  { exists d1, cap1. split; [| split; [| split]].
    - unfold EXH_STACK. eapply munch_trans; [eapply munch_trans; [eapply munch_weaken; [| exact MU] | eapply munch_weaken; [| exact MU2]] | eapply munch_weaken; [| exact MU3]];
        unfold sub_fp; cbn [outside]; clear; intros q Hq; lia.
    - destruct PROV1 as [(E1 & E2 & _)|AV]; [left; split; assumption| right]. exact (avoid_drop _ _ _ _ st AV eq_refl).
    - assert (P1 : emb_prov RESV st d0 cap0 d1 cap1).
      { destruct PROV1 as [(E1 & E2 & _)|AV]; [left; split; assumption| right]. exact (avoid_drop _ _ _ _ st AV eq_refl). }
      destruct PROV2 as [(E1 & E2 & _)|AV]; [subst d2 cap2; exact P1| right]. apply (avoid_drop _ _ _ st1 st AV). rewrite ES1. reflexivity.
    -
      destruct (Z.eq_dec cap1 0) as [Z0|NZ]; [left; exact Z0| right]. unfold emb_cells in EC2. rewrite EA1 in EC2. destruct EC2 as [_ EC2].
      replace (cap1 =? 0) with false in EC2 by (symmetry; apply Z.eqb_neq; exact NZ). destruct EC2 as (_ & _ & _ & _ & _ & _ & _ & P7 & _). exact P7. }
  split; [exact MI3| exact ST3].
Qed.
End CANSEC2.
End TwinB.
