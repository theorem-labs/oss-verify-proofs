(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import PmLibDefs_u5 PmLibSpecs_u5 PmLayout_u5 PmEncSpecs_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutL5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmGrow Require Import GrowKit_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmEnc Require Import EncKit_u5 EncAppendK_u5 EncAppendS_u5 EncAppendL_u5.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module EAP.
Import PMES.
Section AppendX.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis LAY : PmLayout.pm0_layout L.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps GK.RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom GK.RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom GK.RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.
Hypothesis OPNEWX : opnew_x_spec L HI.

Lemma defined_long_obj : forall (M : PML.mem) o cap p s, PML.str_at M o (PML.SLong cap p s) -> GK.HULL_HI <= o -> o + 24 <= 2 ^ 64 -> L5.defined M o 24.
Proof.
  intros M o cap p s ((_ & Hw0 & Hw8 & Hw16 & _) & _) Ho H24.
  apply GK.defined_3x8; [exact (GK.defined_of_u64 M o _ Hw0 ltac:(lia) ltac:(lia)) | exact (GK.defined_of_u64 M (o + 8) _ Hw8 ltac:(lia) ltac:(lia))
                          | exact (GK.defined_of_u64 M (o + 16) _ Hw16 ltac:(lia) ltac:(lia))].
Qed.

Theorem str_append_x_ok : str_append_x_spec L HI.
Proof.
  intros LB cr o q sp r rep src. unfold PML.cps_heap.
  intros fx R M model K HH Hmo HKnil Hfp (Hentry & Ha0 & Ha1 & Ha2 & Hsink & Hlive & Hobj & Hbytes & Hsrc & H47 & Hcredit) Hcont.
  destruct Hsink as (Hstr & Hdo & Hrok).
  pose proof Hentry as (_ & _ & _ & _ & Hstk). pose proof (L5C.stk_floor _ _ _ _ Hstk) as FL. pose proof Hobj as (O1 & O2 & O3).
  destruct Hstk as (_ & _ & _ & (T1 & T2) & _). unfold STRX_SCR, PMS.STR_SCR, PMS.OPNEW_SCR, PML.HEAP_STACK in FL.
  assert (N0 : 0 <= len src) by (unfold len; lia).
  destruct rep as [s|cap p s]; cbn [PML.srep_chars rep_live rep_ok] in *.
  - (* [comment removed for export] *)
    pose proof Hstr as (Hl22 & _). assert (S0 : 0 <= len s <= 22) by (unfold len; lia).
    destruct (Z.eq_dec (len src) 0) as [Hz|Hnz].
    { apply (EAS.append_zero_sso_x L HI HIok LAY FPM LB cr o q sp r s src fx R M model K HH Hmo HKnil Hfp); [repeat (split; [assumption|]); assumption|].
      intros fx' R' M' model' LB' cr' LBk W HFP ((s' & Hls & Hs & Hd & HLB & Hcr & HLBk) & HW) HRP HP Hbv HH2.
      apply (Hcont fx' R' M' model' LB' cr' LBk W HFP); [|assumption..]. exists (PML.SShort s'), s'. split; [exact Hls|]. split; [|exact HW]. left.
      split; [cbn [fits]; lia|]. split; [reflexivity|]. split; [split; [exact Hs | split; [exact Hd | exact I]]|]. cbn [lb_drop]. auto. }
    destruct (Z_le_gt_dec (len s + len src) 22) as [Hle|Hgt].
    { apply (EAS.append_sso_x L HI HIok LAY FPM LB cr o q sp r s src fx R M model K HH Hmo HKnil Hfp).
      { split; [split; lia|]. repeat (split; [assumption|]). assumption. }
      intros fx' R' M' model' LB' cr' LBk W HFP ((s' & Hls & Hs & Hd & HLB & Hcr & HLBk) & HW) HRP HP Hbv HH2.
      apply (Hcont fx' R' M' model' LB' cr' LBk W HFP); [|assumption..]. exists (PML.SShort s'), s'. split; [exact Hls|]. split; [|exact HW]. left.
      split; [cbn [fits]; lia|]. split; [reflexivity|]. split; [split; [exact Hs | split; [exact Hd | exact I]]|]. cbn [lb_drop]. auto. }
    assert (HCR : hl_k_per_malloc L <= fst cr) by (apply Hcredit; cbn [fits]; lia).
    assert (GROWN : forall fx' R' M' model' LB' cr' LBk W, PML.fp_ok fx' ->
              (exists p' s', let cap' := PML.grow_cap 23 (len s + len src) in
                 len s' = len s + len src /\ PML.str_at M' o (PML.SLong cap' p' s') /\ L5C.fresh_block L LB M' p' cap' /\
                 LB' = (p', cap') :: LB /\ cr' = debit_k L cr /\ LBk = LB) /\ W = [(o, 24)] ->
              regs_preserved R R' -> L5C.hpres L LBk sp STRX_SCR W M M' -> model_but_vm model model' -> hi_heap HI LB' cr' M' (m_vmmaps model') ->
              srealizes PML.RSEGS SCFG (@PML.cfg fx' R' r M' model') K).
    { intros fx' R' M' model' LB' cr' LBk W HFP ((p' & s' & Hpost) & HW) HRP HP Hbv HH2.
      apply (Hcont fx' R' M' model' LB' cr' LBk W HFP); [|assumption..].
      cbv zeta in Hpost. destruct Hpost as (Hls & Hs & Hfb & HLB & Hcr & HLBk).
      exists (PML.SLong (PML.grow_cap 23 (len s + len src)) p' s'), s'. split; [exact Hls|]. split; [|exact HW]. right.
      split; [cbn [fits]; lia|]. exists p'. cbv zeta. cbn [alloc_of lb_drop]. rewrite Hls.
      split; [reflexivity|].
      assert (G48 : 48 <= PML.grow_cap 23 (len s + len src)).
      { unfold PML.grow_cap. change (2 * (23 - 1)) with 44. rewrite CL5.lor7 by lia.
        pose proof (Z.div_le_mono 44 (Z.max (len s + len src) 44) 8 ltac:(lia) ltac:(lia)) as X. change (44 / 8) with 5 in X. lia. }
      split; [split; [exact Hs | split; [apply (defined_long_obj M' o _ p' _ Hs); unfold GK.HULL_HI; lia | cbn [rep_ok]; exact G48]]|]. auto. }
    destruct (Z_le_gt_dec (len s + len src) 44) as [H44|H45].
    { apply (EAS.append_sso_grow48_x L HI HIok LAY FPM OPNEWX LB cr o q sp r s src fx R M model K HH Hmo HKnil Hfp); [|exact GROWN].
      split; [split; lia|]. repeat (split; [assumption|]). assumption. }
    { apply (EAS.append_sso_growN_x L HI HIok LAY FPM OPNEWX LB cr o q sp r s src fx R M model K HH Hmo HKnil Hfp); [|exact GROWN].
      split; [split; [lia | split; [lia | exact H47]]|]. repeat (split; [assumption|]). assumption. }
  - (* [comment removed for export] *)
    pose proof Hstr as (_ & Hc8 & Hslt). assert (S0 : 0 <= len s < cap) by (unfold len; lia).
    destruct (Z.eq_dec (len src) 0) as [Hz|Hnz].
    { apply (EAL.append_zero_long_x L HI HIok LAY FPM LB cr o q cap p sp r s src fx R M model K HH Hmo HKnil Hfp).
      { split; [split; [exact Hrok | exact Hz]|]. repeat (split; [assumption|]). assumption. }
      intros fx' R' M' model' LB' cr' LBk W HFP ((s' & Hls & Hs & HLB & Hcr & HLBk) & HW) HRP HP Hbv HH2.
      apply (Hcont fx' R' M' model' LB' cr' LBk W HFP); [|assumption..]. exists (PML.SLong cap p s'), s'. split; [exact Hls|]. split; [|exact HW]. left.
      split; [cbn [fits]; lia|]. split; [reflexivity|].
      split; [split; [exact Hs | split; [apply (defined_long_obj M' o cap p _ Hs); unfold GK.HULL_HI; lia | cbn [rep_ok]; exact Hrok]]|]. cbn [lb_drop]. auto. }
    destruct (Z_lt_le_dec (len s + len src) cap) as [Hlt|Hge].
    { apply (EAL.append_fast_x L HI HIok LAY FPM LB cr o q cap p sp r s src fx R M model K HH Hmo HKnil Hfp).
      { split; [split; [exact Hrok | split; [lia | exact Hlt]]|]. repeat (split; [assumption|]). assumption. }
      intros fx' R' M' model' LB' cr' LBk W HFP ((s' & Hls & Hs & HLB & Hcr & HLBk) & HW) HRP HP Hbv HH2.
      apply (Hcont fx' R' M' model' LB' cr' LBk W HFP); [|assumption..]. exists (PML.SLong cap p s'), s'. split; [exact Hls|]. split; [|exact HW]. left.
      split; [cbn [fits]; lia|]. split; [reflexivity|].
      split; [split; [exact Hs | split; [apply (defined_long_obj M' o cap p _ Hs); unfold GK.HULL_HI; lia | cbn [rep_ok]; exact Hrok]]|]. cbn [lb_drop]. auto. }
    assert (HCR : hl_k_per_malloc L <= fst cr) by (apply Hcredit; cbn [fits]; lia).
    assert (GROWN : forall fx' R' M' model' LB' cr' LBk W, PML.fp_ok fx' ->
              (exists p' s', let cap' := PML.grow_cap cap (len s + len src) in
                 len s' = len s + len src /\ PML.str_at M' o (PML.SLong cap' p' s') /\ L5C.fresh_block L LB M' p' cap' /\
                 LB' = (p', cap') :: lb_remove p LB /\ cr' = debit_k L cr /\ LBk = lb_remove p LB) /\ W = [(o, 24)] ->
              regs_preserved R R' -> L5C.hpres L LBk sp STRX_SCR W M M' -> model_but_vm model model' -> hi_heap HI LB' cr' M' (m_vmmaps model') ->
              srealizes PML.RSEGS SCFG (@PML.cfg fx' R' r M' model') K).
    { intros fx' R' M' model' LB' cr' LBk W HFP ((p' & s' & Hpost) & HW) HRP HP Hbv HH2.
      apply (Hcont fx' R' M' model' LB' cr' LBk W HFP); [|assumption..].
      cbv zeta in Hpost. destruct Hpost as (Hls & Hs & Hfb & HLB & Hcr & HLBk).
      exists (PML.SLong (PML.grow_cap cap (len s + len src)) p' s'), s'. split; [exact Hls|]. split; [|exact HW]. right.
      split; [cbn [fits]; lia|]. exists p'. cbv zeta. cbn [alloc_of lb_drop]. rewrite Hls.
      split; [reflexivity|].
      destruct (EK.grow_cap_ge cap (len s + len src) ltac:(lia) Hc8 ltac:(lia)) as (G1 & G2 & G3).
      split; [split; [exact Hs | split; [apply (defined_long_obj M' o _ p' _ Hs); unfold GK.HULL_HI; lia | cbn [rep_ok]; lia]]|]. auto. }
    destruct (Z_le_gt_dec (len s + len src) (2 * cap - 2)) as [H2|HN].
    { apply (EAL.append_grow2_x L HI HIok LAY FPM OPNEWX LB cr o q cap p sp r s src fx R M model K HH Hmo HKnil Hfp); [|exact GROWN].
      split; [split; [exact Hrok | split; [lia | split; [lia | exact H47]]]|]. repeat (split; [assumption|]). assumption. }
    { apply (EAL.append_growN_x L HI HIok LAY FPM OPNEWX LB cr o q cap p sp r s src fx R M model K HH Hmo HKnil Hfp); [|exact GROWN].
      split; [split; [exact Hrok | split; [lia | split; [lia | exact H47]]]|]. repeat (split; [assumption|]). assumption. }
Qed.
End AppendX.
End EAP.
Print Assumptions EAP.str_append_x_ok.
