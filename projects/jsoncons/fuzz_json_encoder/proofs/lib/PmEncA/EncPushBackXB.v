(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface HeapIfaceA L5Defs L5Core L5LazyA Pm5PlanKit Pm5L5DefsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmHeapIfaceA IcptIfaceA PmIcptIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm5CutKit CutHeap2 CutL5 CutAutoX CutCertA CutHeapA CutAutoXA CutL5A CutBridgeA CutRtCpsA CutRtA CutRtB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmLibDefs PmLibSpecs PmEncSpecs PmLibDefsA PmLibSpecsA PmEncSpecsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmEncA Require Import EncKitXB EncMemXB EncPushBackSXB EncPushBackLXB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module EPBA.
Import PMES.
Section PushBackX.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable HI : asan_iface.
Hypothesis HIok : PmHeapIfaceA.asan_iface_ok L ar C SCFG HI.
Hypothesis LAY : L5A.as0_layout L C.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps Pm5PlanKit.RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Pm5PlanKit.RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom Pm5PlanKit.RSEGS)) -> PMSA.fp_ok fx -> PMSA.fp_ok fx'.
Hypothesis KPM : 0 <= hl_k_per_malloc L.
Hypothesis BLIN : 0 <= hl_b_lin L.
Hypothesis BOV : 0 <= hl_b_overhead L.
Variable CL : Z.
Variable onmax : Z.
Hypothesis CLOK : EKA.clok CL onmax.
Hypothesis OPNEW_OK : PMESA.opnew_x_specA L ar HI onmax EPLA.PC_OPNEW.
Hypothesis OPDEL_OK : PMSA.opdel_specA L ar HI EPLA.PC_OPDEL.
Hypothesis MEMMOVE_LIBC : PMESA.amemcpy_x_spec_at L ar HI onmax EPLA.PC_MM false.

Theorem str_push_back_x_ok : PMESA.str_push_back_x_specA L ar HI CL 1056004.
Proof.
  intros LB FF LK cr A o c sp r kx bx rep. unfold PMSA.cps_asan.
  intros fx R M model K HH Hmo HKnil Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs (Ha0 & Ha1 & Hc & Hsink & Hlive & Hobj & Hstksh & Hcredit & Hroom2) Hcont.
  pose proof (EKA.rep_shape_of_sink L M o rep Hsink) as SH. destruct Hsink as (Hstr & Hdo & Hrok & Hsh).
  pose proof CLOK as (C1 & C2 & C3 & C4).
  assert (LENA : forall s : list Z, len (s ++ [c]) = len s + 1) by (intros s0; unfold len; rewrite length_app, Nat2Z.inj_add; reflexivity).
  assert (DEFO : forall LBx LKx crx Ax (Mx : PMSA.mem) Vx, ri_inv HI LBx FF LKx crx Ax Mx Vx -> L5.defined Mx o 24).
  { intros LBx LKx crx Ax Mx Vx HHx. destruct Hobj as ((f & Hf & F1 & F2) & _ & _). destruct (CHA.wf_frm _ _ _ _ _ _ _ _ (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HHx) f Hf) as (_ & _ & _ & _ & FD & _).
    intros q Hq. replace (o + q) with (ff_addr f + (o + q - ff_addr f)) by lia. apply FD. lia. }
  destruct rep as [s|cap p s]; cbn [PML.srep_chars rep_live rep_ok PMLA.srep_sh] in *.
  - (* [comment removed for export] *)
    pose proof Hstr as (Hl22 & _).
    destruct (Z_le_gt_dec (len s) 21) as [Hle|Hgt].
    + apply (push_back_sso_x L ar C HI HIok LAY FPM LB FF LK cr A o c sp r s fx R M model K HH Hmo HKnil Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs); [repeat (split; [assumption|]); assumption|].
      intros fx' R' M' model' LB' cr' LBk W LK' A' HFP (Hs & Hd & HLB & Hcr & HLBk & HW) HRP HP Hrt HA' Hmo' HLK' HH2. subst LB' cr' LBk.
      apply (Hcont fx' R' M' model' LB cr LB W LK' A' HFP); [|assumption..]. exists (PML.SShort (s ++ [c])). split; [|split; [exact (EKA.grown_scredit_same L CL cr (PML.SShort s) (s ++ [c]) kx bx Hcredit) | exact HW]].
      left. split; [cbn [fits]; rewrite LENA; lia|]. split; [reflexivity|]. split; [split; [exact Hs | split; [exact Hd | split; [exact I | exact I]]]|]. cbn [lb_drop]. auto.
    + assert (H22 : Z.of_nat (length s) = 22) by (unfold len in Hgt; lia).
      destruct (EKA.scredit_grow_ok L CL onmax KPM BLIN BOV cr (PML.SShort s) kx bx (len s + 1) CLOK Hcredit I ltac:(unfold len; lia) Hroom2 ltac:(cbn [fits]; unfold len; lia)) as [HC HO].
      cbn [alloc_of] in HC, HO. unfold len in HC, HO. rewrite H22 in HC, HO. change (PML.grow_cap 23 (22 + 1)) with 48 in HC, HO.
      apply (push_back_sso_full_x L ar C HI HIok LAY FPM onmax OPNEW_OK MEMMOVE_LIBC LB FF LK cr A o c sp r s fx R M model K HH Hmo HKnil Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs).
      { split; [exact H22|]. repeat (split; [assumption|]). exact HC. }
      intros fx' R' M' model' LB' cr' LBk W LK' A' HFP (p & Hs & Hfr & HLB & Hcr & HLBk & HW) HRP HP Hrt HA' Hmo' HLK' HH2. subst LB' cr' LBk.
      apply (Hcont fx' R' M' model' ((p, 48) :: LB) (adebit L cr 48) LB W LK' A' HFP); [|assumption..]. exists (PML.SLong 48 p (s ++ [c])).
      pose proof (EKA.grown_scredit_grow L CL KPM BLIN BOV cr (PML.SShort s) (len s + 1) p (s ++ [c]) kx bx I ltac:(cbn [fits]; unfold len; lia) ltac:(unfold len; lia) Hroom2) as HG.
      cbn [alloc_of] in HG. unfold len in HG. rewrite H22 in HG. change (PML.grow_cap 23 (22 + 1)) with 48 in HG.
      split; [|split; [exact (HG ltac:(lia) Hcredit) | exact HW]].
      right. split; [cbn [fits]; rewrite LENA; unfold len; lia|]. exists p. cbv zeta. cbn [alloc_of lb_drop]. rewrite LENA. unfold len. rewrite H22.
      change (PML.grow_cap 23 (22 + 1)) with 48. pose proof Hfr as (_ & _ & _ & Hdf & Hsb).
      split; [reflexivity|]. split; [split; [exact Hs | split; [| split; [cbn [rep_ok]; lia | exact Hsb]]]|]; [|auto].
      exact (DEFO _ _ _ _ _ _ HH2).
  - (* [comment removed for export] *)
    pose proof Hstr as (_ & Hc8 & Hslt). destruct SH as [H48 _].
    destruct (Z_lt_le_dec (len s + 1) cap) as [Hlt|Hge].
    + apply (push_back_fast_x L ar C HI HIok LAY FPM LB FF LK cr A o cap p c sp r s fx R M model K HH Hmo HKnil Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs).
      { split; [exact Hlt|]. repeat (split; [first [assumption | lia]|]). unfold len in *. lia. }
      intros fx' R' M' model' LB' cr' LBk W LK' A' HFP (Hs & Hsb & HLB & Hcr & HLBk & HW) HRP HP Hrt HA' Hmo' HLK' HH2. subst LB' cr' LBk.
      apply (Hcont fx' R' M' model' LB cr (lb_remove p LB) W LK' A' HFP); [|assumption..]. exists (PML.SLong cap p (s ++ [c])).
      split; [|split; [exact (EKA.grown_scredit_same L CL cr (PML.SLong cap p s) (s ++ [c]) kx bx Hcredit) | exact HW]].
      left. split; [cbn [fits]; rewrite LENA; exact Hlt|]. split; [reflexivity|].
      split; [split; [exact Hs | split; [| split; [cbn [rep_ok]; exact Hrok | exact Hsb]]]|]; [|cbn [lb_drop]; auto].
      exact (DEFO _ _ _ _ _ _ HH2).
    + assert (Heq : Z.of_nat (length s) + 1 = cap) by (unfold len in Hge; lia).
      destruct (EKA.scredit_grow_ok L CL onmax KPM BLIN BOV cr (PML.SLong cap p s) kx bx (len s + 1) CLOK Hcredit (conj H48 Hc8) ltac:(unfold len; lia) Hroom2 ltac:(cbn [fits]; unfold len; lia)) as [HC HO].
      cbn [alloc_of] in HC, HO. unfold len in HC, HO.
      destruct (EKA.grow_cap_ge cap (Z.of_nat (length s) + 1) ltac:(lia) Hc8 ltac:(lia)) as (G1 & G2 & G3).
      apply (push_back_grow_x L ar C HI HIok LAY FPM CL onmax CLOK OPNEW_OK OPDEL_OK MEMMOVE_LIBC LB FF LK cr A o cap p c sp r s fx R M model K HH Hmo HKnil Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs).
      { split; [exact Heq|]. repeat (split; [first [assumption | lia]|]). exact HC. }
      intros fx' R' M' model' LB' cr' LBk W LK' A' HFP (p' & Hpost) HRP HP Hrt HA' Hmo' HLK' HH2.
      cbv zeta in Hpost. destruct Hpost as (Hs & Hfr & HLB & Hcr & HLBk & HW). subst LB' cr' LBk.
      eapply (Hcont fx' R' M' model' _ _ (lb_remove p LB) W LK' A' HFP); [| exact HRP | exact HP | exact Hrt | exact HA' | exact Hmo' | exact HLK' | exact HH2].
      exists (PML.SLong (PML.grow_cap cap (Z.of_nat (length (s ++ [c])))) p' (s ++ [c])).
      pose proof (EKA.grown_scredit_grow L CL KPM BLIN BOV cr (PML.SLong cap p s) (len s + 1) p' (s ++ [c]) kx bx (conj H48 Hc8) ltac:(cbn [fits]; unfold len; lia) ltac:(unfold len; lia) Hroom2) as HG.
      cbn [alloc_of] in HG. unfold len in HG. fold (len (s ++ [c])). rewrite LENA. unfold len.
      split; [|split; [exact (HG ltac:(lia) Hcredit) | exact HW]].
      right. rewrite LENA. unfold len. split; [cbn [fits]; lia|]. exists p'. cbv zeta. cbn [alloc_of lb_drop]. pose proof Hfr as (_ & _ & _ & Hdf & Hsb).
      split; [reflexivity|]. split; [split; [exact Hs | split; [| split; [cbn [rep_ok]; lia | exact Hsb]]]|]; [|auto].
      exact (DEFO _ _ _ _ _ _ HH2).
Qed.
End PushBackX.
End EPBA.
Print Assumptions EPBA.str_push_back_x_ok.
