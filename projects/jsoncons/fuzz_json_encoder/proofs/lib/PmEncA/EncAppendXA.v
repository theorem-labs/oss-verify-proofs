(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface HeapIfaceA L5Defs L5Core L5LazyA Pm4PlanKit Pm4L5DefsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmHeapIfaceA IcptIfaceA PmIcptIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm4CutKit CutHeap2 CutL5 CutAutoX CutCertA CutHeapA CutAutoXA CutL5A CutBridgeA CutRtCpsA CutRtA CutRtB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmLibDefs PmLibSpecs PmEncSpecs PmLibDefsA PmLibSpecsA PmEncSpecsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmEncA Require Import EncKitA EncMemA EncAppendKXA EncAppendSXA EncAppendLXA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module EAPA.
Import PMES.
Definition PC_APPEND : Z := 1040708.   (* [comment removed for export] *)
Section AppendX.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable HI : asan_iface.
Hypothesis HIok : PmHeapIfaceA.asan_iface_ok L ar C SCFG HI.
Hypothesis LAY : L5A.as0_layout L C.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps Pm4PlanKit.RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Pm4PlanKit.RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom Pm4PlanKit.RSEGS)) -> PMSA.fp_ok fx -> PMSA.fp_ok fx'.
Hypothesis KPM : 0 <= hl_k_per_malloc L.
Hypothesis BLIN : 0 <= hl_b_lin L.
Hypothesis BOV : 0 <= hl_b_overhead L.
Variable CL : Z.
Variable onmax : Z.
Hypothesis CLOK : EKA.clok CL onmax.
Hypothesis OPNEW_OK : PMESA.opnew_x_specA L ar HI onmax EALA.PC_OPNEW.
Hypothesis OPDEL_OK : PMSA.opdel_specA L ar HI EALA.PC_OPDEL.
Hypothesis MEMMOVE_LIBC : PMESA.amemcpy_x_spec_at L ar HI onmax EALA.PC_MM false.
Hypothesis MEMCPY_LIBC : PMESA.amemcpy_x_spec_at L ar HI onmax EALA.PC_MC false.

Theorem str_append_x_ok : PMESA.str_append_x_specA L ar HI PMLA.C_xasan CL PC_APPEND.
Proof.
  intros LB FF LK cr A o q sp r kx bx rep src. unfold PMSA.cps_asan.
  intros fx R M model K HH Hmo HKnil Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs (Ha0 & Ha1 & Ha2 & Hsink & Hlive & Hobj & Hstksh & Hbytes & Hsrc & Hcredit & Hroom2) Hcont.
  pose proof (EKA.rep_shape_of_sink L M o rep Hsink) as SH. destruct Hsink as (Hstr & Hdo & Hrok & Hsh).
  pose proof CLOK as (C1 & C2 & C3 & C4).
  assert (IMG_RO_ok : forall a, PMLA.IMG_RO_LO PMLA.C_xasan <= a < PMLA.IMG_RO_HI PMLA.C_xasan -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_rt_static L a).
  { intros a Ha. cbn [PMLA.IMG_RO_LO PMLA.IMG_RO_HI PMLA.C_xasan] in Ha. rewrite (L5A.aly_img_lo L C LAY), (L5A.aly_img_hi L C LAY). split; [clear - Ha; lia|].
    intros Hs; pose proof (L5A.aly_static_lo L C LAY a Hs); clear - Ha H; lia. }
  pose proof (CHA.rng_of_wf _ _ _ _ _ _ _ _ (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH)) as RFx.
  assert (LENA : len (PML.srep_chars rep ++ src) = len (PML.srep_chars rep) + len src) by (unfold len; rewrite length_app, Nat2Z.inj_add; reflexivity).
  assert (LEN0 : forall s : list Z, len s = 0 -> s = []) by (intros [|x s0] Hs0; [reflexivity | exfalso; unfold len in Hs0; cbn [length] in Hs0; lia]).
  assert (DEFO : forall LBx LKx crx Ax (Mx : PMSA.mem) Vx, ri_inv HI LBx FF LKx crx Ax Mx Vx -> L5.defined Mx o 24).
  { intros LBx LKx crx Ax Mx Vx HHx. destruct Hobj as ((f & Hf & F1 & F2) & _ & _). destruct (CHA.wf_frm _ _ _ _ _ _ _ _ (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HHx) f Hf) as (_ & _ & _ & _ & FD & _).
    intros q0 Hq. replace (o + q0) with (ff_addr f + (o + q0 - ff_addr f)) by lia. apply FD. lia. }
  (* [comment removed for export] *)
  destruct (Z.eq_dec (len src) 0) as [Hn0|Hn0].
  { (* [comment removed for export] *)
    pose proof (LEN0 src Hn0) as ->. rewrite Hn0 in Ha2.
    destruct rep as [s|cap p s]; cbn [PML.srep_chars rep_live rep_ok PMLA.srep_sh] in *.
    - apply (EncAppendSXA.append_zero_sso_x L ar C HI HIok LAY FPM LB FF LK cr A o sp r s fx R M model K HH Hmo HKnil Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs); [repeat (split; [assumption|]); assumption|].
      intros fx' R' M' model' LB' cr' LBk W LK' A' HFP (Hs & Hd & HLB & Hcr & HLBk & HW) HRP HP Hrt HA' Hmo' HLK' HH2. subst LB' cr' LBk.
      apply (Hcont fx' R' M' model' LB cr LB W LK' A' HFP); [|assumption..]. exists (PML.SShort s), s. rewrite app_nil_r in *.
      split; [unfold len; cbn [length]; lia|]. split; [|split; [exact (EKA.grown_scredit_same L CL cr (PML.SShort s) s kx bx Hcredit) | exact HW]].
      left. pose proof Hstr as (Hl22 & _). split; [cbn [fits]; unfold len; lia|]. split; [reflexivity|]. split; [split; [exact Hs | split; [exact Hd | split; [exact I | exact I]]]|]. cbn [lb_drop]. auto.
    - pose proof Hstr as (_ & Hc8 & Hslt). destruct SH as [H48 _].
      apply (EncAppendLXA.append_zero_x L ar C HI HIok LAY FPM CL onmax CLOK LB FF LK cr A o cap p sp r s fx R M model K HH Hmo HKnil Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs).
      { repeat (split; [first [assumption | lia]|]). unfold len in *. lia. }
      intros fx' R' M' model' LB' cr' LBk W LK' A' HFP (Hs & Hsb & HLB & Hcr & HLBk & HW) HRP HP Hrt HA' Hmo' HLK' HH2. subst LB' cr' LBk.
      apply (Hcont fx' R' M' model' LB cr (lb_remove p LB) W LK' A' HFP); [|assumption..]. exists (PML.SLong cap p s), s. rewrite app_nil_r in *.
      split; [unfold len; cbn [length]; lia|]. split; [|split; [exact (EKA.grown_scredit_same L CL cr (PML.SLong cap p s) s kx bx Hcredit) | exact HW]].
      left. split; [cbn [fits]; unfold len in *; lia|]. split; [reflexivity|].
      split; [split; [exact Hs | split; [| split; [cbn [rep_ok]; exact Hrok | exact Hsb]]]|]; [|cbn [lb_drop]; auto]. exact (DEFO _ _ _ _ _ _ HH2). }
  assert (Hn1 : 1 <= len src) by (unfold len in *; lia).
  assert (INCLd : incl (lb_drop rep LB) LB) by (destruct rep as [s|cap p s]; cbn [lb_drop]; [apply incl_refl | intros y Hy; exact (L5C.in_lb_remove p y LB Hy)]).
  pose proof (EAKA.srcK_intro L ar HI PMLA.C_xasan M LB (lb_drop rep LB) FF sp o rep q src RFx INCLd eq_refl Hn1 Hbytes Hsrc) as SRC.
  destruct rep as [s|cap p s]; cbn [PML.srep_chars rep_live rep_ok PMLA.srep_sh lb_drop alloc_of] in *.
  - (* [comment removed for export] *)
    pose proof Hstr as (Hl22 & _).
    destruct (Z_le_gt_dec (len s + len src) 22) as [Hle|Hgt].
    + (* [comment removed for export] *)
      apply (EncAppendSXA.append_sso_x L ar C HI HIok LAY FPM PMLA.C_xasan IMG_RO_ok CL onmax CLOK MEMMOVE_LIBC LB FF LK cr A o q sp r s src fx R M model K HH Hmo HKnil Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs).
      { split; [exact Hn1|]. split; [exact Hle|]. repeat (split; [assumption|]). exact Hroom2. }
      intros fx' R' M' model' LB' cr' LBk W LK' A' HFP (Hs & Hd & HLB & Hcr & HLBk & HW) HRP HP Hrt HA' Hmo' HLK' HH2. subst LB' cr' LBk.
      apply (Hcont fx' R' M' model' LB cr LB W LK' A' HFP); [|assumption..]. exists (PML.SShort (s ++ src)), (s ++ src).
      split; [exact LENA|]. split; [|split; [exact (EKA.grown_scredit_same L CL cr (PML.SShort s) (s ++ src) kx bx Hcredit) | exact HW]].
      left. split; [cbn [fits]; rewrite LENA; exact Hle|]. split; [reflexivity|]. split; [split; [exact Hs | split; [exact Hd | split; [exact I | exact I]]]|]. cbn [lb_drop]. auto.
    + (* [comment removed for export] *)
      destruct (EKA.scredit_grow_ok L CL onmax KPM BLIN BOV cr (PML.SShort s) kx bx (len s + len src) CLOK Hcredit I ltac:(unfold len; lia) Hroom2 ltac:(cbn [fits]; lia)) as [HC HO].
      cbn [alloc_of] in HC, HO.
      pose proof (EKA.grown_scredit_grow L CL KPM BLIN BOV cr (PML.SShort s) (len s + len src)) as HG. cbn [alloc_of fits] in HG.
      destruct (Z_le_gt_dec (len s + len src) 44) as [H44|H45].
      * apply (EncAppendSXA.append_sso_grow48_x L ar C HI HIok LAY FPM PMLA.C_xasan IMG_RO_ok CL onmax CLOK OPNEW_OK MEMMOVE_LIBC MEMCPY_LIBC LB FF LK cr A o q sp r s src fx R M model K HH Hmo HKnil Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs).
        { split; [exact Hn1|]. split; [unfold len in *; lia|]. repeat (split; [assumption|]). exact HC. }
        intros fx' R' M' model' LB' cr' LBk W LK' A' HFP (p' & Hpost) HRP HP Hrt HA' Hmo' HLK' HH2.
        cbv zeta in Hpost. destruct Hpost as (Hs & Hfr & HLB & Hcr & HLBk & HW). subst LB' cr' LBk.
        eapply (Hcont fx' R' M' model' _ _ LB W LK' A' HFP); [| exact HRP | exact HP | exact Hrt | exact HA' | exact Hmo' | exact HLK' | exact HH2].
        exists (PML.SLong (PML.grow_cap 23 (len (s ++ src))) p' (s ++ src)), (s ++ src). split; [exact LENA|].
        split; [|split; [rewrite LENA; exact (HG p' (s ++ src) kx bx I ltac:(lia) ltac:(unfold len; lia) Hroom2 ltac:(unfold len in *; lia) Hcredit) | exact HW]].
        right. split; [cbn [fits]; rewrite LENA; unfold len in *; lia|]. exists p'. cbv zeta. cbn [alloc_of lb_drop]. split; [reflexivity|].
        rewrite LENA. unfold len. pose proof Hfr as (_ & _ & _ & Hdf & Hsb). destruct (EKA.grow_cap_short (Z.of_nat (length s) + Z.of_nat (length src)) ltac:(lia)) as (G1 & G2 & G3).
        split; [split; [exact Hs | split; [| split; [cbn [rep_ok]; lia | exact Hsb]]]|]; [|auto]. exact (DEFO _ _ _ _ _ _ HH2).
      * apply (EncAppendSXA.append_sso_growN_x L ar C HI HIok LAY FPM PMLA.C_xasan IMG_RO_ok CL onmax CLOK OPNEW_OK MEMMOVE_LIBC MEMCPY_LIBC LB FF LK cr A o q sp r s src fx R M model K HH Hmo HKnil Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs).
        { split; [exact Hn1|]. split; [unfold len in *; lia|]. repeat (split; [assumption|]). exact HC. }
        intros fx' R' M' model' LB' cr' LBk W LK' A' HFP (p' & Hpost) HRP HP Hrt HA' Hmo' HLK' HH2.
        cbv zeta in Hpost. destruct Hpost as (Hs & Hfr & HLB & Hcr & HLBk & HW). subst LB' cr' LBk.
        eapply (Hcont fx' R' M' model' _ _ LB W LK' A' HFP); [| exact HRP | exact HP | exact Hrt | exact HA' | exact Hmo' | exact HLK' | exact HH2].
        exists (PML.SLong (PML.grow_cap 23 (len (s ++ src))) p' (s ++ src)), (s ++ src). split; [exact LENA|].
        split; [|split; [rewrite LENA; exact (HG p' (s ++ src) kx bx I ltac:(lia) ltac:(unfold len; lia) Hroom2 ltac:(unfold len in *; lia) Hcredit) | exact HW]].
        right. split; [cbn [fits]; rewrite LENA; unfold len in *; lia|]. exists p'. cbv zeta. cbn [alloc_of lb_drop]. split; [reflexivity|].
        rewrite LENA. unfold len. pose proof Hfr as (_ & _ & _ & Hdf & Hsb). destruct (EKA.grow_cap_short (Z.of_nat (length s) + Z.of_nat (length src)) ltac:(lia)) as (G1 & G2 & G3).
        split; [split; [exact Hs | split; [| split; [cbn [rep_ok]; lia | exact Hsb]]]|]; [|auto]. exact (DEFO _ _ _ _ _ _ HH2).
  - (* [comment removed for export] *)
    pose proof Hstr as (_ & Hc8 & Hslt). destruct SH as [H48 _].
    destruct (Z_lt_le_dec (len s + len src) cap) as [Hlt|Hge].
    + (* [comment removed for export] *)
      apply (EncAppendLXA.append_fast_x L ar C HI HIok LAY FPM PMLA.C_xasan IMG_RO_ok CL onmax CLOK MEMMOVE_LIBC LB FF LK cr A o cap p q sp r s src fx R M model K HH Hmo HKnil Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs).
      { split; [exact Hn1|]. split; [exact Hlt|]. repeat (split; [first [assumption | lia]|]). exact Hroom2. }
      intros fx' R' M' model' LB' cr' LBk W LK' A' HFP (Hs & Hsb & HLB & Hcr & HLBk & HW) HRP HP Hrt HA' Hmo' HLK' HH2. subst LB' cr' LBk.
      apply (Hcont fx' R' M' model' LB cr (lb_remove p LB) W LK' A' HFP); [|assumption..]. exists (PML.SLong cap p (s ++ src)), (s ++ src).
      split; [exact LENA|]. split; [|split; [exact (EKA.grown_scredit_same L CL cr (PML.SLong cap p s) (s ++ src) kx bx Hcredit) | exact HW]].
      left. split; [cbn [fits]; rewrite LENA; exact Hlt|]. split; [reflexivity|].
      split; [split; [exact Hs | split; [| split; [cbn [rep_ok]; exact Hrok | exact Hsb]]]|]; [|cbn [lb_drop]; auto]. exact (DEFO _ _ _ _ _ _ HH2).
    + (* [comment removed for export] *)
      destruct (EKA.scredit_grow_ok L CL onmax KPM BLIN BOV cr (PML.SLong cap p s) kx bx (len s + len src) CLOK Hcredit (conj H48 Hc8) ltac:(unfold len; lia) Hroom2 ltac:(cbn [fits]; lia)) as [HC HO].
      cbn [alloc_of] in HC, HO.
      pose proof (EKA.grown_scredit_grow L CL KPM BLIN BOV cr (PML.SLong cap p s) (len s + len src)) as HG. cbn [alloc_of fits] in HG.
      destruct (EKA.grow_cap_ge cap (len s + len src) ltac:(lia) Hc8 ltac:(lia)) as (G1 & G2 & G3).
      destruct (Z_le_gt_dec (len s + len src) (2 * cap - 2)) as [H2c|H2c].
      * apply (EncAppendLXA.append_grow2_x L ar C HI HIok LAY FPM PMLA.C_xasan IMG_RO_ok CL onmax CLOK OPNEW_OK OPDEL_OK MEMMOVE_LIBC MEMCPY_LIBC LB FF LK cr A o cap p q sp r s src fx R M model K HH Hmo HKnil Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs).
        { split; [exact Hn1|]. split; [unfold len in *; lia|]. repeat (split; [first [assumption | lia]|]). exact HC. }
        intros fx' R' M' model' LB' cr' LBk W LK' A' HFP (p' & Hpost) HRP HP Hrt HA' Hmo' HLK' HH2.
        cbv zeta in Hpost. destruct Hpost as (Hs & Hfr & HLB & Hcr & HLBk & HW). subst LB' cr' LBk.
        eapply (Hcont fx' R' M' model' _ _ (lb_remove p LB) W LK' A' HFP); [| exact HRP | exact HP | exact Hrt | exact HA' | exact Hmo' | exact HLK' | exact HH2].
        exists (PML.SLong (PML.grow_cap cap (len (s ++ src))) p' (s ++ src)), (s ++ src). split; [exact LENA|].
        split; [|split; [rewrite LENA; exact (HG p' (s ++ src) kx bx (conj H48 Hc8) ltac:(lia) ltac:(unfold len; lia) Hroom2 ltac:(unfold len in *; lia) Hcredit) | exact HW]].
        right. split; [cbn [fits]; rewrite LENA; unfold len in *; lia|]. exists p'. cbv zeta. cbn [alloc_of lb_drop]. split; [reflexivity|].
        rewrite LENA. unfold len. pose proof Hfr as (_ & _ & _ & Hdf & Hsb).
        split; [split; [exact Hs | split; [| split; [cbn [rep_ok]; unfold len in *; lia | exact Hsb]]]|]; [|auto]. exact (DEFO _ _ _ _ _ _ HH2).
      * apply (EncAppendLXA.append_growN_x L ar C HI HIok LAY FPM PMLA.C_xasan IMG_RO_ok CL onmax CLOK OPNEW_OK OPDEL_OK MEMMOVE_LIBC MEMCPY_LIBC LB FF LK cr A o cap p q sp r s src fx R M model K HH Hmo HKnil Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs).
        { split; [exact Hn1|]. split; [unfold len in *; lia|]. repeat (split; [first [assumption | lia]|]). exact HC. }
        intros fx' R' M' model' LB' cr' LBk W LK' A' HFP (p' & Hpost) HRP HP Hrt HA' Hmo' HLK' HH2.
        cbv zeta in Hpost. destruct Hpost as (Hs & Hfr & HLB & Hcr & HLBk & HW). subst LB' cr' LBk.
        eapply (Hcont fx' R' M' model' _ _ (lb_remove p LB) W LK' A' HFP); [| exact HRP | exact HP | exact Hrt | exact HA' | exact Hmo' | exact HLK' | exact HH2].
        exists (PML.SLong (PML.grow_cap cap (len (s ++ src))) p' (s ++ src)), (s ++ src). split; [exact LENA|].
        split; [|split; [rewrite LENA; exact (HG p' (s ++ src) kx bx (conj H48 Hc8) ltac:(lia) ltac:(unfold len; lia) Hroom2 ltac:(unfold len in *; lia) Hcredit) | exact HW]].
        right. split; [cbn [fits]; rewrite LENA; unfold len in *; lia|]. exists p'. cbv zeta. cbn [alloc_of lb_drop]. split; [reflexivity|].
        rewrite LENA. unfold len. pose proof Hfr as (_ & _ & _ & Hdf & Hsb).
        split; [split; [exact Hs | split; [| split; [cbn [rep_ok]; unfold len in *; lia | exact Hsb]]]|]; [|auto]. exact (DEFO _ _ _ _ _ _ HH2).
Qed.
End AppendX.
End EAPA.
Print Assumptions EAPA.str_append_x_ok.
