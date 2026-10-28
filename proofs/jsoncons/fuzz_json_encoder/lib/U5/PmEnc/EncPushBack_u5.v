(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import PmLibDefs_u5 PmLibSpecs_u5 PmLayout_u5 PmEncSpecs_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmGrow Require Import GrowKit_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmEnc Require Import EncKit_u5 EncPushBackS_u5 EncPushBackL_u5.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module EPB.
Import PMES.
Section PushBackX.
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

Theorem str_push_back_x_ok : str_push_back_x_spec L HI.
Proof.
  intros LB cr o c sp r rep. unfold PML.cps_heap.
  intros fx R M model K HH Hmo HKnil Hfp (Hentry & Ha0 & Ha1 & Hc & Hsink & Hlive & Hobj & Hcredit) Hcont.
  destruct Hsink as (Hstr & Hdo & Hrok).
  pose proof Hentry as (_ & _ & _ & _ & Hstk). pose proof (L5C.stk_floor _ _ _ _ Hstk) as FL. pose proof Hobj as (O1 & O2 & O3).
  destruct Hstk as (_ & _ & _ & (T1 & T2) & _). unfold STRX_SCR, PMS.STR_SCR, PMS.OPNEW_SCR, PML.HEAP_STACK in FL.
  assert (LENA : forall s : list Z, len (s ++ [c]) = len s + 1) by (intros s0; unfold len; rewrite length_app, Nat2Z.inj_add; reflexivity).
  destruct rep as [s|cap p s]; cbn [PML.srep_chars rep_live rep_ok] in *.
  - (* [comment removed for export] *)
    pose proof Hstr as (Hl22 & _).
    destruct (Z_le_gt_dec (len s) 21) as [Hle|Hgt].
    + apply (EPS.push_back_sso_in_x L HI HIok LAY FPM LB cr o c sp r s fx R M model K HH Hmo HKnil Hfp); [repeat (split; [assumption|]); assumption|].
      intros fx' R' M' model' LB' cr' LBk W HFP ((Hs & Hd & HLB & Hcr & HLBk) & HW) HRP HP Hbv HH2.
      apply (Hcont fx' R' M' model' LB' cr' LBk W HFP); [|assumption..]. exists (PML.SShort (s ++ [c])). split; [|exact HW]. left.
      split; [cbn [fits]; rewrite LENA; lia|]. split; [reflexivity|]. split; [split; [exact Hs | split; [exact Hd | exact I]]|]. cbn [lb_drop]. auto.
    + assert (H22 : Z.of_nat (length s) = 22) by (unfold len in Hgt; lia).
      apply (EPS.push_back_sso_full_x L HI HIok LAY FPM OPNEWX LB cr o c sp r s fx R M model K HH Hmo HKnil Hfp).
      { split; [exact H22|]. repeat (split; [assumption|]). apply Hcredit. cbn [fits]. unfold len. lia. }
      intros fx' R' M' model' LB' cr' LBk W HFP ((p & Hs & Hd & Hfb & HLB & Hcr & HLBk) & HW) HRP HP Hbv HH2.
      apply (Hcont fx' R' M' model' LB' cr' LBk W HFP); [|assumption..]. exists (PML.SLong 48 p (s ++ [c])). split; [|exact HW]. right.
      split; [cbn [fits]; rewrite LENA; unfold len; lia|]. exists p. cbv zeta. cbn [alloc_of lb_drop]. rewrite LENA. unfold len. rewrite H22.
      change (PML.grow_cap 23 (22 + 1)) with 48.
      split; [reflexivity|]. split; [split; [exact Hs | split; [exact Hd | cbn [rep_ok]; lia]]|]. auto.
  - (* [comment removed for export] *)
    pose proof Hstr as (_ & Hc8 & Hslt).
    destruct (Z_lt_le_dec (len s + 1) cap) as [Hlt|Hge].
    + apply (EPL.push_back_fast_x L HI HIok LAY FPM LB cr o cap p c sp r s fx R M model K HH Hmo HKnil Hfp).
      { split; [split; [lia | exact Hlt]|]. repeat (split; [assumption|]). assumption. }
      intros fx' R' M' model' LB' cr' LBk W HFP ((Hs & HLB & Hcr & HLBk) & HW) HRP HP Hbv HH2.
      apply (Hcont fx' R' M' model' LB' cr' LBk W HFP); [|assumption..]. exists (PML.SLong cap p (s ++ [c])). split; [|exact HW]. left.
      split; [cbn [fits]; rewrite LENA; exact Hlt|]. split; [reflexivity|].
      split; [split; [exact Hs | split; [apply (defined_long_obj M' o cap p _ Hs); unfold GK.HULL_HI; lia | cbn [rep_ok]; exact Hrok]]|]. cbn [lb_drop]. auto.
    + assert (Heq : Z.of_nat (length s) + 1 = cap) by (unfold len in Hge; lia).
      apply (EPL.push_back_grow_x L HI HIok LAY FPM OPNEWX LB cr o cap p c sp r s fx R M model K HH Hmo HKnil Hfp).
      { split; [split; [lia | exact Heq]|]. repeat (split; [assumption|]). apply Hcredit. cbn [fits]. unfold len. lia. }
      intros fx' R' M' model' LB' cr' LBk W HFP ((p' & Hpost) & HW) HRP HP Hbv HH2.
      apply (Hcont fx' R' M' model' LB' cr' LBk W HFP); [|assumption..].
      cbv zeta in Hpost. destruct Hpost as (Hs & Hfb & HLB & Hcr & HLBk).
      exists (PML.SLong (PML.grow_cap cap (Z.of_nat (length (s ++ [c])))) p' (s ++ [c])). split; [|exact HW]. right.
      split; [cbn [fits]; rewrite LENA; unfold len; lia|]. exists p'. cbv zeta. cbn [alloc_of lb_drop]. fold (len (s ++ [c])).
      split; [reflexivity|].
      destruct (EK.grow_cap_ge cap (len (s ++ [c])) ltac:(lia) Hc8 ltac:(unfold len; lia)) as (G1 & G2 & G3).
      split; [split; [exact Hs | split; [apply (defined_long_obj M' o _ p' _ Hs); unfold GK.HULL_HI; lia | cbn [rep_ok]; lia]]|]. auto.
Qed.
End PushBackX.
End EPB.
Print Assumptions EPB.str_push_back_x_ok.
