(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common Require Import PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim RefMemcpyLib.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Leptonica Require Import PortLib.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Leptonica Require Import SumWalkTac Frame.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Reloc Require Import RelocKit RCode_13084_14000 RCode_1c000_1d000.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Musl Require Import MuslTac MemcpyBase.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Leptonica Require Import PFLib.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Reloc Require Import RelocKit .
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Musl Require Import MuslTac PFBase PFFwx PFStr PFCore PFCoreTop PFVfp PFVsn.
Import ListNotations.
Open Scope bv_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation W8 v := (word_to_le_bytes 8 (Z_to_bv 64 v)).
Abbreviation X8 w := (word_to_le_bytes 8 w).

Ltac indec := apply in_regs_dec; reflexivity.

(* [comment removed for export] *)
Section GD_1.
  Context {RL : Reloc}.
Definition vaf (regs : bvmap 5 word) (q : Z) : word :=
  if (q =? 0)%Z then getr regs 11 else if (q =? 1)%Z then getr regs 12 else if (q =? 2)%Z then getr regs 13
  else if (q =? 3)%Z then getr regs 14 else if (q =? 4)%Z then getr regs 15 else if (q =? 5)%Z then getr regs 16
  else getr regs 17.
End GD_1.

Section LEPT.
  Context {fx : FPState} {RL : Reloc} {RLC : RelocCode RL} {RLS : RelocSites RL} {RLD : RelocData RL} {RLI : RelocImg RL} {RLW : RelocRW RL RLD} {RLP : RelocPF RL}.
  Variables (sp0 : Z) (mem0 : word -> option byte) (cv : Z) (rom : word -> option byte).
  Hypothesis CTX : ctxH sp0 mem0 cv.
  Let Hcsp : (IMG_TOP + FR <= sp0 <= 0x800000000000)%Z := Csp _ _ _ CTX.
  Ltac sok := soks CTX.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition leptM1 (m : word -> option byte) (regs : bvmap 5 word) (ret : word) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m
      (Z_to_bv 64 (sp0 - 72)) (X8 ret))
      (Z_to_bv 64 (sp0 - 24)) (X8 (getr regs 15)))
      (Z_to_bv 64 (sp0 - 16)) (X8 (getr regs 16)))
      (Z_to_bv 64 (sp0 - 8)) (X8 (getr regs 17)))
      (Z_to_bv 64 (sp0 - 56)) (X8 (getr regs 11)))
      (Z_to_bv 64 (sp0 - 48)) (X8 (getr regs 12)))
      (Z_to_bv 64 (sp0 - 40)) (X8 (getr regs 13)))
      (Z_to_bv 64 (sp0 - 32)) (X8 (getr regs 14)))
      (Z_to_bv 64 (sp0 - 80)) (W8 (sp0 - 56)).

  Lemma lept_seg_a : forall m regs (ret : word) (fa : Z),
    FRM sp0 mem0 m ->
    getr regs 1 = ret -> getr regs 2 = Z_to_bv 64 sp0 -> getr regs 10 = Z_to_bv 64 fa ->
    exists r,
      msteps SEGS (mkst regs (rl dF_13694 0x13694) m rom) (mkst r (rl dF_1c740 0x1c740) (leptM1 m regs ret) rom)
      /\ getr r 1 = (rl dF_13694 0x1370c) /\ getr r 2 = Z_to_bv 64 (sp0 - 2096)
      /\ getr r 10 = Z_to_bv 64 (sp0 - 2080) /\ getr r 11 = Z_to_bv 64 2000
      /\ getr r 12 = Z_to_bv 64 fa /\ getr r 13 = Z_to_bv 64 (sp0 - 56)
      /\ (forall x : reg, In x [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr r x = getr regs x).
  Proof.
    intros m regs ret fa F H1 H2 H10.
    pose proof Hcsp as Hsp0. lay.
    eexists. split.
    - stepiv F_13694 D_13694 (Z_to_bv 64 (sp0 - 2032)) ltac:(zval).             (* [comment removed for export] *)
      stepST F_13698 D_13698 (Z_to_bv 64 (sp0 - 72)) ret ltac:(sok).              (* [comment removed for export] *)
      stepiv F_1369c D_1369c (Z_to_bv 64 (sp0 - 2096)) ltac:(zval).             (* [comment removed for export] *)
      stepn F_136a0 D_136a0.                                                      (* [comment removed for export] *)
      stepn F_136a4 D_136a4.                                                      (* [comment removed for export] *)
      stepiv F_136a8 D_136a8 (Z_to_bv 64 (sp0 + 2000)) ltac:(zval).             (* [comment removed for export] *)
      stepST F_136ac D_136ac (Z_to_bv 64 (sp0 - 24)) (getr regs 15) ltac:(sok).   (* [comment removed for export] *)
      stepn F_136b0 D_136b0.                                                      (* [comment removed for export] *)
      stepiv F_136b4 D_136b4 (Z_to_bv 64 (sp0 + 2000)) ltac:(zval).             (* [comment removed for export] *)
      stepST F_136b8 D_136b8 (Z_to_bv 64 (sp0 - 16)) (getr regs 16) ltac:(sok).   (* [comment removed for export] *)
      stepn F_136bc D_136bc.                                                      (* [comment removed for export] *)
      stepiv F_136c0 D_136c0 (Z_to_bv 64 (sp0 + 2000)) ltac:(zval).             (* [comment removed for export] *)
      stepST F_136c4 D_136c4 (Z_to_bv 64 (sp0 - 8)) (getr regs 17) ltac:(sok).    (* [comment removed for export] *)
      stepST F_136c8 D_136c8 (Z_to_bv 64 (sp0 - 56)) (getr regs 11) ltac:(sok).   (* [comment removed for export] *)
      stepn F_136cc D_136cc.                                                      (* [comment removed for export] *)
      stepiv F_136d0 D_136d0 (Z_to_bv 64 (sp0 + 2000)) ltac:(zval).             (* [comment removed for export] *)
      stepST F_136d4 D_136d4 (Z_to_bv 64 (sp0 - 48)) (getr regs 12) ltac:(sok).   (* [comment removed for export] *)
      stepn F_136d8 D_136d8.                                                      (* [comment removed for export] *)
      stepiv F_136dc D_136dc (Z_to_bv 64 (sp0 + 2000)) ltac:(zval).             (* [comment removed for export] *)
      stepST F_136e0 D_136e0 (Z_to_bv 64 (sp0 - 40)) (getr regs 13) ltac:(sok).   (* [comment removed for export] *)
      stepn F_136e4 D_136e4.                                                      (* [comment removed for export] *)
      stepiv F_136e8 D_136e8 (Z_to_bv 64 (sp0 + 2000)) ltac:(zval).             (* [comment removed for export] *)
      stepST F_136ec D_136ec (Z_to_bv 64 (sp0 - 32)) (getr regs 14) ltac:(sok).   (* [comment removed for export] *)
      stepiv F_136f0 D_136f0 (Z_to_bv 64 (sp0 - 56)) ltac:(zval).               (* [comment removed for export] *)
      stepST F_136f4 D_136f4 (Z_to_bv 64 (sp0 - 80)) (Z_to_bv 64 (sp0 - 56)) ltac:(sok).  (* [comment removed for export] *)
      stepiv F_136f8 D_136f8 (Z_to_bv 64 (sp0 - 2080)) ltac:(zval).             (* [comment removed for export] *)
      stepn F_136fc D_136fc.                                                      (* [comment removed for export] *)
      stepiv F_13700 D_13700 (Z_to_bv 64 (sp0 - 56)) ltac:(zval).               (* [comment removed for export] *)
      stepn F_13704 D_13704.                                                      (* [comment removed for export] *)
      stepn F_13708 D_13708.                                                      (* [comment removed for export] *)
      unfold leptM1. apply mst_refl.
    - repeat (split; [gres; rwH; first [reflexivity | bveq] |]).
      intros x Hx. cbv [In] in Hx. repeat (destruct Hx as [<-|Hx]; [gres; reflexivity|]). destruct Hx.
  Qed.

  Lemma leptM1_frame : forall m regs ret, frame_mod m (leptM1 m regs ret) [(Z_to_bv 64 (sp0 - 80), 80%Z)].
  Proof.
    intros m regs ret. pose proof Hcsp as Hsp0. lay. unfold leptM1.
    frame_tac Hsp0. apply frame_mod_refl.
  Qed.

  Lemma leptM1_va : forall m regs ret q, (0 <= q < 7)%Z -> VAslot (leptM1 m regs ret) sp0 q (vaf regs q).
  Proof.
    intros m regs ret q Hq. pose proof Hcsp as Hsp0. lay. unfold VAslot, vaf, leptM1.
    assert (E : q = 0%Z \/ q = 1%Z \/ q = 2%Z \/ q = 3%Z \/ q = 4%Z \/ q = 5%Z \/ q = 6%Z) by lia.
    destruct E as [-> |[-> |[-> |[-> |[-> |[-> | ->]]]]]]; cbn [Z.eqb Pos.eqb];
      [ replace (sp0 - 56 + 8 * 0)%Z with (sp0 - 56)%Z by lia
      | replace (sp0 - 56 + 8 * 1)%Z with (sp0 - 48)%Z by lia
      | replace (sp0 - 56 + 8 * 2)%Z with (sp0 - 40)%Z by lia
      | replace (sp0 - 56 + 8 * 3)%Z with (sp0 - 32)%Z by lia
      | replace (sp0 - 56 + 8 * 4)%Z with (sp0 - 24)%Z by lia
      | replace (sp0 - 56 + 8 * 5)%Z with (sp0 - 16)%Z by lia
      | replace (sp0 - 56 + 8 * 6)%Z with (sp0 - 8)%Z by lia ]; rdn_solve.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma lept_seg_c : forall M r (ret : word),
    FRM sp0 mem0 M -> ret_ok ret ->
    rdn SEGS M (Z_to_bv 64 (sp0 - 72)) 8 = Some (X8 ret) ->
    getr r 2 = Z_to_bv 64 (sp0 - 2096) ->
    exists r',
      msteps SEGS (mkst r (rl dF_13694 0x1370c) M rom) (mkst r' ret M rom)
      /\ getr r' 2 = Z_to_bv 64 sp0 /\ getr r' 1 = ret
      /\ (forall x : reg, In x [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr r' x = getr r x).
  Proof.
    intros M r ret F Hret Rra R2. pose proof Hcsp as Hsp0. lay.
    pose proof (FRM_hdl sp0 mem0 cv CTX M F) as Rhdl. unfold A_HANDLER_CELL, A_DEVNULL in Rhdl.
    destruct (c_lts (getr r 10) (Z_to_bv 64 0)) eqn:Hc.
    - (* [comment removed for export] *)
      eexists. split.
      + stepb_tk F_1370c D_1370c ltac:(gres; exact Hc).                           (* [comment removed for export] *)
        stepiv F_13720 D_13720 (Z_to_bv 64 (sp0 - 2032)) ltac:(zval).           (* [comment removed for export] *)
        stepLD8 F_13724 D_13724 ret.                                              (* [comment removed for export] *)
        stepiv F_13728 D_13728 (Z_to_bv 64 sp0) ltac:(zval).                    (* [comment removed for export] *)
        stepret F_1372c D_1372c ret ltac:(reflexivity).                          (* [comment removed for export] *)
        apply mst_refl.
      + split; [gres; reflexivity|]. split; [gres; reflexivity|].
        intros x Hx. cbv [In] in Hx. repeat (destruct Hx as [<-|Hx]; [gres; reflexivity|]). destruct Hx.
    - (* [comment removed for export] *)
      eexists. split.
      + stepb_ft F_1370c D_1370c ltac:(gres; exact Hc).                           (* [comment removed for export] *)
        stepn F_13710 D_13710.                                                    (* [comment removed for export] *)
        stepLD8 F_13714 D_13714 (rl dF_1365c 0x1365c).                            (* [comment removed for export] *)
        stepiv F_13718 D_13718 (Z_to_bv 64 (sp0 - 2080)) ltac:(zval).           (* [comment removed for export] *)
        stepretF F_1371c D_1371c F_1365c.                    (* [comment removed for export] *)
        stepretF F_1365c D_1365c F_13720.                    (* [comment removed for export] *)
        stepiv F_13720 D_13720 (Z_to_bv 64 (sp0 - 2032)) ltac:(zval).           (* [comment removed for export] *)
        stepLD8 F_13724 D_13724 ret.                                              (* [comment removed for export] *)
        stepiv F_13728 D_13728 (Z_to_bv 64 sp0) ltac:(zval).                    (* [comment removed for export] *)
        stepret F_1372c D_1372c ret ltac:(reflexivity).                          (* [comment removed for export] *)
        apply mst_refl.
      + split; [gres; reflexivity|]. split; [gres; reflexivity|].
        intros x Hx. cbv [In] in Hx. repeat (destruct Hx as [<-|Hx]; [gres; reflexivity|]). destruct Hx.
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variables (fa : Z) (fbs : list Z).      (* [comment removed for export] *)
  Hypothesis FMT0 : forall i, (0 <= i < Z.of_nat (length fbs))%Z ->
    mem0 (Z_to_bv 64 (fa + i)) = None /\ seg_rom SEGS (Z_to_bv 64 (fa + i)) = Some (Z_to_bv 8 (nth (Z.to_nat i) fbs 0%Z)).
  Hypothesis FMTR : (IMG_LO <= fa /\ fa + Z.of_nat (length fbs) <= IMG_TOP)%Z.
  Hypothesis FBYTE : forall i, (0 <= i < Z.of_nat (length fbs))%Z -> (0 <= nth (Z.to_nat i) fbs 0%Z <= 255)%Z.
  Variable its : list fitem.               (* [comment removed for export] *)
  Hypothesis ITS : flat its = fbs.
  Hypothesis WF : wf_items its = true.
  Hypothesis NC7 : (Z.of_nat (length (convs its)) <= 7)%Z.
  Hypothesis REM : (rem its + 56 <= INT_MAX)%Z.

  Ltac fkeep FM := rewrite (frame_mod_rdn SEGS _ _ _ _ _ FM);
    [ | intros i Hi; cbn [outside]; unfold in_rng; unorm; repeat split; lia | unorm; lia ].

  (* [comment removed for export] *)
  Theorem lept_stderr_run : forall regs (ret : word) (nS : Z) (saddr slen : Z -> Z),
    (forall q, (0 <= q < nS)%Z ->
       vaf regs q = Z_to_bv 64 (saddr q) /\ rostr mem0 (saddr q) (slen q) /\ (slen q <= 200)%Z) ->
    convs_ok nS 0 (convs its) ->
    ret_ok ret -> getr regs 1 = ret -> getr regs 2 = Z_to_bv 64 sp0 -> getr regs 10 = Z_to_bv 64 fa ->
    exists r' m',
      msteps SEGS (mkst regs (rl dF_13694 0x13694) mem0 rom) (mkst r' ret m' rom)
      /\ getr r' 2 = Z_to_bv 64 sp0
      /\ (forall x : reg, In x [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr r' x = getr regs x)
      /\ FRM sp0 mem0 m'.
  Proof.
    intros regs ret nS saddr slen SARGS COK0 Hret H1 H2 H10. pose proof Hcsp as Hsp0.
    (* [comment removed for export] *)
    destruct (lept_seg_a mem0 regs ret fa (FRM_refl sp0 mem0) H1 H2 H10)
      as (r1 & RUN1 & A1 & A2 & A10 & A11 & A12 & A13 & AK).
    pose proof (leptM1_frame mem0 regs ret) as FM1.
    pose proof (leptM1_va mem0 regs ret) as VA1.
    set (M1 := leptM1 mem0 regs ret) in *.
    assert (F1 : FRM sp0 mem0 M1).
    { eapply FRM_sub; [apply FRM_refl | exact FM1 |]. intros a Ho.
      cbn [outside] in Ho |- *. unfold in_rng in *. lay. revert Ho. unorm. intros Ho. repeat split; lia. }
    assert (Cra : rdn SEGS M1 (Z_to_bv 64 (sp0 - 72)) 8 = Some (X8 ret)) by (subst M1; unfold leptM1; lay; rdn_solve).
    clearbody M1.
    (* [comment removed for export] *)
    destruct (vsnprintf_run sp0 mem0 cv rom CTX (getr regs 3) (getr regs 4) (vaf regs) nS saddr slen SARGS
                fa fbs FMT0 FMTR FBYTE its ITS WF COK0 NC7 REM
                M1 r1 (rl dF_13694 0x1370c) ltac:(rl_ret_ok) F1 VA1 A1 A2 A10 A11 A12 A13
                ltac:(apply AK; indec) ltac:(apply AK; indec))
      as (r2 & m2 & RUN2 & B2 & BK & FM2).
    assert (F2 : FRM sp0 mem0 m2).
    { eapply FRM_sub; [exact F1 | exact FM2 |]. intros a Ho. unfold vsn_regions.
      cbn [outside] in Ho |- *. unfold in_rng in *. lay. revert Ho. unorm. intros Ho. repeat split; lia. }
    assert (Cra2 : rdn SEGS m2 (Z_to_bv 64 (sp0 - 72)) 8 = Some (X8 ret)).
    { lay. unfold vsn_regions in FM2. fkeep FM2. exact Cra. }
    (* [comment removed for export] *)
    destruct (lept_seg_c m2 r2 ret F2 Hret Cra2 B2) as (r3 & RUN3 & C2 & C1 & CK).
    exists r3, m2. split; [|split; [exact C2 | split; [|exact F2]]].
    - eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. exact RUN3.
    - intros x Hx. rewrite CK by exact Hx. rewrite BK by exact Hx. apply AK. exact Hx.
  Qed.
End LEPT.
