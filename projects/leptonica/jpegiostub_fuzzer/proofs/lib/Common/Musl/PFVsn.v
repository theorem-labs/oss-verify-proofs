(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common Require Import PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim ZStores RefMemcpyLib.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Leptonica Require Import PortLib.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Leptonica Require Import SumWalkTac Frame.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Reloc Require Import RelocKit RCode_17000_18000 RCode_1c000_1d000.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Musl Require Import MuslTac MemcpyBase.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Leptonica Require Import PFLib.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Reloc Require Import RelocKit .
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Musl Require Import MuslTac PFBase PFMemset232 PFFwx PFStr PFCore PFCoreTop PFVfp.
Import ListNotations.
Open Scope bv_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation W8 v := (word_to_le_bytes 8 (Z_to_bv 64 v)).
Abbreviation W4 v := (word_to_le_bytes 4 (Z_to_bv 64 v)).
Abbreviation X8 w := (word_to_le_bytes 8 w).

Ltac indec := apply in_regs_dec; reflexivity.

(* [comment removed for export] *)
Section GD_1.
  Context {RL : Reloc}.
Definition vsn_regions (sp0 : Z) : list (word * Z) :=
  [(Z_to_bv 64 (sp0 - 3376), 1280%Z); (Z_to_bv 64 (sp0 - 2080), 2000%Z)].
End GD_1.

(* [comment removed for export] *)
Section GD_2.
  Context {RL : Reloc}.
Lemma w4_m1 : word_to_le_bytes 4 (Z_to_bv 64 18446744073709551615) = word_to_le_bytes 4 (Z_to_bv 64 4294967295).
Proof. vm_refl_bv. Qed.
End GD_2.
Section GD_3.
  Context {RL : Reloc}.
Lemma zeros4 : zeros 4 = word_to_le_bytes 4 (Z_to_bv 64 0).
Proof. vm_refl_bv. Qed.
End GD_3.
Section GD_4.
  Context {RL : Reloc}.
Lemma zeros8 : zeros 8 = word_to_le_bytes 8 (Z_to_bv 64 0).
Proof. vm_refl_bv. Qed.
End GD_4.

Section VSN.
  Context {fx : FPState} {RL : Reloc} {RLC : RelocCode RL} {RLS : RelocSites RL} {RLD : RelocData RL} {RLI : RelocImg RL} {RLW : RelocRW RL RLD} {RLP : RelocPF RL}.
  Variables (sp0 : Z) (mem0 : word -> option byte) (cv : Z) (rom : word -> option byte).
  Hypothesis CTX : ctxH sp0 mem0 cv.
  Let Hcsp : (IMG_TOP + FR <= sp0 <= 0x800000000000)%Z := Csp _ _ _ CTX.
  Ltac sok := soks CTX.
  Variables (g3 g4 : word).     (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition vsnM1 (m : word -> option byte) (regs : bvmap 5 word) (ret : word) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m
      (Z_to_bv 64 (sp0 - 2104)) (X8 ret))
      (Z_to_bv 64 (sp0 - 2112)) (X8 (getr regs 8)))
      (Z_to_bv 64 (sp0 - 2120)) (X8 (getr regs 9)))
      (Z_to_bv 64 (sp0 - 2128)) (X8 (getr regs 18)))
      (Z_to_bv 64 (sp0 - 2136)) (X8 (getr regs 19)))
      (Z_to_bv 64 (sp0 - 2144)) (W8 cv))                 (* [comment removed for export] *)
      (Z_to_bv 64 (sp0 - 2168)) (W8 (sp0 - 2080)))       (* [comment removed for export] *)
      (Z_to_bv 64 (sp0 - 2160)) (W8 1999).               (* [comment removed for export] *)

  Lemma vsn_seg_a : forall m regs (ret : word) (fa : Z),
    FRM sp0 mem0 m ->
    getr regs 1 = ret -> getr regs 2 = Z_to_bv 64 (sp0 - 2096) ->
    getr regs 10 = Z_to_bv 64 (sp0 - 2080) -> getr regs 11 = Z_to_bv 64 2000 ->
    getr regs 12 = Z_to_bv 64 fa -> getr regs 13 = Z_to_bv 64 (sp0 - 56) ->
    exists r,
      msteps SEGS (mkst regs (rl dF_1c740 0x1c740) m rom) (mkst r (rl dF_1cdb8 0x1cdb8) (vsnM1 m regs ret) rom)
      /\ getr r 1 = (rl dF_1c740 0x1c7a4) /\ getr r 2 = Z_to_bv 64 (sp0 - 2400) /\ getr r 10 = Z_to_bv 64 (sp0 - 2400)
      /\ getr r 11 = Z_to_bv 64 0 /\ getr r 12 = Z_to_bv 64 232
      /\ getr r 8 = Z_to_bv 64 (sp0 - 56) /\ getr r 9 = Z_to_bv 64 fa /\ getr r 18 = Z_to_bv 64 A_CANARY
      /\ getr r 19 = Z_to_bv 64 (sp0 - 2080)
      /\ (forall x : reg, In x [3; 4; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr r x = getr regs x).
  Proof.
    intros m regs ret fa F H1 H2 H10 H11 H12 H13.
    pose proof Hcsp as Hsp0. lay.
    pose proof (FRM_got sp0 mem0 cv CTX m F) as Rgot.
    pose proof (FRM_can sp0 mem0 cv CTX m F) as Rcan.
    pose proof (Ccv _ _ _ CTX) as Hcv. unfold A_CANARY_GOT, A_CANARY in *.
    eexists. split.
    - stepiv F_1c740 D_1c740 (Z_to_bv 64 (sp0 - 2400)) ltac:(zval).             (* [comment removed for export] *)
      stepST F_1c744 D_1c744 (Z_to_bv 64 (sp0 - 2104)) ret ltac:(sok).            (* [comment removed for export] *)
      stepST F_1c748 D_1c748 (Z_to_bv 64 (sp0 - 2112)) (getr regs 8) ltac:(sok).  (* [comment removed for export] *)
      stepST F_1c74c D_1c74c (Z_to_bv 64 (sp0 - 2120)) (getr regs 9) ltac:(sok).  (* [comment removed for export] *)
      stepST F_1c750 D_1c750 (Z_to_bv 64 (sp0 - 2128)) (getr regs 18) ltac:(sok). (* [comment removed for export] *)
      stepST F_1c754 D_1c754 (Z_to_bv 64 (sp0 - 2136)) (getr regs 19) ltac:(sok). (* [comment removed for export] *)
      stepn F_1c758 D_1c758.                                                      (* [comment removed for export] *)
      stepn F_1c75c D_1c75c.                                                      (* [comment removed for export] *)
      stepn F_1c760 D_1c760.                                                      (* [comment removed for export] *)
      stepLD8 F_1c764 D_1c764 (rl dA_2f848 0x2f848).                              (* [comment removed for export] *)
      stepLD8 F_1c768 D_1c768 (Z_to_bv 64 cv).                                   (* [comment removed for export] *)
      stepST F_1c76c D_1c76c (Z_to_bv 64 (sp0 - 2144)) (Z_to_bv 64 cv) ltac:(sok).        (* [comment removed for export] *)
      stepiv F_1c770 D_1c770 (Z_to_bv 64 (sp0 - 2146)) ltac:(zval).             (* [comment removed for export] *)
      stepb_ft F_1c774 D_1c774 ltac:(cond_vm).                                  (* [comment removed for export] *)
      stepn F_1c778 D_1c778.                                                      (* [comment removed for export] *)
      stepiv F_1c77c D_1c77c (Z_to_bv 64 1999) ltac:(zval).                     (* [comment removed for export] *)
      stepn F_1c780 D_1c780. rwH. vals_lit.                                       (* [comment removed for export] *)
      stepn F_1c784 D_1c784.                                                      (* [comment removed for export] *)
      stepn F_1c788 D_1c788.                                                      (* [comment removed for export] *)
      stepST F_1c78c D_1c78c (Z_to_bv 64 (sp0 - 2168)) (Z_to_bv 64 (sp0 - 2080)) ltac:(sok).  (* [comment removed for export] *)
      stepST F_1c790 D_1c790 (Z_to_bv 64 (sp0 - 2160)) (Z_to_bv 64 1999) ltac:(sok).         (* [comment removed for export] *)
      stepn F_1c794 D_1c794.                                                      (* [comment removed for export] *)
      stepn F_1c798 D_1c798.                                                      (* [comment removed for export] *)
      stepn F_1c79c D_1c79c.                                                      (* [comment removed for export] *)
      stepn F_1c7a0 D_1c7a0.                                                      (* [comment removed for export] *)
      unfold vsnM1. apply mst_refl.
    - repeat (split; [gres; rwH; first [reflexivity | bveq] |]).
      intros x Hx. cbv [In] in Hx. repeat (destruct Hx as [<-|Hx]; [gres; reflexivity|]). destruct Hx.
  Qed.

  Lemma vsnM1_frame : forall m regs ret, frame_mod m (vsnM1 m regs ret) [(Z_to_bv 64 (sp0 - 2400), 304%Z)].
  Proof.
    intros m regs ret. pose proof Hcsp as Hsp0. lay. unfold vsnM1.
    frame_tac Hsp0. apply frame_mod_refl.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition vsnM3 (M : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes M
      (Z_to_bv 64 (sp0 - 2328)) (X8 (rl dF_1c80c 0x1c80c)))            (* [comment removed for export] *)
      (Z_to_bv 64 (sp0 - 2312)) (W8 (sp0 - 2145)))       (* [comment removed for export] *)
      (Z_to_bv 64 (sp0 - 2260)) (W4 4294967295))       (* [comment removed for export] *)
      (Z_to_bv 64 (sp0 - 2256)) (W4 4294967295))       (* [comment removed for export] *)
      (Z_to_bv 64 (sp0 - 2248)) (W8 (sp0 - 2168)))       (* [comment removed for export] *)
      (Z_to_bv 64 (sp0 - 2080)) [Z_to_bv 8 (bv_unsigned (Z_to_bv 64 0))].   (* [comment removed for export] *)

  Lemma vsn_seg_b : forall M r,
    FRM sp0 mem0 M ->
    getr r 2 = Z_to_bv 64 (sp0 - 2400) -> getr r 19 = Z_to_bv 64 (sp0 - 2080) ->
    exists r',
      msteps SEGS (mkst r (rl dF_1c740 0x1c7a4) M rom) (mkst r' (rl dF_17dbc 0x17dbc) (vsnM3 M) rom)
      /\ getr r' 1 = (rl dF_1c740 0x1c7e0) /\ getr r' 2 = Z_to_bv 64 (sp0 - 2400) /\ getr r' 10 = Z_to_bv 64 (sp0 - 2400)
      /\ getr r' 11 = getr r 9 /\ getr r' 12 = getr r 8
      /\ (forall x : reg, In x [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr r' x = getr r x).
  Proof.
    intros M r F R2 R19. pose proof Hcsp as Hsp0. lay.
    eexists. split.
    - stepn F_1c7a4 D_1c7a4.                                                      (* [comment removed for export] *)
      stepiv F_1c7a8 D_1c7a8 (Z_to_bv 64 (sp0 - 2145)) ltac:(zval).             (* [comment removed for export] *)
      stepn F_1c7ac D_1c7ac.                                                      (* [comment removed for export] *)
      stepn F_1c7b0 D_1c7b0.                                                      (* [comment removed for export] *)
      stepST F_1c7b4 D_1c7b4 (Z_to_bv 64 (sp0 - 2328)) (rl dF_1c80c 0x1c80c) ltac:(sok).       (* [comment removed for export] *)
      stepST F_1c7b8 D_1c7b8 (Z_to_bv 64 (sp0 - 2312)) (Z_to_bv 64 (sp0 - 2145)) ltac:(sok). (* [comment removed for export] *)
      stepiv F_1c7bc D_1c7bc (Z_to_bv 64 (sp0 - 2168)) ltac:(zval).             (* [comment removed for export] *)
      stepST F_1c7c0 D_1c7c0 (Z_to_bv 64 (sp0 - 2260)) (Z_to_bv 64 18446744073709551615) ltac:(sok). (* [comment removed for export] *)
      stepST F_1c7c4 D_1c7c4 (Z_to_bv 64 (sp0 - 2256)) (Z_to_bv 64 18446744073709551615) ltac:(sok). (* [comment removed for export] *)
      stepST F_1c7c8 D_1c7c8 (Z_to_bv 64 (sp0 - 2248)) (Z_to_bv 64 (sp0 - 2168)) ltac:(sok). (* [comment removed for export] *)
      stepST F_1c7cc D_1c7cc (Z_to_bv 64 (sp0 - 2080)) (Z_to_bv 64 0) ltac:(sok).            (* [comment removed for export] *)
      stepn F_1c7d0 D_1c7d0.                                                      (* [comment removed for export] *)
      stepn F_1c7d4 D_1c7d4.                                                      (* [comment removed for export] *)
      stepn F_1c7d8 D_1c7d8.                                                      (* [comment removed for export] *)
      stepn F_1c7dc D_1c7dc.                                                      (* [comment removed for export] *)
      rewrite !w4_m1. unfold vsnM3. apply mst_refl.
    - repeat (split; [gres; rwH; first [reflexivity | bveq] |]).
      intros x Hx. cbv [In] in Hx. repeat (destruct Hx as [<-|Hx]; [gres; reflexivity|]). destruct Hx.
  Qed.

  Lemma vsnM3_frame : forall M, frame_mod M (vsnM3 M) [(Z_to_bv 64 (sp0 - 2328), 88%Z); (Z_to_bv 64 (sp0 - 2080), 1%Z)].
  Proof.
    intros M. pose proof Hcsp as Hsp0. lay. unfold vsnM3.
    frame_tac Hsp0. apply frame_mod_refl.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma vsn_seg_c : forall M r regs (ret : word),
    FRM sp0 mem0 M -> ret_ok ret ->
    rdn SEGS M (Z_to_bv 64 (sp0 - 2144)) 8 = Some (W8 cv) ->
    rdn SEGS M (Z_to_bv 64 (sp0 - 2104)) 8 = Some (X8 ret) ->
    rdn SEGS M (Z_to_bv 64 (sp0 - 2112)) 8 = Some (X8 (getr regs 8)) ->
    rdn SEGS M (Z_to_bv 64 (sp0 - 2120)) 8 = Some (X8 (getr regs 9)) ->
    rdn SEGS M (Z_to_bv 64 (sp0 - 2128)) 8 = Some (X8 (getr regs 18)) ->
    rdn SEGS M (Z_to_bv 64 (sp0 - 2136)) 8 = Some (X8 (getr regs 19)) ->
    getr r 2 = Z_to_bv 64 (sp0 - 2400) -> getr r 18 = Z_to_bv 64 A_CANARY ->
    exists r',
      msteps SEGS (mkst r (rl dF_1c740 0x1c7e0) M rom) (mkst r' ret M rom)
      /\ getr r' 2 = Z_to_bv 64 (sp0 - 2096) /\ getr r' 1 = ret
      /\ (forall x : reg, In x [8; 9; 18; 19]%bv -> getr r' x = getr regs x)
      /\ (forall x : reg, In x [3; 4; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr r' x = getr r x).
  Proof.
    intros M r regs ret F Hret Rcv Rra Rs0 Rs1 Rs2 Rs3 R2 R18.
    pose proof Hcsp as Hsp0. lay.
    pose proof (FRM_can sp0 mem0 cv CTX M F) as Rcan. pose proof (Ccv _ _ _ CTX) as Hcv. unfold A_CANARY in *.
    eexists. split.
    - stepLD8 F_1c7e0 D_1c7e0 (Z_to_bv 64 cv).                                   (* [comment removed for export] *)
      stepLD8 F_1c7e4 D_1c7e4 (Z_to_bv 64 cv).                                   (* [comment removed for export] *)
      stepb_ft F_1c7e8 D_1c7e8 ltac:(rwH; apply c_eq_refl).                      (* [comment removed for export] *)
      stepLD8 F_1c7ec D_1c7ec ret.                                                (* [comment removed for export] *)
      stepLD8 F_1c7f0 D_1c7f0 (getr regs 8).                                      (* [comment removed for export] *)
      stepLD8 F_1c7f4 D_1c7f4 (getr regs 9).                                      (* [comment removed for export] *)
      stepLD8 F_1c7f8 D_1c7f8 (getr regs 18).                                     (* [comment removed for export] *)
      stepLD8 F_1c7fc D_1c7fc (getr regs 19).                                     (* [comment removed for export] *)
      stepiv F_1c800 D_1c800 (Z_to_bv 64 (sp0 - 2096)) ltac:(zval).             (* [comment removed for export] *)
      stepret F_1c804 D_1c804 ret ltac:(reflexivity).                            (* [comment removed for export] *)
      apply mst_refl.
    - split; [gres; reflexivity|]. split; [gres; reflexivity|]. split.
      + intros x Hx. cbv [In] in Hx. repeat (destruct Hx as [<-|Hx]; [gres; reflexivity|]). destruct Hx.
      + intros x Hx. cbv [In] in Hx. repeat (destruct Hx as [<-|Hx]; [gres; reflexivity|]). destruct Hx.
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variable va : Z -> word.
  Variables (nS : Z) (saddr slen : Z -> Z).
  Hypothesis SARGS : forall q, (0 <= q < nS)%Z ->
    va q = Z_to_bv 64 (saddr q) /\ rostr mem0 (saddr q) (slen q) /\ (slen q <= 200)%Z.
  Variables (fa : Z) (fbs : list Z).
  Hypothesis FMT0 : forall i, (0 <= i < Z.of_nat (length fbs))%Z ->
    mem0 (Z_to_bv 64 (fa + i)) = None /\ seg_rom SEGS (Z_to_bv 64 (fa + i)) = Some (Z_to_bv 8 (nth (Z.to_nat i) fbs 0%Z)).
  Hypothesis FMTR : (IMG_LO <= fa /\ fa + Z.of_nat (length fbs) <= IMG_TOP)%Z.
  Hypothesis FBYTE : forall i, (0 <= i < Z.of_nat (length fbs))%Z -> (0 <= nth (Z.to_nat i) fbs 0%Z <= 255)%Z.
  Variable its : list fitem.
  Hypothesis ITS : flat its = fbs.
  Hypothesis WF : wf_items its = true.
  Hypothesis COK0 : convs_ok nS 0 (convs its).
  Hypothesis NC7 : (Z.of_nat (length (convs its)) <= 7)%Z.
  Hypothesis REM : (rem its + 56 <= INT_MAX)%Z.

  Ltac fkeep FM := rewrite (frame_mod_rdn SEGS _ _ _ _ _ FM);
    [ | intros i Hi; cbn [outside]; unfold in_rng; unorm; repeat split; lia | unorm; lia ].

  Theorem vsnprintf_run : forall m regs (ret : word),
    ret_ok ret -> FRM sp0 mem0 m ->
    (forall q, (0 <= q < 7)%Z -> VAslot m sp0 q (va q)) ->
    getr regs 1 = ret -> getr regs 2 = Z_to_bv 64 (sp0 - 2096) ->
    getr regs 10 = Z_to_bv 64 (sp0 - 2080) -> getr regs 11 = Z_to_bv 64 2000 ->
    getr regs 12 = Z_to_bv 64 fa -> getr regs 13 = Z_to_bv 64 (sp0 - 56) ->
    getr regs 3 = g3 -> getr regs 4 = g4 ->
    exists r' m',
      msteps SEGS (mkst regs (rl dF_1c740 0x1c740) m rom) (mkst r' ret m' rom)
      /\ getr r' 2 = Z_to_bv 64 (sp0 - 2096)
      /\ (forall x : reg, In x [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr r' x = getr regs x)
      /\ frame_mod m m' (vsn_regions sp0).
  Proof.
    intros m regs ret Hret F VA H1 H2 H10 H11 H12 H13 H3 H4. pose proof Hcsp as Hsp0.
    pose proof (Csp16 _ _ _ CTX) as AL16.
    assert (SUBv : forall m1 m2 rs, FRM sp0 mem0 m1 -> frame_mod m1 m2 rs ->
              (forall a, outside a (vsn_regions sp0) -> outside a rs) -> FRM sp0 mem0 m2 /\ frame_mod m1 m2 (vsn_regions sp0)).
    { intros m1 m2 rs Fa Fb W. split.
      - eapply FRM_sub; [exact Fa | exact Fb |]. intros a Ho. apply W.
        unfold vsn_regions in *. cbn [outside] in Ho |- *. unfold in_rng in *. lay. revert Ho. unorm. intros Ho. repeat split; lia.
      - eapply frame_mod_weaken; [exact W | exact Fb]. }
    (* [comment removed for export] *)
    destruct (vsn_seg_a m regs ret fa F H1 H2 H10 H11 H12 H13)
      as (r1 & RUN1 & A1 & A2 & A10 & A11 & A12 & A8 & A9 & A18 & A19 & AK).
    pose proof (vsnM1_frame m regs ret) as FM1.
    set (M1 := vsnM1 m regs ret) in *.
    destruct (SUBv m M1 _ F FM1) as [F1 V1].
    { intros a Ho. unfold vsn_regions in *. cbn [outside] in Ho |- *. unfold in_rng in *. lay. revert Ho. unorm. intros Ho. repeat split; lia. }
    assert (C44 : rdn SEGS M1 (Z_to_bv 64 (sp0 - 2144)) 8 = Some (W8 cv)) by (subst M1; unfold vsnM1; lay; rdn_solve).
    assert (C04 : rdn SEGS M1 (Z_to_bv 64 (sp0 - 2104)) 8 = Some (X8 ret)) by (subst M1; unfold vsnM1; lay; rdn_solve).
    assert (C12 : rdn SEGS M1 (Z_to_bv 64 (sp0 - 2112)) 8 = Some (X8 (getr regs 8))) by (subst M1; unfold vsnM1; lay; rdn_solve).
    assert (C20 : rdn SEGS M1 (Z_to_bv 64 (sp0 - 2120)) 8 = Some (X8 (getr regs 9))) by (subst M1; unfold vsnM1; lay; rdn_solve).
    assert (C28 : rdn SEGS M1 (Z_to_bv 64 (sp0 - 2128)) 8 = Some (X8 (getr regs 18))) by (subst M1; unfold vsnM1; lay; rdn_solve).
    assert (C36 : rdn SEGS M1 (Z_to_bv 64 (sp0 - 2136)) 8 = Some (X8 (getr regs 19))) by (subst M1; unfold vsnM1; lay; rdn_solve).
    assert (Ccs : rdn SEGS M1 (Z_to_bv 64 (sp0 - 2168)) 8 = Some (W8 (sp0 - 2080))) by (subst M1; unfold vsnM1; lay; rdn_solve).
    assert (Ccn : rdn SEGS M1 (Z_to_bv 64 (sp0 - 2160)) 8 = Some (W8 1999)) by (subst M1; unfold vsnM1; lay; rdn_solve).
    clearbody M1.
    (* [comment removed for export] *)
    assert (SOK1 : store_ok SEGS M1 (Z_to_bv 64 (sp0 - 2400)) 232 = true).
    { eapply (FRM_sok sp0 mem0 cv CTX); [exact F1 | lay; lia | lay; cbn; lia]. }
    assert (AL8 : (bv_unsigned (Z_to_bv 64 (sp0 - 2400)) mod 8 = 0)%Z).
    { lay. unorm. destruct (proj1 (Z.mod_divide sp0 16 ltac:(lia)) AL16) as [k Hk].
      replace (sp0 - 2400)%Z with ((2 * k - 300) * 8)%Z by lia. apply Z.mod_mul. lia. }
    destruct (memset232_run r1 M1 rom (Z_to_bv 64 (sp0 - 2400)) (rl dF_1c740 0x1c7a4) A1 ltac:(rl_ret_ok)
                A10 A11 A12 AL8 ltac:(lay; unorm; lia) SOK1) as (r2 & M2 & RUN2 & HM2 & RA2).
    assert (FM2 : frame_mod M1 M2 [(Z_to_bv 64 (sp0 - 2400), 232%Z)]).
    { rewrite HM2. replace 232%Z with (Z.of_nat (length (zeros 232))) by (rewrite length_zeros; reflexivity).
      apply frame_mod_wbytes. rewrite length_zeros. lay. unorm. lia. }
    destruct (SUBv M1 M2 _ F1 FM2) as [F2 V2].
    { intros a Ho. unfold vsn_regions in *. cbn [outside] in Ho |- *. unfold in_rng in *. lay. revert Ho. unorm. intros Ho. repeat split; lia. }
    assert (Zfl : rdn SEGS M2 (Z_to_bv 64 (sp0 - 2400)) 4 = Some (W4 0)).
    { rewrite HM2, <- zeros4. apply rdn_wbytes_zeros_in; lay; unorm; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia. }
    assert (Zbsz : rdn SEGS M2 (Z_to_bv 64 (sp0 - 2304)) 8 = Some (W8 0)).
    { rewrite HM2, <- zeros8. apply rdn_wbytes_zeros_in; lay; unorm; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia. }
    assert (Zmode : rdn SEGS M2 (Z_to_bv 64 (sp0 - 2264)) 4 = Some (W4 0)).
    { rewrite HM2, <- zeros4. apply rdn_wbytes_zeros_in; lay; unorm; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia. }
    assert (KM : forall (a : Z) v, (sp0 - 2168 <= a)%Z -> (a + 8 <= sp0 - 2096)%Z ->
              rdn SEGS M1 (Z_to_bv 64 a) 8 = Some v -> rdn SEGS M2 (Z_to_bv 64 a) 8 = Some v).
    { intros a v Ha1 Ha2 R. lay. fkeep FM2. exact R. }
    apply KM in C44; [|lia|lia]. apply KM in C04; [|lia|lia]. apply KM in C12; [|lia|lia]. apply KM in C20; [|lia|lia].
    apply KM in C28; [|lia|lia]. apply KM in C36; [|lia|lia]. apply KM in Ccs; [|lia|lia]. apply KM in Ccn; [|lia|lia].
    clear KM HM2 SOK1.
    (* [comment removed for export] *)
    assert (NC : forall x : reg, In x [3; 4; 2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr r2 x = getr r1 x).
    { intros x Hx. apply RA2. intros Hc. cbv [memset232_clob In] in Hc, Hx.
      repeat (destruct Hx as [<-|Hx]; [intuition discriminate|]). destruct Hx. }
    assert (B2 : getr r2 2 = Z_to_bv 64 (sp0 - 2400)) by (rewrite NC by indec; exact A2).
    assert (B19 : getr r2 19 = Z_to_bv 64 (sp0 - 2080)) by (rewrite NC by indec; exact A19).
    destruct (vsn_seg_b M2 r2 F2 B2 B19) as (r3 & RUN3 & C1 & C2 & C10 & C11 & C12r & CK3).
    pose proof (vsnM3_frame M2) as FM3.
    set (M3 := vsnM3 M2) in *.
    destruct (SUBv M2 M3 _ F2 FM3) as [F3 V3].
    { intros a Ho. unfold vsn_regions in *. cbn [outside] in Ho |- *. unfold in_rng in *. lay. revert Ho. unorm. intros Ho. repeat split; lia. }
    assert (VF3 : VFc M3 sp0).
    { subst M3. unfold vsnM3. lay. split; rdn_solve_w. }
    assert (CKS3 : CKst M3 sp0 0).
    { split; [|split; [|lia]].
      - rewrite Z.add_0_r. subst M3. unfold vsnM3. lay. rdn_solve_w.
      - replace (1999 - 0)%Z with 1999%Z by reflexivity. subst M3. unfold vsnM3. lay. rdn_solve_w. }
    assert (VA3 : forall q, (0 <= q < 7)%Z -> VAslot M3 sp0 q (va q)).
    { intros q Hq. unfold VAslot. lay. fkeep FM3. fkeep FM2. fkeep FM1. apply VA. exact Hq. }
    assert (KM : forall (a : Z) v, (sp0 - 2168 <= a)%Z -> (a + 8 <= sp0 - 2096)%Z ->
              rdn SEGS M2 (Z_to_bv 64 a) 8 = Some v -> rdn SEGS M3 (Z_to_bv 64 a) 8 = Some v).
    { intros a v Ha1 Ha2 R. lay. fkeep FM3. exact R. }
    apply KM in C44; [|lia|lia]. apply KM in C04; [|lia|lia]. apply KM in C12; [|lia|lia]. apply KM in C20; [|lia|lia].
    apply KM in C28; [|lia|lia]. apply KM in C36; [|lia|lia]. clear KM.
    clearbody M3.
    assert (C11' : getr r3 11 = Z_to_bv 64 fa) by (rewrite C11; rewrite NC by indec; exact A9).
    assert (C12' : getr r3 12 = Z_to_bv 64 (sp0 - 56)) by (rewrite C12r; rewrite NC by indec; exact A8).
    assert (C3' : getr r3 3 = g3) by (rewrite CK3 by indec; rewrite NC by indec; rewrite AK by indec; exact H3).
    assert (C4' : getr r3 4 = g4) by (rewrite CK3 by indec; rewrite NC by indec; rewrite AK by indec; exact H4).
    (* [comment removed for export] *)
    destruct (vfprintf_run sp0 mem0 cv rom CTX g3 g4 va nS saddr slen SARGS fa fbs FMT0 FMTR FBYTE its ITS WF COK0 NC7 REM
                M3 r3 (rl dF_1c740 0x1c7e0) 0 ltac:(rl_ret_ok) F3 VF3 CKS3 VA3 C1 C2 C10 C11' C12' C3' C4')
      as (r4 & m4 & RUN4 & D2 & DK & FM4).
    destruct (SUBv M3 m4 _ F3 FM4) as [F4 V4].
    { intros a Ho. unfold vsn_regions, vfp_regions in *. cbn [outside] in Ho |- *. unfold in_rng in *. lay. revert Ho. unorm. intros Ho. repeat split; lia. }
    assert (KM : forall (a : Z) v, (sp0 - 2152 <= a)%Z -> (a + 8 <= sp0 - 2096)%Z ->
              rdn SEGS M3 (Z_to_bv 64 a) 8 = Some v -> rdn SEGS m4 (Z_to_bv 64 a) 8 = Some v).
    { intros a v Ha1 Ha2 R. lay. unfold vfp_regions in FM4. fkeep FM4. exact R. }
    apply KM in C44; [|lia|lia]. apply KM in C04; [|lia|lia]. apply KM in C12; [|lia|lia]. apply KM in C20; [|lia|lia].
    apply KM in C28; [|lia|lia]. apply KM in C36; [|lia|lia]. clear KM.
    (* [comment removed for export] *)
    assert (D18 : getr r4 18 = Z_to_bv 64 A_CANARY).
    { rewrite DK by indec. rewrite CK3 by indec. rewrite NC by indec. exact A18. }
    destruct (vsn_seg_c m4 r4 regs ret F4 Hret C44 C04 C12 C20 C28 C36 D2 D18) as (r5 & RUN5 & E2 & E1 & EK1 & EK2).
    exists r5, m4. split; [|split; [exact E2 | split]].
    - eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUN3|].
      eapply msteps_trans; [exact RUN4|]. exact RUN5.
    - intros x Hx. cbv [In] in Hx.
      destruct Hx as [<-|[<-|Hx]].
      1,2: rewrite EK2 by indec; rewrite DK by indec; rewrite CK3 by indec; rewrite NC by indec; apply AK; indec.
      destruct Hx as [<-|[<-|[<-|[<-|Hx]]]]; try (apply EK1; indec).
      repeat (destruct Hx as [<-|Hx];
        [ rewrite EK2 by indec; rewrite DK by indec; rewrite CK3 by indec; rewrite NC by indec; apply AK; indec |]).
      destruct Hx.
    - eapply frame_mod_trans_same; [exact V1|]. eapply frame_mod_trans_same; [exact V2|].
      eapply frame_mod_trans_same; [exact V3|]. exact V4.
  Qed.
End VSN.
