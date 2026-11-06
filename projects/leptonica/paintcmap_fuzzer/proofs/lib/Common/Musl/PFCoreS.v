(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common Require Import PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim RefMemcpyLib.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Leptonica Require Import PortLib.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Leptonica Require Import SumWalkTac Frame.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Reloc Require Import RelocKit RCode_17000_18000 RCode_18000_19000 RCode_1c000_1d000.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Musl Require Import MuslTac MemcpyBase.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Leptonica Require Import PFLib.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Reloc Require Import RelocKit .
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Musl Require Import MuslTac PFBase PFFwx PFStr PFCore PFInv.
Import ListNotations.
Open Scope bv_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation W8 v := (word_to_le_bytes 8 (Z_to_bv 64 v)).
Abbreviation W4 v := (word_to_le_bytes 4 (Z_to_bv 64 v)).
Abbreviation X8 w := (word_to_le_bytes 8 w).

Ltac indec := apply in_regs_dec; reflexivity.

Section CS.
  Context {fx : FPState} {RL : Reloc} {RLC : RelocCode RL} {RLS : RelocSites RL} {RLD : RelocData RL} {RLI : RelocImg RL} {RLW : RelocRW RL RLD} {RLP : RelocPF RL}.
  Variables (sp0 : Z) (mem0 : word -> option byte) (cv : Z) (rom : word -> option byte).
  Hypothesis CTX : ctxH sp0 mem0 cv.
  Let Hcsp : (IMG_TOP + FR <= sp0 <= 0x800000000000)%Z := Csp _ _ _ CTX.
  Ltac sok := soks CTX.
  Variables (g3 g4 : word).     (* [comment removed for export] *)

  Variables (a ka : Z).
  Hypothesis RS : rostr mem0 a ka.
  Hypothesis Hka : (ka <= 200)%Z.

  (* [comment removed for export] *)
  Lemma s_seg_a : forall m1 r,
    rdn SEGS m1 (Z_to_bv 64 (sp0 - 3200)) 8 = Some (X8 (Z_to_bv 64 a)) ->
    getr r 2 = Z_to_bv 64 (sp0 - 3312) -> getr r 9 = Z_to_bv 64 INT_MAX -> getr r 25 = Z_to_bv 64 18446744073709551615 ->
    exists r',
      msteps SEGS (mkst r (rl dF_17f6c 0x1854c) m1 rom) (mkst r' (rl dF_1cf40 0x1cf40) m1 rom)
      /\ getr r' 1 = (rl dF_17f6c 0x18584) /\ getr r' 10 = Z_to_bv 64 a /\ getr r' 11 = Z_to_bv 64 0x7fffffff
      /\ getr r' 23 = Z_to_bv 64 a
      /\ (forall x : reg, In x [3; 4; 2; 5; 8; 9; 18; 19; 20; 21; 22; 24; 25; 26; 27]%bv -> getr r' x = getr r x).
  Proof.
    intros m1 r ARG R2 R9 R25. pose proof Hcsp as Hsp0. lay. unfold INT_MAX in *.
    pose proof (rostr_range mem0 a ka RS Hka) as RR.
    assert (K0 : (0 <= ka)%Z) by (destruct RS as [K0 _]; exact K0).
    eexists. split.
    - stepLD8 F_1854c D_1854c (Z_to_bv 64 a).                                                    (* [comment removed for export] *)
      stepb_tk F_18550 D_18550 ltac:(rewrite c_eq_Z by lia; apply Z.eqb_neq; lia).               (* [comment removed for export] *)
      stepn F_18570 D_18570; rwH.                                                                  (* [comment removed for export] *)
      stepb_ft F_18574 D_18574 ltac:(cond_vm).                                                     (* [comment removed for export] *)
      stepn F_18578 D_18578; rwH.                                                                  (* [comment removed for export] *)
      stepn F_1857c D_1857c.                                                                       (* [comment removed for export] *)
      stepn F_18580 D_18580.                                                                       (* [comment removed for export] *)
      apply mst_refl.
    - split; [gres; bveq|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|].
      intros x Hx. cbv [In] in Hx. repeat (destruct Hx as [<-|Hx]; [gres; reflexivity|]). destruct Hx.
  Qed.

  (* [comment removed for export] *)
  Definition segbM (m2 : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes m2
      (Z_to_bv 64 (sp0 - 3288)) (W8 0))                (* [comment removed for export] *)
      (Z_to_bv 64 (sp0 - 3312)) (X8 (rl dS_102e7 0x102e7)))          (* [comment removed for export] *)
      (Z_to_bv 64 (sp0 - 3296)) (W8 ka))               (* [comment removed for export] *)
      (Z_to_bv 64 (sp0 - 3280)) (W8 ka))               (* [comment removed for export] *)
      (Z_to_bv 64 (sp0 - 3304)) (W8 0).                (* [comment removed for export] *)

  Lemma s_seg_b : forall m2 r (cnt' : Z),
    FRM sp0 mem0 m2 -> FILEc m2 sp0 -> (0 <= cnt')%Z -> (cnt' + ka <= INT_MAX)%Z ->
    getr r 2 = Z_to_bv 64 (sp0 - 3312) -> getr r 9 = Z_to_bv 64 INT_MAX -> getr r 10 = Z_to_bv 64 ka ->
    getr r 18 = Z_to_bv 64 (INT_MAX - cnt') -> getr r 20 = Z_to_bv 64 (sp0 - 2400) -> getr r 22 = Z_to_bv 64 0 ->
    getr r 23 = Z_to_bv 64 a -> getr r 25 = Z_to_bv 64 18446744073709551615 -> getr r 26 = Z_to_bv 64 0 ->
    exists r',
      msteps SEGS (mkst r (rl dF_17f6c 0x18584) m2 rom) (mkst r' (rl dF_17b9c 0x17b9c) (segbM m2) rom)
      /\ getr r' 1 = (rl dF_17f6c 0x189ac) /\ getr r' 10 = rl dS_102e7 0x102e7 /\ getr r' 11 = Z_to_bv 64 0
      /\ getr r' 12 = Z_to_bv 64 (sp0 - 2400)
      /\ getr r' 18 = Z_to_bv 64 0 /\ getr r' 25 = Z_to_bv 64 ka /\ getr r' 26 = Z_to_bv 64 ka /\ getr r' 23 = Z_to_bv 64 a
      /\ (forall x : reg, In x [3; 4; 2; 8; 9; 19; 20; 21]%bv -> getr r' x = getr r x).
  Proof.
    intros m2 r cnt' F2 FC2 Hc0 Hck R2 R9 R10 R18 R20 R22 R23 R25 R26. pose proof Hcsp as Hsp0. lay. unfold INT_MAX in *.
    pose proof (rostr_range mem0 a ka RS Hka) as RR.
    assert (K0 : (0 <= ka)%Z) by (destruct RS as [K0 _]; exact K0).
    pose proof (Fc_flags _ _ FC2) as Cfl.
    (* [comment removed for export] *)
    assert (NUL : rdn SEGS m2 (Z_to_bv 64 (a + ka)) 1 = Some [Z_to_bv 8 0]).
    { destruct RS as (_ & _ & NONE & _ & ZE & _).
      rewrite (FRM_rdn sp0 mem0 cv CTX m2 (a + ka) 1 F2); [| lia | lay; lia | lia].
      apply rdn1_rom; [apply NONE; lia | exact ZE]. }
    eexists. split.
    - stepiv F_18584 D_18584 (Z_to_bv 64 (a + ka)) ltac:(zval).                                  (* [comment removed for export] *)
      stepb_ft F_18588 D_18588 ltac:(cond_vm).                                                     (* [comment removed for export] *)
      stepLBU F_1858c D_1858c (Z_to_bv 8 0) ltac:(addr_norm; exact NUL).                          (* [comment removed for export] *)
      stepb_ft F_18590 D_18590 ltac:(apply c_eq_refl).                                             (* [comment removed for export] *)
      stepST F_18594 D_18594 (Z_to_bv 64 (sp0 - 3288)) (Z_to_bv 64 0) ltac:(sok).                (* [comment removed for export] *)
      stepn F_18598 D_18598.                                                                       (* [comment removed for export] *)
      stepn F_1859c D_1859c.                                                                       (* [comment removed for export] *)
      stepST F_185a0 D_185a0 (Z_to_bv 64 (sp0 - 3312)) (rl dS_102e7 0x102e7) ltac:(sok).          (* [comment removed for export] *)
      stepn F_185a4 D_185a4; rwH.                                                                  (* [comment removed for export] *)
      stepn F_185a8 D_185a8.                                                                       (* [comment removed for export] *)
      stepn F_188b4 D_188b4; rwH.                                                                  (* [comment removed for export] *)
      stepiv F_188b8 D_188b8 (Z_to_bv 64 ka) ltac:(gres; rwH; imm_norm; rewrite v_addiw_Z by lia; f_equal; lia). (* [comment removed for export] *)
      stepiv F_188bc D_188bc (Z_to_bv 64 ka) ltac:(zval).                                         (* [comment removed for export] *)
      stepn F_188c0 D_188c0.                                                                       (* [comment removed for export] *)
      stepST F_188c4 D_188c4 (Z_to_bv 64 (sp0 - 3296)) (Z_to_bv 64 ka) ltac:(sok).               (* [comment removed for export] *)
      stepb_ft F_188c8 D_188c8 ltac:(rewrite c_lts_Z by lia; apply Z.ltb_ge; lia).               (* [comment removed for export] *)
      stepn F_188cc D_188cc.                                                                       (* [comment removed for export] *)
      stepiv F_188d0 D_188d0 (Z_to_bv 64 ka) ltac:(gres; rwH; imm_norm; rewrite v_addiw_Z by lia; f_equal; lia). (* [comment removed for export] *)
      stepLD8 F_188d4 D_188d4 (Z_to_bv 64 0).                                                     (* [comment removed for export] *)
      stepn F_188d8 D_188d8; rwH; rewrite (v_subw_Z 2147483647 0) by lia.                        (* [comment removed for export] *)
      stepb_ft F_188dc D_188dc ltac:(rewrite c_lts_Z by lia; apply Z.ltb_ge; lia).               (* [comment removed for export] *)
      stepn F_188e0 D_188e0.                                                                       (* [comment removed for export] *)
      stepLD8 F_188e4 D_188e4 (Z_to_bv 64 0).                                                     (* [comment removed for export] *)
      stepn F_188e8 D_188e8; rewrite (v_addw_Z 0 ka) by lia.                                     (* [comment removed for export] *)
      stepn F_188ec D_188ec; rwH.                                                                  (* [comment removed for export] *)
      stepST F_188f0 D_188f0 (Z_to_bv 64 (sp0 - 3280)) (Z_to_bv 64 ka) ltac:(gres; rwH; sok).    (* [comment removed for export] *)
      stepb_ft F_188f4 D_188f4 ltac:(rwH; rewrite c_lts_Z by lia; apply Z.ltb_ge; lia).          (* [comment removed for export] *)
      stepLD8 F_188f8 D_188f8 (Z_to_bv 64 ka).                                                    (* [comment removed for export] *)
      stepb_ft F_188fc D_188fc ltac:(rwH; rewrite c_lts_Z by lia; apply Z.ltb_ge; lia).          (* [comment removed for export] *)
      stepn F_18900 D_18900.                                                                       (* [comment removed for export] *)
      stepn F_18904 D_18904; rwH.                                                                  (* [comment removed for export] *)
      stepST F_18908 D_18908 (Z_to_bv 64 (sp0 - 3304)) (Z_to_bv 64 0) ltac:(sok).                (* [comment removed for export] *)
      stepb_ft F_1890c D_1890c ltac:(cond_vm).                                                     (* [comment removed for export] *)
      stepLD8 F_18910 D_18910 (Z_to_bv 64 ka).                                                    (* [comment removed for export] *)
      stepb_tk F_18914 D_18914 ltac:(rwH; rewrite c_lts_Z by lia; apply Z.ltb_ge; lia).          (* [comment removed for export] *)
      stepLBU F_18990 D_18990 (Z_to_bv 8 0) ltac:(addr_norm; rdn_solve).                           (* [comment removed for export] *)
      stepn F_18994 D_18994.                                                                       (* [comment removed for export] *)
      stepb_ft F_18998 D_18998 ltac:(apply c_eq_refl).                                             (* [comment removed for export] *)
      stepLD8 F_1899c D_1899c (rl dS_102e7 0x102e7).                                               (* [comment removed for export] *)
      stepLD8 F_189a0 D_189a0 (Z_to_bv 64 0).                                                     (* [comment removed for export] *)
      stepn F_189a4 D_189a4.                                                                       (* [comment removed for export] *)
      stepn F_189a8 D_189a8.                                                                       (* [comment removed for export] *)
      unfold segbM. apply mst_refl.
    - repeat split; gres; rwH; try reflexivity; try bveq.
      intros x Hx. cbv [In] in Hx. repeat (destruct Hx as [<-|Hx]; [gres; reflexivity|]). destruct Hx.
  Qed.

  (* [comment removed for export] *)
  Lemma s_seg_c : forall m4 r,
    FILEc m4 sp0 -> rdn SEGS m4 (Z_to_bv 64 (sp0 - 3296)) 8 = Some (W8 ka) ->
    getr r 2 = Z_to_bv 64 (sp0 - 3312) -> getr r 18 = Z_to_bv 64 0 -> getr r 20 = Z_to_bv 64 (sp0 - 2400) ->
    getr r 23 = Z_to_bv 64 a -> getr r 25 = Z_to_bv 64 ka ->
    exists r',
      msteps SEGS (mkst r (rl dF_17f6c 0x189ac) m4 rom) (mkst r' (rl dF_17b9c 0x17b9c) m4 rom)
      /\ getr r' 1 = (rl dF_17f6c 0x18ad4) /\ getr r' 10 = Z_to_bv 64 a /\ getr r' 11 = Z_to_bv 64 ka
      /\ getr r' 12 = Z_to_bv 64 (sp0 - 2400)
      /\ (forall x : reg, In x [3; 4; 2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr r' x = getr r x).
  Proof.
    intros m4 r FC4 Z16 R2 R18 R20 R23 R25. pose proof Hcsp as Hsp0. lay.
    assert (K0 : (0 <= ka)%Z) by (destruct RS as [K0 _]; exact K0).
    pose proof (Fc_flags _ _ FC4) as Cfl.
    assert (Z16' : rdn SEGS m4 (Z_to_bv 64 (sp0 - 3296)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 ka))).
    { change (word_to_le_bytes 4 (Z_to_bv 64 ka)) with (firstn 4 (W8 ka)). eapply rdn_firstn; [exact Z16 | lia]. }
    eexists. split.
    - stepn F_189ac D_189ac.                                                                       (* [comment removed for export] *)
      stepb_tk F_189b0 D_189b0 ltac:(cond_vm).                                                     (* [comment removed for export] *)
      stepLD F_18a34 D_18a34 (word_to_le_bytes 4 (Z_to_bv 64 ka)) (Z_to_bv 64 ka)
        ltac:(addr_norm; exact Z16') ltac:(apply bytes_le_to_Z_4; unorm; lia).                    (* [comment removed for export] *)
      rewrite (v_lw_small ka) by lia.
      stepb_tk F_18a38 D_18a38 ltac:(rwH; rewrite c_lts_Z by lia; apply Z.ltb_ge; lia).          (* [comment removed for export] *)
      stepLBU F_18ab8 D_18ab8 (Z_to_bv 8 0) ltac:(addr_norm; exact Cfl).                          (* [comment removed for export] *)
      stepn F_18abc D_18abc.                                                                       (* [comment removed for export] *)
      stepb_ft F_18ac0 D_18ac0 ltac:(apply c_eq_refl).                                             (* [comment removed for export] *)
      stepn F_18ac4 D_18ac4.                                                                       (* [comment removed for export] *)
      stepLD8 F_18ac8 D_18ac8 (Z_to_bv 64 ka).                                                    (* [comment removed for export] *)
      stepn F_18acc D_18acc.                                                                       (* [comment removed for export] *)
      stepn F_18ad0 D_18ad0.                                                                       (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; rwH; try reflexivity; try bveq.
      intros x Hx. cbv [In] in Hx. repeat (destruct Hx as [<-|Hx]; [gres; reflexivity|]). destruct Hx.
  Qed.

  (* [comment removed for export] *)
  Lemma s_seg_d : forall m5 r,
    getr r 18 = Z_to_bv 64 0 ->
    exists r',
      msteps SEGS (mkst r (rl dF_17f6c 0x18ad4) m5 rom) (mkst r' (rl dF_17f6c 0x1801c) m5 rom)
      /\ (forall x : reg, x <> 10 -> getr r' x = getr r x).
  Proof.
    intros m5 r R18. eexists. split.
    - stepn F_18ad4 D_18ad4.                                                                       (* [comment removed for export] *)
      stepb_tk F_18ad8 D_18ad8 ltac:(cond_vm).                                                     (* [comment removed for export] *)
      apply mst_refl.
    - intros x Hx. rewrite getr_other by exact Hx. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Theorem conv_s_run : forall m1 r regs (ret : word) (f p cnt' u j apv : Z),
    FRM sp0 mem0 m1 -> PCc m1 sp0 cv regs ret -> FILEc m1 sp0 -> FILEst m1 sp0 u j ->
    rdn SEGS m1 (Z_to_bv 64 (sp0 - 3200)) 8 = Some (X8 (Z_to_bv 64 a)) ->
    rdn SEGS m1 (Z_to_bv 64 (sp0 - 2768)) 8 = Some (W8 apv) ->
    f = (sp0 - 2400)%Z -> (0 <= cnt')%Z -> (cnt' + ka <= INT_MAX)%Z ->
    getr r 2 = Z_to_bv 64 (sp0 - 3312) -> getr r 8 = Z_to_bv 64 37 -> getr r 9 = Z_to_bv 64 INT_MAX ->
    getr r 18 = Z_to_bv 64 (INT_MAX - cnt') -> getr r 19 = Z_to_bv 64 cnt' -> getr r 20 = Z_to_bv 64 f ->
    getr r 21 = Z_to_bv 64 p -> getr r 22 = Z_to_bv 64 0 -> getr r 24 = Z_to_bv 64 0 ->
    getr r 25 = Z_to_bv 64 18446744073709551615 -> getr r 26 = Z_to_bv 64 0 -> getr r 3 = g3 -> getr r 4 = g4 ->
    exists r' m',
      msteps SEGS (mkst r (rl dF_17f6c 0x1854c) m1 rom) (mkst r' (rl dF_17f6c 0x1801c) m' rom)
      /\ (pcR sp0 g3 g4 r' f p cnt' ka
          /\ frame_mod m1 m' (pc_regions sp0)
          /\ (exists u' j', FILEst m' sp0 u' j' /\ (j <= j')%Z)
          /\ rdn SEGS m' (Z_to_bv 64 (sp0 - 2768)) 8 = Some (W8 apv)).
  Proof.
    intros m1 r regs ret f p cnt' u j apv F1 PC1 FC1 FS1 ARG AP2 Hf Hc0 Hck R2 R8 R9 R18 R19 R20 R21 R22 R24 R25 R26 R3 R4.
    pose proof Hcsp as Hsp0. lay. subst f.
    assert (K0 : (0 <= ka)%Z) by (destruct RS as [K0 _]; exact K0).
    pose proof (rostr_range mem0 a ka RS Hka) as RR.
    (* [comment removed for export] *)
    destruct (s_seg_a m1 r ARG R2 R9 R25) as (r1 & RUN1 & Q1 & Q10 & Q11 & Q23 & QK).
    (* [comment removed for export] *)
    destruct (strnlen_rostr sp0 mem0 cv rom CTX a ka RS Hka m1 (sp0 - 3312) r1 (rl dF_17f6c 0x18584) F1 ltac:(lay; lia)
                ltac:(rl_ret_ok) Q1 ltac:(rewrite QK by indec; exact R2) Q10 Q11)
      as (r2 & m2 & RUN2 & K2 & A2 & FM2).
    replace (sp0 - 3312 - 32)%Z with (sp0 - 3344)%Z in FM2 by lia.
    assert (LF2 : low_frame sp0 m1 m2).
    { eapply low_frame_sub; [exact FM2|]. intros x Hx. cbn [outside]. unfold in_rng. unorm. lia. }
    assert (PM2 : frame_mod m1 m2 (pc_regions sp0)).
    { eapply frame_mod_weaken; [|exact FM2]. intros x Ho. unfold pc_regions in Ho. cbn [outside] in Ho |- *.
      unfold in_rng in *. revert Ho. unorm. intros Ho. repeat split; lia. }
    assert (F2 : FRM sp0 mem0 m2) by (eapply FRM_sub; [exact F1 | exact PM2 | apply (pc_regions_sub sp0 mem0 cv CTX)]).
    assert (FC2 : FILEc m2 sp0) by (eapply FILEc_low; [lia | exact FC1 | exact LF2]).
    assert (FS2 : FILEst m2 sp0 u j) by (eapply FILEst_low; [lia | exact FS1 | exact LF2]).
    (* [comment removed for export] *)
    assert (T2 : getr r2 2 = Z_to_bv 64 (sp0 - 3312)) by (rewrite (K2 2%bv) by kept_reg; rewrite QK by indec; exact R2).
    assert (T9 : getr r2 9 = Z_to_bv 64 INT_MAX) by (rewrite (K2 9%bv) by kept_reg; rewrite QK by indec; exact R9).
    assert (T18 : getr r2 18 = Z_to_bv 64 (INT_MAX - cnt')) by (rewrite (K2 18%bv) by kept_reg; rewrite QK by indec; exact R18).
    assert (T20 : getr r2 20 = Z_to_bv 64 (sp0 - 2400)) by (rewrite (K2 20%bv) by kept_reg; rewrite QK by indec; exact R20).
    assert (T22 : getr r2 22 = Z_to_bv 64 0) by (rewrite (K2 22%bv) by kept_reg; rewrite QK by indec; exact R22).
    assert (T23 : getr r2 23 = Z_to_bv 64 a) by (rewrite (K2 23%bv) by kept_reg; exact Q23).
    assert (T25 : getr r2 25 = Z_to_bv 64 18446744073709551615) by (rewrite (K2 25%bv) by kept_reg; rewrite QK by indec; exact R25).
    assert (T26 : getr r2 26 = Z_to_bv 64 0) by (rewrite (K2 26%bv) by kept_reg; rewrite QK by indec; exact R26).
    (* [comment removed for export] *)
    destruct (s_seg_b m2 r2 cnt' F2 FC2 Hc0 Hck T2 T9 A2 T18 T20 T22 T23 T25 T26)
      as (r3 & RUN3 & U1 & U10 & U11 & U12 & U18 & U25 & U26 & U23 & UK).
    set (M3 := segbM m2).
    assert (LF3 : low_frame sp0 m2 M3).
    { unfold M3, segbM. repeat (eapply low_frame_trans; [|apply low_frame_wb; cbn; lia]). apply low_frame_refl. }
    assert (PM3 : frame_mod m2 M3 (pc_regions sp0)).
    { unfold M3, segbM, pc_regions. frame_tac Hsp0. apply frame_mod_refl. }
    assert (F3 : FRM sp0 mem0 M3) by (eapply FRM_sub; [exact F2 | exact PM3 | apply (pc_regions_sub sp0 mem0 cv CTX)]).
    assert (FC3 : FILEc M3 sp0) by (eapply FILEc_low; [lia | exact FC2 | exact LF3]).
    assert (FS3 : FILEst M3 sp0 u j) by (eapply FILEst_low; [lia | exact FS2 | exact LF3]).
    assert (Hbs0 : rdn SEGS M3 (rl dS_102e7 0x102e7) (Z.to_nat 0) = Some []) by reflexivity.
    destruct (fwritex_run sp0 mem0 cv rom CTX M3 (sp0 - 3312) u j (0x102e7 + dS_102e7) 0 [] F3 ltac:(lay; lia) FC3 FS3 ltac:(lia) Hbs0
                ltac:(lay; lia) r3 (rl dF_17f6c 0x189ac) ltac:(rl_ret_ok)
                U1 ltac:(rewrite UK by indec; exact T2) U10 U11 U12)
      as (r4 & m4 & RUN4 & K4 & A4 & [u4 [j4 [FS4 Hj4]]] & FM4).
    assert (PM4 : frame_mod M3 m4 (pc_regions sp0)).
    { eapply frame_mod_weaken; [|exact FM4]. intros x Ho. apply fwx_sub_pc; [lia | exact Ho]. }
    assert (F4 : FRM sp0 mem0 m4) by (eapply FRM_sub; [exact F3 | exact PM4 | apply (pc_regions_sub sp0 mem0 cv CTX)]).
    assert (FC4 : FILEc m4 sp0) by (eapply (FILEc_fwx M3 m4 sp0 (sp0 - 3312)); [lia | lia | exact FC3 | exact FM4]).
    assert (Z16 : rdn SEGS m4 (Z_to_bv 64 (sp0 - 3296)) 8 = Some (W8 ka)).
    { unfold fwx_regions in FM4. frame_rdn_keep FM4. unfold M3, segbM. rdn_solve. }
    (* [comment removed for export] *)
    assert (V2 : getr r4 2 = Z_to_bv 64 (sp0 - 3312)) by (rewrite (K4 2%bv) by kept_reg; rewrite UK by indec; exact T2).
    assert (V18 : getr r4 18 = Z_to_bv 64 0) by (rewrite (K4 18%bv) by kept_reg; exact U18).
    assert (V20 : getr r4 20 = Z_to_bv 64 (sp0 - 2400)) by (rewrite (K4 20%bv) by kept_reg; rewrite UK by indec; exact T20).
    assert (V23 : getr r4 23 = Z_to_bv 64 a) by (rewrite (K4 23%bv) by kept_reg; exact U23).
    assert (V25 : getr r4 25 = Z_to_bv 64 ka) by (rewrite (K4 25%bv) by kept_reg; exact U25).
    (* [comment removed for export] *)
    destruct (s_seg_c m4 r4 FC4 Z16 V2 V18 V20 V23 V25) as (r5 & RUN5 & W1 & W10 & W11 & W12 & WK).
    (* [comment removed for export] *)
    pose proof (rostr_win_ge _ _ _ RS) as WG.
    destruct RS as (K0' & FL & NONE & NZ & ZE & [bsw Hbsw]).
    pose proof (rdn_length _ _ _ _ _ Hbsw) as Lbsw.
    set (bs := firstn (Z.to_nat ka) bsw).
    assert (Hbs : rdn SEGS m4 (Z_to_bv 64 a) (Z.to_nat ka) = Some bs).
    { subst bs. apply (rdn_firstn SEGS m4 (Z.to_nat (rostr_win a ka))); [|lia].
      rewrite (FRM_rdn sp0 mem0 cv CTX m4 a _ F4); [exact Hbsw | lia | lay; lia | lia]. }
    destruct (fwritex_run sp0 mem0 cv rom CTX m4 (sp0 - 3312) u4 j4 a ka bs F4 ltac:(lay; lia) FC4 FS4 ltac:(lia) Hbs
                ltac:(lay; lia) r5 (rl dF_17f6c 0x18ad4) ltac:(rl_ret_ok)
                W1 ltac:(rewrite WK by indec; exact V2) W10 W11 W12)
      as (r6 & m6 & RUN6 & K6 & A6 & [u6 [j6 [FS6 Hj6]]] & FM6).
    assert (PM6 : frame_mod m4 m6 (pc_regions sp0)).
    { eapply frame_mod_weaken; [|exact FM6]. intros x Ho. apply fwx_sub_pc; [lia | exact Ho]. }
    (* [comment removed for export] *)
    assert (X18 : getr r6 18 = Z_to_bv 64 0) by (rewrite (K6 18%bv) by kept_reg; rewrite WK by indec; exact V18).
    destruct (s_seg_d m6 r6 X18) as (r7 & RUN7 & YK).
    exists r7, m6. split.
    - eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUN3|].
      eapply msteps_trans; [exact RUN4|]. eapply msteps_trans; [exact RUN5|]. eapply msteps_trans; [exact RUN6|]. exact RUN7.
    - split; [|split; [|split]].
      + (* [comment removed for export] *)
        unfold pcR.
        assert (E : forall x : reg, In x [3; 4; 2; 8; 9; 19; 20; 21]%bv -> getr r7 x = getr r x).
        { intros x Hx. cbv [In] in Hx.
          repeat (destruct Hx as [<-|Hx];
            [ rewrite YK by (intros E; discriminate E); rewrite (K6 _) by kept_reg; rewrite WK by indec;
              rewrite (K4 _) by kept_reg; rewrite UK by indec; rewrite (K2 _) by kept_reg; rewrite QK by indec; reflexivity |]).
          destruct Hx. }
        rewrite !E by indec.
        repeat split; try assumption.
        rewrite YK by (intros E'; discriminate E'). rewrite (K6 26%bv) by kept_reg.
        rewrite WK by indec. rewrite (K4 26%bv) by kept_reg. exact U26.
      + eapply frame_mod_trans_same; [exact PM2|]. eapply frame_mod_trans_same; [exact PM3|].
        eapply frame_mod_trans_same; [exact PM4 | exact PM6].
      + exists u6, j6. split; [exact FS6 | lia].
      + (* [comment removed for export] *)
        unfold fwx_regions in FM6. frame_rdn_keep FM6.
        unfold fwx_regions in FM4. frame_rdn_keep FM4.
        unfold M3, segbM. repeat rdn_peel1.
        eapply cell_low; [exact LF2 | lia | lia | cbn; lia | exact AP2].
  Qed.
End CS.
