(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require Import PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim RefMemcpyLib.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica Require Import PortLib.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica Require Import SumWalkTac Frame.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Reloc Require Import RelocKit RCode_17000_18000 RCode_18000_19000 RCode_1c000_1d000.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Musl Require Import MuslTac MemcpyBase.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica Require Import PFLib.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Reloc Require Import RelocKit .
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Musl Require Import MuslTac PFBase PFFwx PFCore PFInv PFCoreD.
Import ListNotations.
Open Scope bv_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation W8 v := (word_to_le_bytes 8 (Z_to_bv 64 v)).
Abbreviation W4 v := (word_to_le_bytes 4 (Z_to_bv 64 v)).
Abbreviation X8 w := (word_to_le_bytes 8 w).

Ltac indec := apply in_regs_dec; reflexivity.

Section CD2.
  Context {fx : FPState} {RL : Reloc} {RLC : RelocCode RL} {RLS : RelocSites RL} {RLD : RelocData RL} {RLI : RelocImg RL} {RLW : RelocRW RL RLD} {RLP : RelocPF RL}.
  Variables (sp0 : Z) (mem0 : word -> option byte) (cv : Z) (rom : word -> option byte).
  Hypothesis CTX : ctxH sp0 mem0 cv.
  Let Hcsp : (IMG_TOP + FR <= sp0 <= 0x800000000000)%Z := Csp _ _ _ CTX.
  Ltac sok := soks CTX.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma memset1_run : forall m r (d : Z) (ret : word),
    FRM sp0 mem0 m -> (sp0 - FR <= d /\ d + 1 <= sp0)%Z ->
    ret_ok ret -> getr r 1 = ret -> getr r 10 = Z_to_bv 64 d -> getr r 11 = Z_to_bv 64 48 -> getr r 12 = Z_to_bv 64 1 ->
    exists r',
      msteps SEGS (mkst r (rl dF_1cdb8 0x1cdb8) m rom)
                  (mkst r' ret (wbytes (wbytes m (Z_to_bv 64 d) [Z_to_bv 8 48]) (Z_to_bv 64 d) [Z_to_bv 8 48]) rom)
      /\ (forall x0 : reg, x0 <> 13 -> x0 <> 14 -> getr r' x0 = getr r x0).
  Proof.
    intros m r d ret F Hd Hret H1 H10 H11 H12. pose proof Hcsp as Hsp0. lay.
    eexists. split.
    - stepb_ft F_1cdb8 D_1cdb8 ltac:(cond_vm).                                                    (* [comment removed for export] *)
      stepST F_1cdbc D_1cdbc (Z_to_bv 64 d) (Z_to_bv 64 48) ltac:(sok).                          (* [comment removed for export] *)
      stepiv F_1cdc0 D_1cdc0 (Z_to_bv 64 (d + 1)) ltac:(zval).                                    (* [comment removed for export] *)
      stepn F_1cdc4 D_1cdc4.                                                                       (* [comment removed for export] *)
      stepST F_1cdc8 D_1cdc8 (Z_to_bv 64 d) (Z_to_bv 64 48) ltac:(sok).                          (* [comment removed for export] *)
      stepb_tk F_1cdcc D_1cdcc ltac:(cond_vm).                                                    (* [comment removed for export] *)
      stepret F_1ceac D_1ceac ret ltac:(exact H1).
      change (bv_unsigned (Z_to_bv 64 48)) with 48%Z. apply mst_refl.
    - intros x0 N13 N14. repeat (rewrite getr_other by assumption). reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma int_seg4 : forall m (x pl : Z) (u j : Z) r,
    (0 <= x < 2 ^ 64)%Z -> (pl = 0 \/ pl = 1)%Z ->
    FRM sp0 mem0 m -> FILEc m sp0 -> FILEst m sp0 u j ->
    rdn SEGS m (Z_to_bv 64 (sp0 - 3296)) 8 = Some (W8 (ndz x)) ->
    getr r 2 = Z_to_bv 64 (sp0 - 3312) -> getr r 18 = Z_to_bv 64 0 -> getr r 20 = Z_to_bv 64 (sp0 - 2400) ->
    getr r 25 = Z_to_bv 64 (ndz x + ez x) -> getr r 27 = Z_to_bv 64 (ndz x + ez x) ->
    exists r' m',
      msteps SEGS (mkst r (rl dF_17f6c 0x189ac) m rom) (mkst r' (rl dF_17f6c 0x18ab8) m' rom)
      /\ ((forall x0 : reg, In x0 [3; 4; 2; 8; 9; 19; 20; 21; 23; 26]%bv -> getr r' x0 = getr r x0)
          /\ getr r' 18 = Z_to_bv 64 0
          /\ frame_mod m m' (pc_regions sp0)
          /\ (exists u' j', FILEst m' sp0 u' j' /\ (j <= j')%Z)
          /\ (forall a n vv, (sp0 - 3312 <= a)%Z -> (a + Z.of_nat n <= sp0 - 3136)%Z ->
                 rdn SEGS m (Z_to_bv 64 a) n = Some vv -> rdn SEGS m' (Z_to_bv 64 a) n = Some vv)
          /\ rdn SEGS m' (Z_to_bv 64 (sp0 - 2768)) 8 = rdn SEGS m (Z_to_bv 64 (sp0 - 2768)) 8).
  Proof.
    intros m x pl u j r Hx Hpl F FC FS Z16 R2 R18 R20 R25 R27. pose proof Hcsp as Hsp0. lay.
    pose proof (ndz_range x Hx) as [NR NR1]. pose proof (Fc_flags _ _ FC) as Cfl.
    assert (Z16' : rdn SEGS m (Z_to_bv 64 (sp0 - 3296)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 (ndz x)))).
    { change (word_to_le_bytes 4 (Z_to_bv 64 (ndz x))) with (firstn 4 (W8 (ndz x))).
      apply (rdn_firstn SEGS m 8); [exact Z16 | lia]. }
    destruct (Z.eq_dec x 0) as [X0|X0].
    - (* [comment removed for export] *)
      assert (ND0 : ndz x = 0%Z) by (unfold ndz; subst x; reflexivity).
      assert (EZ1 : ez x = 1%Z) by (unfold ez; subst x; reflexivity).
      rewrite ND0, EZ1 in *. cbn [Z.add] in R25, R27.
      (* [comment removed for export] *)
      assert (S1 : exists r1, msteps SEGS (mkst r (rl dF_17f6c 0x189ac) m rom) (mkst r1 (rl dF_1cdb8 0x1cdb8) m rom)
              /\ getr r1 1 = (rl dF_17f6c 0x18a64) /\ getr r1 10 = Z_to_bv 64 (sp0 - 3136) /\ getr r1 11 = Z_to_bv 64 48
              /\ getr r1 12 = Z_to_bv 64 1 /\ getr r1 24 = Z_to_bv 64 1 /\ getr r1 25 = Z_to_bv 64 0 /\ getr r1 18 = Z_to_bv 64 256
              /\ (forall x0 : reg, In x0 [3; 4; 2; 8; 9; 19; 20; 21; 23; 26]%bv -> getr r1 x0 = getr r x0)).
      { eexists. split.
        - stepn F_189ac D_189ac.                                                                   (* [comment removed for export] *)
          stepb_tk F_189b0 D_189b0 ltac:(cond_vm).                                                 (* [comment removed for export] *)
          stepLD F_18a34 D_18a34 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0)
            ltac:(addr_norm; exact Z16') ltac:(apply bytes_le_to_Z_4; unorm; lia).                (* [comment removed for export] *)
          stepb_ft F_18a38 D_18a38 ltac:(cond_vm).                                                 (* [comment removed for export] *)
          stepn F_18a3c D_18a3c.                                                                   (* [comment removed for export] *)
          stepLD8 F_18a40 D_18a40 (Z_to_bv 64 0).                                                  (* [comment removed for export] *)
          stepn F_18a44 D_18a44; rwH.                                                              (* [comment removed for export] *)
          stepn F_18a48 D_18a48.                                                                   (* [comment removed for export] *)
          stepn F_18a4c D_18a4c.                                                                   (* [comment removed for export] *)
          stepb_tk F_18a50 D_18a50 ltac:(cond_vm).                                                 (* [comment removed for export] *)
          stepiv F_18a58 D_18a58 (Z_to_bv 64 (sp0 - 3136)) ltac:(zval).                            (* [comment removed for export] *)
          stepn F_18a5c D_18a5c.                                                                   (* [comment removed for export] *)
          stepn F_18a60 D_18a60.                                                                   (* [comment removed for export] *)
          apply mst_refl.
        - repeat split; gres; rwH; try reflexivity; try bveq.
          intros x0 Hx0. cbv [In] in Hx0. repeat (destruct Hx0 as [<-|Hx0]; [gres; reflexivity|]). destruct Hx0. }
      destruct S1 as (r1 & RUN1 & Q1 & Q10 & Q11 & Q12 & Q24 & Q25 & Q18 & QK).
      destruct (memset1_run m r1 (sp0 - 3136) (rl dF_17f6c 0x18a64) F ltac:(lay; lia) ltac:(rl_ret_ok) Q1 Q10 Q11 Q12)
        as (r2 & RUN2 & K2).
      set (m2 := wbytes (wbytes m (Z_to_bv 64 (sp0 - 3136)) [Z_to_bv 8 48]) (Z_to_bv 64 (sp0 - 3136)) [Z_to_bv 8 48]).
      assert (LF2 : low_frame sp0 m m2) by (unfold m2; eapply low_frame_trans; apply low_frame_wb; cbn; lia).
      assert (PM2 : frame_mod m m2 (pc_regions sp0)) by (unfold m2, pc_regions; frame_tac Hsp0; apply frame_mod_refl).
      assert (F2 : FRM sp0 mem0 m2) by (eapply FRM_sub; [exact F | exact PM2 | apply (pc_regions_sub sp0 mem0 cv CTX)]).
      assert (FC2 : FILEc m2 sp0) by (eapply FILEc_low; [lia | exact FC | exact LF2]).
      assert (FS2 : FILEst m2 sp0 u j) by (eapply FILEst_low; [lia | exact FS | exact LF2]).
      pose proof (Fc_flags _ _ FC2) as Cfl2.
      (* [comment removed for export] *)
      assert (S3 : exists r3, msteps SEGS (mkst r2 (rl dF_17f6c 0x18a64) m2 rom) (mkst r3 (rl dF_17b9c 0x17b9c) m2 rom)
              /\ getr r3 1 = (rl dF_17f6c 0x18ab8) /\ getr r3 10 = Z_to_bv 64 (sp0 - 3136) /\ getr r3 11 = Z_to_bv 64 1
              /\ getr r3 12 = Z_to_bv 64 (sp0 - 2400) /\ getr r3 18 = Z_to_bv 64 0
              /\ (forall x0 : reg, In x0 [3; 4; 2; 8; 9; 19; 20; 21; 23; 26]%bv -> getr r3 x0 = getr r x0)).
      { assert (T24 : getr r2 24 = Z_to_bv 64 1) by (rewrite K2 by (intros E; discriminate E); exact Q24).
        assert (T18 : getr r2 18 = Z_to_bv 64 256) by (rewrite K2 by (intros E; discriminate E); exact Q18).
        assert (T25 : getr r2 25 = Z_to_bv 64 0) by (rewrite K2 by (intros E; discriminate E); exact Q25).
        assert (T20 : getr r2 20 = Z_to_bv 64 (sp0 - 2400)) by (rewrite K2 by (intros E; discriminate E); rewrite QK by indec; exact R20).
        assert (T2 : getr r2 2 = Z_to_bv 64 (sp0 - 3312)) by (rewrite K2 by (intros E; discriminate E); rewrite QK by indec; exact R2).
        eexists. split.
        - stepb_tk F_18a64 D_18a64 ltac:(cond_vm).                                                 (* [comment removed for export] *)
          stepLBU F_18a98 D_18a98 (Z_to_bv 8 0) ltac:(addr_norm; unfold m2; rdn_solve).             (* [comment removed for export] *)
          stepn F_18a9c D_18a9c.                                                                   (* [comment removed for export] *)
          stepn F_18aa0 D_18aa0.                                                                   (* [comment removed for export] *)
          stepb_ft F_18aa4 D_18aa4 ltac:(apply c_eq_refl).                                         (* [comment removed for export] *)
          stepiv F_18aa8 D_18aa8 (Z_to_bv 64 (sp0 - 3136)) ltac:(zval).                            (* [comment removed for export] *)
          stepn F_18aac D_18aac.                                                                   (* [comment removed for export] *)
          stepn F_18ab0 D_18ab0.                                                                   (* [comment removed for export] *)
          stepn F_18ab4 D_18ab4.                                                                   (* [comment removed for export] *)
          apply mst_refl.
        - repeat split; gres; rwH; try reflexivity; try bveq.
          intros x0 Hx0. pose proof (QK x0 Hx0) as E. cbv [In] in Hx0.
          repeat (destruct Hx0 as [<-|Hx0]; [gres; rewrite K2 by (intros E'; discriminate E'); exact E|]). destruct Hx0. }
      destruct S3 as (r3 & RUN3 & T1 & T10 & T11 & T12 & T18 & TK).
      assert (Hbs : rdn SEGS m2 (Z_to_bv 64 (sp0 - 3136)) (Z.to_nat 1) = Some [Z_to_bv 8 48]).
      { unfold m2. cbn [Z.to_nat Pos.to_nat Pos.iter_op]. apply (rdn_wbytes_hit SEGS [Z_to_bv 8 48]). cbn. unorm. lia. }
      destruct (fwritex_run sp0 mem0 cv rom CTX m2 (sp0 - 3312) u j (sp0 - 3136) 1 [Z_to_bv 8 48] F2 ltac:(lay; lia) FC2 FS2
                  ltac:(lia) Hbs ltac:(lay; lia) r3 (rl dF_17f6c 0x18ab8) ltac:(rl_ret_ok)
                  T1 ltac:(rewrite TK by indec; exact R2) T10 T11 T12)
        as (r4 & m4 & RUN4 & K4 & A4 & [u4 [j4 [FS4 Hj4]]] & FM4).
      exists r4, m4. split.
      + eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|].
        eapply msteps_trans; [exact RUN3|]. exact RUN4.
      + split.
        { intros x0 Hx0. pose proof Hx0 as Hx1. cbv [In] in Hx1.
          repeat (destruct Hx1 as [<-|Hx1]; [rewrite (K4 _) by kept_reg; apply TK; exact Hx0|]). destruct Hx1. }
        split; [rewrite (K4 18%bv) by kept_reg; exact T18|].
        split.
        { eapply frame_mod_trans_same; [exact PM2|]. eapply frame_mod_weaken; [|exact FM4]. intros x0 Ho. apply fwx_sub_pc; [lia | exact Ho]. }
        split; [exists u4, j4; split; [exact FS4 | exact Hj4]|].
        split.
        { intros a n vv Ha Hn RD. unfold fwx_regions in FM4. frame_rdn_keep FM4.
          unfold m2. rewrite !rdn_wbytes_out; [exact RD | cbn; unorm; lia | unorm; lia | cbn; unorm; lia | cbn; unorm; lia | unorm; lia | cbn; unorm; lia]. }
        unfold fwx_regions in FM4. frame_rdn_keep FM4. unfold m2.
        rewrite !rdn_wbytes_out; [reflexivity | cbn; unorm; lia | unorm; lia | cbn; unorm; lia | cbn; unorm; lia | unorm; lia | cbn; unorm; lia].
    - (* [comment removed for export] *)
      specialize (NR1 X0).
      assert (EZ0 : ez x = 0%Z) by (unfold ez; replace (x =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia); reflexivity).
      rewrite EZ0, Z.add_0_r in R25, R27.
      eexists. exists m. split.
      + stepn F_189ac D_189ac.                                                                     (* [comment removed for export] *)
        stepb_tk F_189b0 D_189b0 ltac:(cond_vm).                                                   (* [comment removed for export] *)
        stepLD F_18a34 D_18a34 (word_to_le_bytes 4 (Z_to_bv 64 (ndz x))) (Z_to_bv 64 (ndz x))
          ltac:(addr_norm; exact Z16') ltac:(apply bytes_le_to_Z_4; unorm; lia).                  (* [comment removed for export] *)
        rewrite (v_lw_small (ndz x)) by lia.
        stepb_tk F_18a38 D_18a38 ltac:(rwH; rewrite c_lts_Z by lia; apply Z.ltb_ge; lia).        (* [comment removed for export] *)
        apply mst_refl.
      + split; [intros x0 Hx0; cbv [In] in Hx0; repeat (destruct Hx0 as [<-|Hx0]; [gres; reflexivity|]); destruct Hx0|].
        split; [gres; exact R18|].
        split; [apply frame_mod_refl|].
        split; [exists u, j; split; [exact FS | lia]|].
        split; [intros a n vv Ha Hn RD; exact RD|].
        reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma int_seg5 : forall m (nd : Z) r,
    FILEc m sp0 -> rdn SEGS m (Z_to_bv 64 (sp0 - 3296)) 8 = Some (W8 nd) ->
    getr r 2 = Z_to_bv 64 (sp0 - 3312) -> getr r 20 = Z_to_bv 64 (sp0 - 2400) -> getr r 23 = Z_to_bv 64 (sp0 - 3136 - nd) ->
    exists r',
      msteps SEGS (mkst r (rl dF_17f6c 0x18ab8) m rom) (mkst r' (rl dF_17b9c 0x17b9c) m rom)
      /\ getr r' 1 = (rl dF_17f6c 0x18ad4) /\ getr r' 10 = Z_to_bv 64 (sp0 - 3136 - nd) /\ getr r' 11 = Z_to_bv 64 nd
      /\ getr r' 12 = Z_to_bv 64 (sp0 - 2400)
      /\ (forall x0 : reg, In x0 [3; 4; 2; 8; 9; 18; 19; 20; 21; 26]%bv -> getr r' x0 = getr r x0).
  Proof.
    intros m nd r FC Z16 R2 R20 R23. pose proof Hcsp as Hsp0. lay. pose proof (Fc_flags _ _ FC) as Cfl.
    eexists. split.
    - stepLBU F_18ab8 D_18ab8 (Z_to_bv 8 0) ltac:(addr_norm; exact Cfl).                          (* [comment removed for export] *)
      stepn F_18abc D_18abc.                                                                       (* [comment removed for export] *)
      stepb_ft F_18ac0 D_18ac0 ltac:(apply c_eq_refl).                                             (* [comment removed for export] *)
      stepn F_18ac4 D_18ac4.                                                                       (* [comment removed for export] *)
      stepLD8 F_18ac8 D_18ac8 (Z_to_bv 64 nd).                                                    (* [comment removed for export] *)
      stepn F_18acc D_18acc.                                                                       (* [comment removed for export] *)
      stepn F_18ad0 D_18ad0.                                                                       (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; rwH; try reflexivity; try bveq.
      intros x0 Hx0. cbv [In] in Hx0. repeat (destruct Hx0 as [<-|Hx0]; [gres; reflexivity|]). destruct Hx0.
  Qed.

  Lemma int_seg_d : forall m5 r,
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
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma int_tail : forall mA (x pl cnt' u j apv : Z) r regs ret,
    (0 <= x < 2 ^ 64)%Z -> (pl = 0 \/ pl = 1)%Z -> (0 <= cnt')%Z -> (cnt' + 22 <= INT_MAX)%Z ->
    FRM sp0 mem0 mA -> PCc mA sp0 cv regs ret -> FILEc mA sp0 -> FILEst mA sp0 u j ->
    rdn SEGS mA (Z_to_bv 64 (sp0 - 3200)) 8 = Some (W8 x) ->
    rdn SEGS mA (Z_to_bv 64 (sp0 - 3288)) 8 = Some (W8 pl) ->
    rdn SEGS mA (Z_to_bv 64 (sp0 - 2768)) 8 = Some (W8 apv) ->
    getr r 2 = Z_to_bv 64 (sp0 - 3312) -> getr r 5 = Z_to_bv 64 0 -> getr r 8 = Z_to_bv 64 37 -> getr r 9 = Z_to_bv 64 INT_MAX ->
    getr r 10 = Z_to_bv 64 x -> getr r 14 = Z_to_bv 64 10 -> getr r 17 = rl dS_102e7 0x102e7 ->
    getr r 18 = Z_to_bv 64 (INT_MAX - cnt') -> getr r 19 = Z_to_bv 64 cnt' -> getr r 20 = Z_to_bv 64 (sp0 - 2400) ->
    getr r 22 = Z_to_bv 64 0 -> getr r 24 = Z_to_bv 64 0 -> getr r 25 = Z_to_bv 64 18446744073709551615 ->
    exists r' m',
      msteps SEGS (mkst r (rl dF_17f6c 0x18808) mA rom) (mkst r' (rl dF_17f6c 0x1801c) m' rom)
      /\ ((forall x0 : reg, In x0 [3; 4; 2; 8; 9; 19; 20; 21]%bv -> getr r' x0 = getr r x0)
          /\ getr r' 26 = Z_to_bv 64 (pl + (ndz x + ez x))
          /\ frame_mod mA m' (pc_regions sp0)
          /\ (exists u' j', FILEst m' sp0 u' j' /\ (j <= j')%Z)
          /\ rdn SEGS m' (Z_to_bv 64 (sp0 - 2768)) 8 = Some (W8 apv)).
  Proof.
    intros mA x pl cnt' u j apv r regs ret Hx Hpl Hc0 Hck FA PCA FCA FSA ARG PL AP2
           R2 R5 R8 R9 R10 R14 R17 R18 R19 R20 R22 R24 R25.
    pose proof Hcsp as Hsp0. lay. pose proof (ndz_range x Hx) as [NR NR1].
    assert (HW : (1 <= ndz x + ez x <= 21)%Z).
    { unfold ez. destruct (Z.eqb_spec x 0); [|specialize (NR1 n)]; lia. }
    (* [comment removed for export] *)
    destruct (fmtu_run sp0 mem0 cv rom CTX x (rl dS_102e7 0x102e7) mA r regs ret Hx FA PCA R2 R10 R14 R17)
      as (rB & mB & RUNB & B23 & BK & FMB & B0 & DB).
    assert (LFB : low_frame sp0 mA mB).
    { eapply low_frame_sub; [exact FMB|]. intros x0 Hx0. cbn [outside]. unfold in_rng. unorm. repeat split; lia. }
    assert (PMB : frame_mod mA mB (pc_regions sp0)).
    { eapply frame_mod_weaken; [|exact FMB]. intros x0 Ho. unfold pc_regions in Ho. cbn [outside] in Ho |- *.
      unfold in_rng in *. revert Ho. unorm. intros Ho. repeat split; lia. }
    assert (FB : FRM sp0 mem0 mB) by (eapply FRM_sub; [exact FA | exact PMB | apply (pc_regions_sub sp0 mem0 cv CTX)]).
    assert (FCB : FILEc mB sp0) by (eapply FILEc_low; [lia | exact FCA | exact LFB]).
    assert (FSB : FILEst mB sp0 u j) by (eapply FILEst_low; [lia | exact FSA | exact LFB]).
    assert (ARGB : rdn SEGS mB (Z_to_bv 64 (sp0 - 3200)) 8 = Some (W8 x)) by (frame_rdn_keep FMB; exact ARG).
    assert (PLB : rdn SEGS mB (Z_to_bv 64 (sp0 - 3288)) 8 = Some (W8 pl)) by (frame_rdn_keep FMB; exact PL).
    assert (B2 : getr rB 2 = Z_to_bv 64 (sp0 - 3312)) by (rewrite BK by indec; exact R2).
    assert (B5 : getr rB 5 = Z_to_bv 64 0) by (rewrite BK by indec; exact R5).
    assert (B9 : getr rB 9 = Z_to_bv 64 INT_MAX) by (rewrite BK by indec; exact R9).
    assert (B18 : getr rB 18 = Z_to_bv 64 (INT_MAX - cnt')) by (rewrite BK by indec; exact R18).
    assert (B20 : getr rB 20 = Z_to_bv 64 (sp0 - 2400)) by (rewrite BK by indec; exact R20).
    assert (B22 : getr rB 22 = Z_to_bv 64 0) by (rewrite BK by indec; exact R22).
    assert (B24 : getr rB 24 = Z_to_bv 64 0) by (rewrite BK by indec; exact R24).
    assert (B25 : getr rB 25 = Z_to_bv 64 18446744073709551615) by (rewrite BK by indec; exact R25).
    (* [comment removed for export] *)
    destruct (int_seg3 sp0 mem0 cv rom CTX mB x pl cnt' (rl dS_102e7 0x102e7) rB Hx Hpl Hc0 Hck FB FCB ARGB PLB B0 B2 B5 B9 B18 B20 B22 B23 B24 B25)
      as (rC & RUNC & C1 & C10 & C11 & C12 & C18 & C25 & C27 & C26 & C24 & CK).
    set (mC := seg3M sp0 mB (ndz x) pl (ndz x + ez x)).
    assert (LFC : low_frame sp0 mB mC).
    { unfold mC, seg3M. repeat (eapply low_frame_trans; [|apply low_frame_wb; cbn; lia]). apply low_frame_refl. }
    assert (PMC : frame_mod mB mC (pc_regions sp0)) by (unfold mC, seg3M, pc_regions; frame_tac Hsp0; apply frame_mod_refl).
    assert (FC : FRM sp0 mem0 mC) by (eapply FRM_sub; [exact FB | exact PMC | apply (pc_regions_sub sp0 mem0 cv CTX)]).
    assert (FCC : FILEc mC sp0) by (eapply FILEc_low; [lia | exact FCB | exact LFC]).
    assert (FSC : FILEst mC sp0 u j) by (eapply FILEst_low; [lia | exact FSB | exact LFC]).
    assert (HbsP : exists bsP, rdn SEGS mC (rl dS_102e7 0x102e7) (Z.to_nat pl) = Some bsP).
    { destruct Hpl as [-> | ->].
      - exists []. reflexivity.
      - exists [Z_to_bv 8 45]. change (rl dS_102e7 0x102e7) with (Z_to_bv 64 (0x102e7 + dS_102e7)).
        rewrite (FRM_img sp0 mem0 cv CTX mC _ _ FC); [exact rl_pf_prefix0 | lay; lia | lay; cbn; lia]. }
    destruct HbsP as [bsP HbsP].
    destruct (fwritex_run sp0 mem0 cv rom CTX mC (sp0 - 3312) u j (0x102e7 + dS_102e7) pl bsP FC ltac:(lay; lia) FCC FSC ltac:(lia) HbsP
                ltac:(lay; lia) rC (rl dF_17f6c 0x189ac) ltac:(rl_ret_ok)
                C1 ltac:(rewrite CK by indec; exact B2) C10 C11 C12)
      as (rD & mD & RUND & KD & AD & [uD [jD [FSD HjD]]] & FMD).
    assert (PMD : frame_mod mC mD (pc_regions sp0)).
    { eapply frame_mod_weaken; [|exact FMD]. intros x0 Ho. apply fwx_sub_pc; [lia | exact Ho]. }
    assert (FD : FRM sp0 mem0 mD) by (eapply FRM_sub; [exact FC | exact PMD | apply (pc_regions_sub sp0 mem0 cv CTX)]).
    assert (FCD : FILEc mD sp0) by (eapply (FILEc_fwx mC mD sp0 (sp0 - 3312)); [lia | lia | exact FCC | exact FMD]).
    assert (Z16D : rdn SEGS mD (Z_to_bv 64 (sp0 - 3296)) 8 = Some (W8 (ndz x))).
    { unfold fwx_regions in FMD. frame_rdn_keep FMD. unfold mC, seg3M. rdn_solve. }
    assert (D2 : getr rD 2 = Z_to_bv 64 (sp0 - 3312)) by (rewrite (KD 2%bv) by kept_reg; rewrite CK by indec; exact B2).
    assert (D18 : getr rD 18 = Z_to_bv 64 0) by (rewrite (KD 18%bv) by kept_reg; exact C18).
    assert (D20 : getr rD 20 = Z_to_bv 64 (sp0 - 2400)) by (rewrite (KD 20%bv) by kept_reg; rewrite CK by indec; exact B20).
    assert (D25 : getr rD 25 = Z_to_bv 64 (ndz x + ez x)) by (rewrite (KD 25%bv) by kept_reg; exact C25).
    assert (D27 : getr rD 27 = Z_to_bv 64 (ndz x + ez x)) by (rewrite (KD 27%bv) by kept_reg; exact C27).
    (* [comment removed for export] *)
    destruct (int_seg4 mD x pl uD jD rD Hx Hpl FD FCD FSD Z16D D2 D18 D20 D25 D27)
      as (rE & mE & RUNE & EK & E18 & PME & [uE [jE [FSE HjE]]] & EP & EAP).
    assert (FE : FRM sp0 mem0 mE) by (eapply FRM_sub; [exact FD | exact PME | apply (pc_regions_sub sp0 mem0 cv CTX)]).
    assert (FCE : FILEc mE sp0) by (eapply FILEc_pc; [lia | exact FCD | exact PME]).
    assert (Z16E : rdn SEGS mE (Z_to_bv 64 (sp0 - 3296)) 8 = Some (W8 (ndz x))) by (apply EP; [lia | cbn; lia | exact Z16D]).
    assert (E2 : getr rE 2 = Z_to_bv 64 (sp0 - 3312)) by (rewrite EK by indec; exact D2).
    assert (E20 : getr rE 20 = Z_to_bv 64 (sp0 - 2400)) by (rewrite EK by indec; exact D20).
    assert (E23 : getr rE 23 = Z_to_bv 64 (sp0 - 3136 - ndz x)).
    { rewrite EK by indec. rewrite (KD 23%bv) by kept_reg. rewrite CK by indec. exact B23. }
    (* [comment removed for export] *)
    destruct (int_seg5 mE (ndz x) rE FCE Z16E E2 E20 E23) as (rF & RUNF & F1' & F10 & F11 & F12 & FK).
    (* [comment removed for export] *)
    assert (DE : defined mE (sp0 - 3136 - ndz x) (ndz x)).
    { eapply defined_grows; [| exact DB].
      eapply mem_grows_trans; [destruct PMC as [_ G]; exact G|].
      eapply mem_grows_trans; [destruct PMD as [_ G]; exact G|]. destruct PME as [_ G]; exact G. }
    destruct (rdn_defined SEGS mE (sp0 - 3136 - ndz x) (Z.to_nat (ndz x)) ltac:(lia) ltac:(lia)
                ltac:(intros i Hi; apply DE; lia)) as (bsD & HbsD & LbsD).
    destruct (fwritex_run sp0 mem0 cv rom CTX mE (sp0 - 3312) uE jE (sp0 - 3136 - ndz x) (ndz x) bsD FE ltac:(lay; lia) FCE FSE
                ltac:(lia) HbsD ltac:(lay; lia) rF (rl dF_17f6c 0x18ad4) ltac:(rl_ret_ok)
                F1' ltac:(rewrite FK by indec; exact E2) F10 F11 F12)
      as (rG & mG & RUNG & KG & AG & [uG [jG [FSG HjG]]] & FMG).
    assert (PMG : frame_mod mE mG (pc_regions sp0)).
    { eapply frame_mod_weaken; [|exact FMG]. intros x0 Ho. apply fwx_sub_pc; [lia | exact Ho]. }
    assert (G18 : getr rG 18 = Z_to_bv 64 0) by (rewrite (KG 18%bv) by kept_reg; rewrite FK by indec; exact E18).
    destruct (int_seg_d mG rG G18) as (rH & RUNH & HK).
    exists rH, mG. split.
    - eapply msteps_trans; [exact RUNB|]. eapply msteps_trans; [exact RUNC|]. eapply msteps_trans; [exact RUND|].
      eapply msteps_trans; [exact RUNE|]. eapply msteps_trans; [exact RUNF|]. eapply msteps_trans; [exact RUNG|]. exact RUNH.
    - split.
      { intros x0 Hx0. cbv [In] in Hx0.
        repeat (destruct Hx0 as [<-|Hx0];
          [ rewrite HK by (intros E; discriminate E); rewrite (KG _) by kept_reg; rewrite FK by indec;
            rewrite EK by indec; rewrite (KD _) by kept_reg; rewrite CK by indec; rewrite BK by indec; reflexivity |]).
        destruct Hx0. }
      split.
      { rewrite HK by (intros E; discriminate E). rewrite (KG 26%bv) by kept_reg. rewrite FK by indec.
        rewrite EK by indec. rewrite (KD 26%bv) by kept_reg. exact C26. }
      split.
      { eapply frame_mod_trans_same; [exact PMB|]. eapply frame_mod_trans_same; [exact PMC|].
        eapply frame_mod_trans_same; [exact PMD|]. eapply frame_mod_trans_same; [exact PME | exact PMG]. }
      split; [exists uG, jG; split; [exact FSG | lia]|].
      unfold fwx_regions in FMG. frame_rdn_keep FMG. rewrite EAP.
      unfold fwx_regions in FMD. frame_rdn_keep FMD.
      eapply cell_low; [exact LFC | lia | lia | cbn; lia |].
      eapply cell_low; [exact LFB | lia | lia | cbn; lia | exact AP2].
  Qed.
End CD2.
