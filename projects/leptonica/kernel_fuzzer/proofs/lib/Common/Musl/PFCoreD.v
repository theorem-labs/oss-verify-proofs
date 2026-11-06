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
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Reloc Require Import RelocKit RCode_17000_18000 RCode_18000_19000.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Musl Require Import MuslTac MemcpyBase.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica Require Import PFLib.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Reloc Require Import RelocKit .
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Musl Require Import MuslTac PFBase PFFwx PFCore PFInv.
Import ListNotations.
Open Scope bv_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation W8 v := (word_to_le_bytes 8 (Z_to_bv 64 v)).
Abbreviation W4 v := (word_to_le_bytes 4 (Z_to_bv 64 v)).
Abbreviation X8 w := (word_to_le_bytes 8 w).

(* [comment removed for export] *)
Section GD_1.
  Context {RL : Reloc}.
Definition ndz (x : Z) : Z := if (x =? 0)%Z then 0 else ndig x.
End GD_1.
Arguments ndz _ : simpl never.

Section VP1.
  Context {fx : FPState} {RL : Reloc} {RLC : RelocCode RL} {RLS : RelocSites RL} {RLD : RelocData RL} {RLI : RelocImg RL} {RLW : RelocRW RL RLD} {RLP : RelocPF RL}.
Lemma ndz_range : forall x, (0 <= x < 2 ^ 64)%Z -> (0 <= ndz x <= 20)%Z /\ (x <> 0%Z -> (1 <= ndz x)%Z).
Proof.
  intros x Hx. unfold ndz. pose proof (ndig_range x Hx). destruct (Z.eqb_spec x 0); lia.
Qed.
End VP1.

Section GD_2.
  Context {RL : Reloc}.
Lemma defined_eqn : forall m a n n', defined m a n -> (n' = n)%Z -> defined m a n'.
Proof. intros m a n n' D E. subst n'. exact D. Qed.
End GD_2.

Section CD.
  Context {fx : FPState} {RL : Reloc} {RLC : RelocCode RL} {RLS : RelocSites RL} {RLD : RelocData RL} {RLI : RelocImg RL} {RLW : RelocRW RL RLD} {RLP : RelocPF RL}.
  Variables (sp0 : Z) (mem0 : word -> option byte) (cv : Z) (rom : word -> option byte).
  Hypothesis CTX : ctxH sp0 mem0 cv.
  Let Hcsp : (IMG_TOP + FR <= sp0 <= 0x800000000000)%Z := Csp _ _ _ CTX.
  Ltac sok := soks CTX.

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma fmtu_loop : forall kk (x q : Z) m r,
    (Z.of_nat kk = ndig x)%Z -> (10 <= x < 2 ^ 64)%Z ->
    (sp0 - 3156 + ndig x - 1 <= q <= sp0 - 3136)%Z ->
    FRM sp0 mem0 m ->
    getr r 10 = Z_to_bv 64 x -> getr r 11 = Z_to_bv 64 q -> getr r 14 = Z_to_bv 64 10 ->
    getr r 15 = Z_to_bv 64 18446744072850558157 -> getr r 16 = Z_to_bv 64 99 ->
    exists r' m',
      msteps SEGS (mkst r (rl dF_17f6c 0x18818) m rom) (mkst r' (rl dF_17f6c 0x18850) m' rom)
      /\ ((exists y, (1 <= y <= 9)%Z /\ getr r' 10 = Z_to_bv 64 y)
          /\ getr r' 23 = Z_to_bv 64 (q - (ndig x - 1))
          /\ (forall x0 : reg, In x0 [3; 4; 2; 5; 8; 9; 17; 18; 19; 20; 21; 22; 24; 25; 26; 27]%bv -> getr r' x0 = getr r x0)
          /\ frame_mod m m' [(Z_to_bv 64 (sp0 - 3156), 20%Z)]
          /\ defined m' (q - (ndig x - 1)) (ndig x - 1)).
  Proof.
    pose proof Hcsp as Hsp0. lay.
    induction kk as [|kk IH]; intros x q m r Hkk Hx Hq F R10 R11 R14 R15 R16.
    { exfalso. pose proof (ndig_range x ltac:(lia)). lia. }
    pose proof (ndig_step x ltac:(lia)) as ND.
    pose proof (Z.div_mod x 10 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound x 10 ltac:(lia)) as MB.
    assert (Hq10 : (1 <= x / 10 < 2 ^ 64)%Z) by (split; [apply Z.div_le_lower_bound; lia | apply Z.div_lt_upper_bound; lia]).
    pose proof (ndig_range (x / 10) ltac:(lia)) as NR.
    (* [comment removed for export] *)
    assert (STEP : exists r1,
      msteps SEGS (mkst r (rl dF_17f6c 0x18818) m rom)
                  (mkst r1 (rl dF_17f6c 0x18844) (wbytes m (Z_to_bv 64 (q - 1)) [Z_to_bv 8 (48 + x mod 10)]) rom)
      /\ getr r1 10 = Z_to_bv 64 (x / 10) /\ getr r1 11 = Z_to_bv 64 (q - 1) /\ getr r1 12 = Z_to_bv 64 x
      /\ getr r1 23 = Z_to_bv 64 (q - 1) /\ getr r1 14 = Z_to_bv 64 10
      /\ getr r1 15 = Z_to_bv 64 18446744072850558157 /\ getr r1 16 = Z_to_bv 64 99
      /\ (forall x0 : reg, In x0 [3; 4; 2; 5; 8; 9; 17; 18; 19; 20; 21; 22; 24; 25; 26; 27]%bv -> getr r1 x0 = getr r x0)).
    { eexists. split.
      - stepn F_18818 D_18818.                                                                     (* [comment removed for export] *)
        stepn F_1881c D_1881c; rwH.                                                                (* [comment removed for export] *)
        stepiv F_18820 D_18820 (Z_to_bv 64 MAGIC10) ltac:(gres; rwH; bveq).                      (* [comment removed for export] *)
        stepn F_18824 D_18824; rwH.                                                                (* [comment removed for export] *)
        stepn F_18828 D_18828. rewrite (fmtu_q x) by lia.                                          (* [comment removed for export] *)
        stepn F_1882c D_1882c; rwH.                                                                (* [comment removed for export] *)
        stepn F_18830 D_18830; rwH.                                                                (* [comment removed for export] *)
        stepn F_18834 D_18834. rewrite (fmtu_r x) by lia.                                          (* [comment removed for export] *)
        stepiv F_18838 D_18838 (Z_to_bv 64 (q - 1)) ltac:(zval).                                  (* [comment removed for export] *)
        stepST F_1883c D_1883c (Z_to_bv 64 (q - 1)) (Z_to_bv 64 (48 + x mod 10)) ltac:(sok).     (* [comment removed for export] *)
        stepn F_18840 D_18840.                                                                     (* [comment removed for export] *)
        rewrite (u_Z2bv (48 + x mod 10)) by lia.
        apply mst_refl.
      - repeat split; gres; rwH; try reflexivity.
        intros x0 Hx0. cbv [In] in Hx0. repeat (destruct Hx0 as [<-|Hx0]; [gres; reflexivity|]). destruct Hx0. }
    destruct STEP as (r1 & RUN1 & Q10 & Q11 & Q12 & Q23 & Q14 & Q15 & Q16 & QK).
    set (m1 := wbytes m (Z_to_bv 64 (q - 1)) [Z_to_bv 8 (48 + x mod 10)]) in *.
    assert (FM1 : frame_mod m m1 [(Z_to_bv 64 (sp0 - 3156), 20%Z)]).
    { unfold m1. frame_tac Hsp0. apply frame_mod_refl. }
    assert (F1 : FRM sp0 mem0 m1).
    { eapply FRM_sub; [exact F | exact FM1 |]. intros a0 Ho. cbn [outside] in Ho |- *. unfold in_rng in *. lay.
      revert Ho. unorm. intros Ho. repeat split; lia. }
    assert (D1 : defined m1 (q - 1) 1).
    { unfold m1. apply (defined_wbytes m (q - 1) [Z_to_bv 8 (48 + x mod 10)]); cbn; lia. }
    destruct (Z_lt_le_dec 99 x) as [Hbig|Hsmall].
    - (* [comment removed for export] *)
      assert (Hkk' : Z.of_nat kk = ndig (x / 10)) by lia.
      assert (Hx' : (10 <= x / 10 < 2 ^ 64)%Z) by (split; [apply Z.div_le_lower_bound; lia | lia]).
      pose proof (ndig_ge2 (x / 10) ltac:(lia)) as G2.
      destruct (IH (x / 10)%Z (q - 1)%Z m1 r1 Hkk' Hx' ltac:(lia) F1 Q10 Q11 Q14 Q15 Q16)
        as (r2 & m2 & RUN2 & (y & Hy & Y10) & Y23 & YK & FM2 & D2).
      exists r2, m2. split.
      + eapply msteps_trans; [exact RUN1|].
        stepb_tk F_18844 D_18844 ltac:(rwH; rewrite c_ltu_Z by lia; apply Z.ltb_lt; lia).      (* [comment removed for export] *)
        exact RUN2.
      + split; [exists y; split; [exact Hy | exact Y10]|].
        split; [rewrite Y23; f_equal; lia|].
        split; [intros x0 Hx0; rewrite (YK x0 Hx0); apply QK; exact Hx0|].
        split; [eapply frame_mod_trans_same; [exact FM1 | exact FM2]|].
        replace (ndig x - 1)%Z with ((ndig (x / 10) - 1) + 1)%Z by lia.
        replace (q - (ndig (x / 10) - 1 + 1))%Z with (q - 1 - (ndig (x / 10) - 1))%Z by lia.
        apply defined_app; [exact D2 | | lia].
        replace (q - 1 - (ndig (x / 10) - 1) + (ndig (x / 10) - 1))%Z with (q - 1)%Z by lia.
        eapply defined_grows; [| exact D1]. destruct FM2 as [_ G]. exact G.
    - (* [comment removed for export] *)
      assert (ND1 : ndig (x / 10) = 1%Z) by (apply ndig_small; apply Z.div_lt_upper_bound; lia).
      eexists. exists m1. split.
      + eapply msteps_trans; [exact RUN1|].
        stepb_ft F_18844 D_18844 ltac:(rwH; rewrite c_ltu_Z by lia; apply Z.ltb_ge; lia).      (* [comment removed for export] *)
        stepn F_18848 D_18848.                                                                     (* [comment removed for export] *)
        apply mst_refl.
      + split; [exists (x / 10)%Z; split; [lia | gres; exact Q10]|].
        split; [gres; rewrite Q23; f_equal; lia|].
        split; [intros x0 Hx0; gres; apply QK; exact Hx0|].
        split; [exact FM1|].
        replace (ndig x - 1)%Z with 1%Z by lia. exact D1.
  Qed.

  (* [comment removed for export] *)
  Lemma fmtu_run : forall (x : Z) (pfx : word) m r regs ret,
    (0 <= x < 2 ^ 64)%Z -> FRM sp0 mem0 m -> PCc m sp0 cv regs ret ->
    getr r 2 = Z_to_bv 64 (sp0 - 3312) -> getr r 10 = Z_to_bv 64 x -> getr r 14 = Z_to_bv 64 10 -> getr r 17 = pfx ->
    exists r' m',
      msteps SEGS (mkst r (rl dF_17f6c 0x18808) m rom) (mkst r' (rl dF_17f6c 0x18868) m' rom)
      /\ (getr r' 23 = Z_to_bv 64 (sp0 - 3136 - ndz x)
          /\ (forall x0 : reg, In x0 [3; 4; 2; 5; 8; 9; 18; 19; 20; 21; 22; 24; 25; 26; 27]%bv -> getr r' x0 = getr r x0)
          /\ frame_mod m m' [(Z_to_bv 64 (sp0 - 3156), 20%Z); (Z_to_bv 64 (sp0 - 3312), 8%Z)]
          /\ rdn SEGS m' (Z_to_bv 64 (sp0 - 3312)) 8 = Some (X8 pfx)
          /\ defined m' (sp0 - 3136 - ndz x) (ndz x)).
  Proof.
    intros x pfx m r regs ret Hx F PC R2 R10 R14 R17. pose proof Hcsp as Hsp0. lay.
    pose proof (Pc40 _ _ _ _ _ PC) as C40. pose proof (ndig_range x Hx) as NR.
    destruct (Z_lt_le_dec x 10) as [Hsmall|Hbig].
    - (* [comment removed for export] *)
      assert (ND : ndz x = (if (x =? 0)%Z then 0 else 1)%Z).
      { unfold ndz. destruct (Z.eqb_spec x 0); [reflexivity|]. apply ndig_small. lia. }
      destruct (Z.eq_dec x 0) as [X0|X0].
      + (* [comment removed for export] *)
        rewrite ND. replace (x =? 0)%Z with true by (symmetry; apply Z.eqb_eq; lia). rewrite Z.sub_0_r.
        eexists. eexists. split.
        * stepLD8 F_18808 D_18808 (Z_to_bv 64 18446744072850558157).                              (* [comment removed for export] *)
          stepn F_1880c D_1880c.                                                                   (* [comment removed for export] *)
          stepb_tk F_18810 D_18810 ltac:(rwH; rewrite c_ltu_Z by lia; apply Z.ltb_lt; lia).    (* [comment removed for export] *)
          stepiv F_1884c D_1884c (Z_to_bv 64 (sp0 - 3136)) ltac:(zval).                           (* [comment removed for export] *)
          stepST F_18850 D_18850 (Z_to_bv 64 (sp0 - 3312)) pfx ltac:(sok).                        (* [comment removed for export] *)
          stepb_tk F_18854 D_18854 ltac:(rwH; subst x; apply c_eq_refl).                          (* [comment removed for export] *)
          apply mst_refl.
        * split; [gres; reflexivity|].
          split; [intros x0 Hx0; cbv [In] in Hx0; repeat (destruct Hx0 as [<-|Hx0]; [gres; reflexivity|]); destruct Hx0|].
          split; [frame_tac Hsp0; apply frame_mod_refl|].
          split; [rdn_solve|]. apply defined_0.
      + (* [comment removed for export] *)
        rewrite ND. replace (x =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia).
        eexists. eexists. split.
        * stepLD8 F_18808 D_18808 (Z_to_bv 64 18446744072850558157).                              (* [comment removed for export] *)
          stepn F_1880c D_1880c.                                                                   (* [comment removed for export] *)
          stepb_tk F_18810 D_18810 ltac:(rwH; rewrite c_ltu_Z by lia; apply Z.ltb_lt; lia).    (* [comment removed for export] *)
          stepiv F_1884c D_1884c (Z_to_bv 64 (sp0 - 3136)) ltac:(zval).                           (* [comment removed for export] *)
          stepST F_18850 D_18850 (Z_to_bv 64 (sp0 - 3312)) pfx ltac:(sok).                        (* [comment removed for export] *)
          stepb_ft F_18854 D_18854 ltac:(rwH; rewrite c_eq_Z by lia; apply Z.eqb_neq; lia).      (* [comment removed for export] *)
          stepn F_18858 D_18858; rwH. rewrite (v_ori48 x) by lia.                                (* [comment removed for export] *)
          stepiv F_1885c D_1885c (Z_to_bv 64 (sp0 - 3136 - 1)) ltac:(zval).                       (* [comment removed for export] *)
          stepST F_18860 D_18860 (Z_to_bv 64 (sp0 - 3136 - 1)) (Z_to_bv 64 (48 + x)) ltac:(sok). (* [comment removed for export] *)
          stepn F_18864 D_18864.                                                                   (* [comment removed for export] *)
          rewrite (u_Z2bv (48 + x)) by lia.
          apply mst_refl.
        * split; [gres; reflexivity|].
          split; [intros x0 Hx0; cbv [In] in Hx0; repeat (destruct Hx0 as [<-|Hx0]; [gres; reflexivity|]); destruct Hx0|].
          split; [frame_tac Hsp0; apply frame_mod_refl|].
          split; [rdn_solve|].
          apply (defined_wbytes _ (sp0 - 3136 - 1) [Z_to_bv 8 (48 + x)]); cbn; lia.
    - (* [comment removed for export] *)
      assert (ND : ndz x = ndig x).
      { unfold ndz. replace (x =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
      rewrite ND. pose proof (ndig_ge2 x ltac:(lia)) as G2.
      assert (S1 : exists r1, msteps SEGS (mkst r (rl dF_17f6c 0x18808) m rom) (mkst r1 (rl dF_17f6c 0x18818) m rom)
              /\ getr r1 10 = Z_to_bv 64 x /\ getr r1 11 = Z_to_bv 64 (sp0 - 3136) /\ getr r1 14 = Z_to_bv 64 10
              /\ getr r1 15 = Z_to_bv 64 18446744072850558157 /\ getr r1 16 = Z_to_bv 64 99 /\ getr r1 17 = pfx
              /\ (forall x0 : reg, In x0 [3; 4; 2; 5; 8; 9; 18; 19; 20; 21; 22; 24; 25; 26; 27]%bv -> getr r1 x0 = getr r x0)).
      { eexists. split.
        - stepLD8 F_18808 D_18808 (Z_to_bv 64 18446744072850558157).                              (* [comment removed for export] *)
          stepn F_1880c D_1880c.                                                                   (* [comment removed for export] *)
          stepb_ft F_18810 D_18810 ltac:(rwH; rewrite c_ltu_Z by lia; apply Z.ltb_ge; lia).    (* [comment removed for export] *)
          stepiv F_18814 D_18814 (Z_to_bv 64 (sp0 - 3136)) ltac:(zval).                           (* [comment removed for export] *)
          apply mst_refl.
        - repeat split; gres; rwH; try reflexivity.
          intros x0 Hx0. cbv [In] in Hx0. repeat (destruct Hx0 as [<-|Hx0]; [gres; reflexivity|]). destruct Hx0. }
      destruct S1 as (r1 & RUN1 & Q10 & Q11 & Q14 & Q15 & Q16 & Q17 & QK).
      destruct (fmtu_loop (Z.to_nat (ndig x)) x (sp0 - 3136) m r1 ltac:(lia) ltac:(lia) ltac:(lia) F Q10 Q11 Q14 Q15 Q16)
        as (r2 & m2 & RUN2 & (y & Hy & Y10) & Y23 & YK & FM2 & D2).
      assert (F2 : FRM sp0 mem0 m2).
      { eapply FRM_sub; [exact F | exact FM2 |]. intros a0 Ho. cbn [outside] in Ho |- *. unfold in_rng in *. lay.
        revert Ho. unorm. intros Ho. repeat split; lia. }
      assert (Y17 : getr r2 17 = pfx) by (rewrite (YK 17%bv) by (cbv; tauto); exact Q17).
      assert (Y2 : getr r2 2 = Z_to_bv 64 (sp0 - 3312)) by (rewrite (YK 2%bv) by (cbv; tauto); rewrite QK by (cbv; tauto); exact R2).
      eexists. eexists. split.
      + eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|].
        stepST F_18850 D_18850 (Z_to_bv 64 (sp0 - 3312)) pfx ltac:(sok).                          (* [comment removed for export] *)
        stepb_ft F_18854 D_18854 ltac:(rwH; rewrite c_eq_Z by lia; apply Z.eqb_neq; lia).        (* [comment removed for export] *)
        stepn F_18858 D_18858; rwH. rewrite (v_ori48 y) by lia.                                  (* [comment removed for export] *)
        stepiv F_1885c D_1885c (Z_to_bv 64 (sp0 - 3136 - ndig x)) ltac:(zval).                    (* [comment removed for export] *)
        stepST F_18860 D_18860 (Z_to_bv 64 (sp0 - 3136 - ndig x)) (Z_to_bv 64 (48 + y)) ltac:(sok).  (* [comment removed for export] *)
        stepn F_18864 D_18864.                                                                     (* [comment removed for export] *)
        rewrite (u_Z2bv (48 + y)) by lia.
        apply mst_refl.
      + split; [gres; reflexivity|].
        split.
        { intros x0 Hx0. pose proof Hx0 as Hx1. cbv [In] in Hx1.
          repeat (destruct Hx1 as [<-|Hx1]; [gres; rewrite (YK _) by (cbv [In]; tauto); apply QK; exact Hx0|]). destruct Hx1. }
        split.
        { frame_tac Hsp0. eapply frame_mod_weaken; [|exact FM2]. intros a0 Ho. cbn [outside] in Ho |- *. tauto. }
        split; [rdn_solve|].
        apply (defined_eqn _ _ (1 + (ndig x - 1))%Z); [|lia].
        apply defined_app; [| |lia].
        * apply (defined_wbytes _ (sp0 - 3136 - ndig x) [Z_to_bv 8 (48 + y)]); cbn; lia.
        * replace (sp0 - 3136 - ndig x + 1)%Z with (sp0 - 3136 - (ndig x - 1))%Z by lia.
          eapply defined_grows; [| exact D2].
          eapply mem_grows_trans; apply wbytes_grows.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma int_entry_d : forall m (v : word) r,
    FRM sp0 mem0 m ->
    rdn SEGS m (Z_to_bv 64 (sp0 - 3200)) 8 = Some (X8 v) ->
    getr r 2 = Z_to_bv 64 (sp0 - 3312) -> getr r 24 = Z_to_bv 64 0 ->
    exists r' m' (x pl : Z),
      msteps SEGS (mkst r (rl dF_17f6c 0x18504) m rom) (mkst r' (rl dF_17f6c 0x18808) m' rom)
      /\ ((0 <= x < 2 ^ 64)%Z /\ (pl = 0 \/ pl = 1)%Z
          /\ getr r' 10 = Z_to_bv 64 x /\ getr r' 14 = Z_to_bv 64 10 /\ getr r' 17 = rl dS_102e7 0x102e7
          /\ (forall x0 : reg, In x0 [3; 4; 2; 5; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr r' x0 = getr r x0)
          /\ low_frame sp0 m m' /\ frame_mod m m' (pc_regions sp0)
          /\ rdn SEGS m' (Z_to_bv 64 (sp0 - 3288)) 8 = Some (W8 pl)
          /\ rdn SEGS m' (Z_to_bv 64 (sp0 - 3200)) 8 = Some (W8 x)
          /\ (forall a n vv, (sp0 - 3280 <= a)%Z -> (a + Z.of_nat n <= sp0 - 3200)%Z ->
                 rdn SEGS m (Z_to_bv 64 a) n = Some vv -> rdn SEGS m' (Z_to_bv 64 a) n = Some vv)).
  Proof.
    intros m v r F ARG R2 R24. pose proof Hcsp as Hsp0. lay. pose proof (u64_range v) as Hv.
    destruct (Z_lt_le_dec (bv_unsigned v) (2 ^ 63)) as [POS|NEG].
    - (* [comment removed for export] *)
      eexists. exists (wbytes m (Z_to_bv 64 (sp0 - 3288)) (W8 0)). exists (bv_unsigned v), 0%Z. split.
      + stepLD8 F_18504 D_18504 v.                                                                (* [comment removed for export] *)
        stepb_ft F_18508 D_18508 ltac:(apply c_lts_pos_0; lia).                                    (* [comment removed for export] *)
        stepn F_1850c D_1850c.                                                                     (* [comment removed for export] *)
        stepn F_18510 D_18510; rwH.                                                                (* [comment removed for export] *)
        stepn F_18514 D_18514.                                                                     (* [comment removed for export] *)
        stepn F_18518 D_18518.                                                                     (* [comment removed for export] *)
        stepb_ft F_1851c D_1851c ltac:(cond_vm).                                                   (* [comment removed for export] *)
        stepn F_18520 D_18520; rwH.                                                                (* [comment removed for export] *)
        stepST F_18524 D_18524 (Z_to_bv 64 (sp0 - 3288)) (Z_to_bv 64 0) ltac:(sok).              (* [comment removed for export] *)
        stepn F_18528 D_18528.                                                                     (* [comment removed for export] *)
        stepn F_1852c D_1852c.                                                                     (* [comment removed for export] *)
        stepn F_18530 D_18530.                                                                     (* [comment removed for export] *)
        apply mst_refl.
      + split; [lia|]. split; [lia|]. split; [gres; symmetry; apply Z_to_bv_bv_unsigned|]. split; [gres; reflexivity|].
        split; [gres; reflexivity|].
        split; [intros x0 Hx0; cbv [In] in Hx0; repeat (destruct Hx0 as [<-|Hx0]; [gres; reflexivity|]); destruct Hx0|].
        split; [apply low_frame_wb; cbn; lia|].
        split; [unfold pc_regions; frame_tac Hsp0; apply frame_mod_refl|].
        split; [rdn_solve|].
        split; [rdn_peel1; rewrite Z_to_bv_bv_unsigned; exact ARG|].
        intros a n vv Ha Hn RD. rewrite rdn_wbytes_out; [exact RD | zlen; unorm; lia | unorm; lia | zlen; unorm; lia].
    - (* [comment removed for export] *)
      eexists. exists (wbytes (wbytes m (Z_to_bv 64 (sp0 - 3288)) (W8 1)) (Z_to_bv 64 (sp0 - 3200)) (W8 (2 ^ 64 - bv_unsigned v))).
      exists (2 ^ 64 - bv_unsigned v)%Z, 1%Z. split.
      + stepLD8 F_18504 D_18504 v.                                                                (* [comment removed for export] *)
        stepb_tk F_18508 D_18508 ltac:(apply c_lts_neg_0; lia).                                    (* [comment removed for export] *)
        stepiv F_187dc D_187dc (Z_to_bv 64 (2 ^ 64 - bv_unsigned v))
          ltac:(gres; rewrite v_sub_0_neg; apply bv_eq; rewrite (u_neg_small (bv_unsigned v)) by lia;
                rewrite u_Z2bv by lia; reflexivity).                                               (* [comment removed for export] *)
        stepn F_187e0 D_187e0.                                                                     (* [comment removed for export] *)
        stepST F_187e4 D_187e4 (Z_to_bv 64 (sp0 - 3288)) (Z_to_bv 64 1) ltac:(sok).              (* [comment removed for export] *)
        stepn F_187e8 D_187e8.                                                                     (* [comment removed for export] *)
        stepST F_187ec D_187ec (Z_to_bv 64 (sp0 - 3200)) (Z_to_bv 64 (2 ^ 64 - bv_unsigned v)) ltac:(sok).  (* [comment removed for export] *)
        stepn F_187f0 D_187f0.                                                                     (* [comment removed for export] *)
        stepn F_187f4 D_187f4.                                                                     (* [comment removed for export] *)
        stepn F_187f8 D_187f8.                                                                     (* [comment removed for export] *)
        apply mst_refl.
      + split; [lia|]. split; [lia|]. split; [gres; reflexivity|]. split; [gres; reflexivity|].
        split; [gres; reflexivity|].
        split; [intros x0 Hx0; cbv [In] in Hx0; repeat (destruct Hx0 as [<-|Hx0]; [gres; reflexivity|]); destruct Hx0|].
        split; [eapply low_frame_trans; apply low_frame_wb; cbn; lia|].
        split; [unfold pc_regions; frame_tac Hsp0; apply frame_mod_refl|].
        split; [rdn_solve|].
        split; [rdn_solve|].
        intros a n vv Ha Hn RD. rewrite !rdn_wbytes_out; [exact RD | zlen; unorm; lia | unorm; lia | zlen; unorm; lia
                                                              | zlen; unorm; lia | unorm; lia | zlen; unorm; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma int_entry_u : forall m (v : word) r,
    FRM sp0 mem0 m ->
    rdn SEGS m (Z_to_bv 64 (sp0 - 3200)) 8 = Some (X8 v) ->
    getr r 2 = Z_to_bv 64 (sp0 - 3312) ->
    exists r' m' (x pl : Z),
      msteps SEGS (mkst r (rl dF_17f6c 0x1863c) m rom) (mkst r' (rl dF_17f6c 0x18808) m' rom)
      /\ ((0 <= x < 2 ^ 64)%Z /\ (pl = 0 \/ pl = 1)%Z
          /\ getr r' 10 = Z_to_bv 64 x /\ getr r' 14 = Z_to_bv 64 10 /\ getr r' 17 = rl dS_102e7 0x102e7
          /\ (forall x0 : reg, In x0 [3; 4; 2; 5; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr r' x0 = getr r x0)
          /\ low_frame sp0 m m' /\ frame_mod m m' (pc_regions sp0)
          /\ rdn SEGS m' (Z_to_bv 64 (sp0 - 3288)) 8 = Some (W8 pl)
          /\ rdn SEGS m' (Z_to_bv 64 (sp0 - 3200)) 8 = Some (W8 x)
          /\ (forall a n vv, (sp0 - 3280 <= a)%Z -> (a + Z.of_nat n <= sp0 - 3200)%Z ->
                 rdn SEGS m (Z_to_bv 64 a) n = Some vv -> rdn SEGS m' (Z_to_bv 64 a) n = Some vv)).
  Proof.
    intros m v r F ARG R2. pose proof Hcsp as Hsp0. lay. pose proof (u64_range v) as Hv.
    eexists. exists (wbytes m (Z_to_bv 64 (sp0 - 3288)) (W8 0)). exists (bv_unsigned v), 0%Z. split.
    - stepST F_1863c D_1863c (Z_to_bv 64 (sp0 - 3288)) (Z_to_bv 64 0) ltac:(sok).                (* [comment removed for export] *)
      stepLD8 F_18640 D_18640 v.                                                                  (* [comment removed for export] *)
      stepn F_18644 D_18644.                                                                       (* [comment removed for export] *)
      stepn F_18648 D_18648.                                                                       (* [comment removed for export] *)
      stepn F_1864c D_1864c.                                                                       (* [comment removed for export] *)
      stepn F_18650 D_18650.                                                                       (* [comment removed for export] *)
      apply mst_refl.
    - split; [lia|]. split; [lia|]. split; [gres; symmetry; apply Z_to_bv_bv_unsigned|]. split; [gres; reflexivity|].
      split; [gres; reflexivity|].
      split; [intros x0 Hx0; cbv [In] in Hx0; repeat (destruct Hx0 as [<-|Hx0]; [gres; reflexivity|]); destruct Hx0|].
      split; [apply low_frame_wb; cbn; lia|].
      split; [unfold pc_regions; frame_tac Hsp0; apply frame_mod_refl|].
      split; [rdn_solve|].
      split; [rdn_peel1; rewrite Z_to_bv_bv_unsigned; exact ARG|].
      intros a n vv Ha Hn RD. rewrite rdn_wbytes_out; [exact RD | zlen; unorm; lia | unorm; lia | zlen; unorm; lia].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition ez (x : Z) : Z := if (x =? 0)%Z then 1 else 0.

  Definition seg3M (m : word -> option byte) (nd pl P : Z) : word -> option byte :=
    wbytes (wbytes (wbytes m
      (Z_to_bv 64 (sp0 - 3296)) (W8 nd))                (* [comment removed for export] *)
      (Z_to_bv 64 (sp0 - 3280)) (W8 (pl + P)))          (* [comment removed for export] *)
      (Z_to_bv 64 (sp0 - 3304)) (W8 0).                 (* [comment removed for export] *)

  Lemma int_seg3 : forall m (x pl cnt' : Z) (pfx : word) r,
    (0 <= x < 2 ^ 64)%Z -> (pl = 0 \/ pl = 1)%Z -> (0 <= cnt')%Z -> (cnt' + 22 <= INT_MAX)%Z ->
    FRM sp0 mem0 m -> FILEc m sp0 ->
    rdn SEGS m (Z_to_bv 64 (sp0 - 3200)) 8 = Some (W8 x) ->
    rdn SEGS m (Z_to_bv 64 (sp0 - 3288)) 8 = Some (W8 pl) ->
    rdn SEGS m (Z_to_bv 64 (sp0 - 3312)) 8 = Some (X8 pfx) ->
    getr r 2 = Z_to_bv 64 (sp0 - 3312) -> getr r 5 = Z_to_bv 64 0 -> getr r 9 = Z_to_bv 64 INT_MAX ->
    getr r 18 = Z_to_bv 64 (INT_MAX - cnt') -> getr r 20 = Z_to_bv 64 (sp0 - 2400) -> getr r 22 = Z_to_bv 64 0 ->
    getr r 23 = Z_to_bv 64 (sp0 - 3136 - ndz x) -> getr r 24 = Z_to_bv 64 0 ->
    getr r 25 = Z_to_bv 64 18446744073709551615 ->
    exists r',
      msteps SEGS (mkst r (rl dF_17f6c 0x18868) m rom) (mkst r' (rl dF_17b9c 0x17b9c) (seg3M m (ndz x) pl (ndz x + ez x)) rom)
      /\ getr r' 1 = (rl dF_17f6c 0x189ac) /\ getr r' 10 = pfx /\ getr r' 11 = Z_to_bv 64 pl /\ getr r' 12 = Z_to_bv 64 (sp0 - 2400)
      /\ getr r' 18 = Z_to_bv 64 0 /\ getr r' 25 = Z_to_bv 64 (ndz x + ez x) /\ getr r' 27 = Z_to_bv 64 (ndz x + ez x)
      /\ getr r' 26 = Z_to_bv 64 (pl + (ndz x + ez x)) /\ getr r' 24 = Z_to_bv 64 0
      /\ (forall x0 : reg, In x0 [3; 4; 2; 8; 9; 19; 20; 21; 23]%bv -> getr r' x0 = getr r x0).
  Proof.
    intros m x pl cnt' pfx r Hx Hpl Hc0 Hck F FC ARG PL PFX R2 R5 R9 R18 R20 R22 R23 R24 R25.
    pose proof Hcsp as Hsp0. lay. unfold INT_MAX in *.
    pose proof (ndz_range x Hx) as [NR NR1]. pose proof (Fc_flags _ _ FC) as Cfl.
    set (nd := ndz x) in *. set (P := (nd + ez x)%Z).
    assert (HP : (1 <= P <= 21)%Z /\ (nd <= P)%Z).
    { subst P. unfold ez. destruct (Z.eqb_spec x 0); [lia|]. specialize (NR1 n). lia. }
    (* [comment removed for export] *)
    assert (S1 : exists r1, msteps SEGS (mkst r (rl dF_17f6c 0x18868) m rom) (mkst r1 (rl dF_17f6c 0x18898) m rom)
            /\ getr r1 10 = Z_to_bv 64 x /\ (forall x0 : reg, x0 <> 10 -> getr r1 x0 = getr r x0)).
    { destruct (Z.eq_dec x 0) as [X0|X0].
      - eexists. split.
        + stepn F_18868 D_18868; rwH.                                                              (* [comment removed for export] *)
          stepn F_1886c D_1886c; rwH.                                                              (* [comment removed for export] *)
          stepb_ft F_18870 D_18870 ltac:(cond_vm).                                                 (* [comment removed for export] *)
          stepb_tk F_18874 D_18874 ltac:(cond_vm).                                                 (* [comment removed for export] *)
          stepLD8 F_18880 D_18880 (Z_to_bv 64 x).                                                  (* [comment removed for export] *)
          stepb_ft F_18884 D_18884 ltac:(subst x; apply c_eq_refl).                                (* [comment removed for export] *)
          stepb_tk F_18888 D_18888 ltac:(cond_vm).                                                 (* [comment removed for export] *)
          apply mst_refl.
        + split; [gres; reflexivity|]. intros x0 Hx0. repeat (rewrite getr_other by exact Hx0). reflexivity.
      - eexists. split.
        + stepn F_18868 D_18868; rwH.
          stepn F_1886c D_1886c; rwH.
          stepb_ft F_18870 D_18870 ltac:(cond_vm).
          stepb_tk F_18874 D_18874 ltac:(cond_vm).
          stepLD8 F_18880 D_18880 (Z_to_bv 64 x).
          stepb_tk F_18884 D_18884 ltac:(rewrite c_eq_Z by lia; apply Z.eqb_neq; lia).          (* [comment removed for export] *)
          apply mst_refl.
        + split; [gres; reflexivity|]. intros x0 Hx0. repeat (rewrite getr_other by exact Hx0). reflexivity. }
    destruct S1 as (r1 & RUN1 & Q10 & QK).
    assert (Q2 : getr r1 2 = Z_to_bv 64 (sp0 - 3312)) by (rewrite QK by (intros E; discriminate E); exact R2).
    assert (Q9 : getr r1 9 = Z_to_bv 64 2147483647) by (rewrite QK by (intros E; discriminate E); exact R9).
    assert (Q18 : getr r1 18 = Z_to_bv 64 (2147483647 - cnt')) by (rewrite QK by (intros E; discriminate E); exact R18).
    assert (Q20 : getr r1 20 = Z_to_bv 64 (sp0 - 2400)) by (rewrite QK by (intros E; discriminate E); exact R20).
    assert (Q22 : getr r1 22 = Z_to_bv 64 0) by (rewrite QK by (intros E; discriminate E); exact R22).
    assert (Q23 : getr r1 23 = Z_to_bv 64 (sp0 - 3136 - nd)) by (rewrite QK by (intros E; discriminate E); exact R23).
    assert (Q24 : getr r1 24 = Z_to_bv 64 0) by (rewrite QK by (intros E; discriminate E); exact R24).
    assert (Q25 : getr r1 25 = Z_to_bv 64 18446744073709551615) by (rewrite QK by (intros E; discriminate E); exact R25).
    assert (EZ : v_sltiu (Z_to_bv 64 x) 1 = Z_to_bv 64 (ez x)).
    { unfold v_sltiu, ez. change (bv_wrap 64 1) with 1%Z. rewrite u_Z2bv by lia.
      destruct (Z.eqb_spec x 0).
      - replace (x <? 1)%Z with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
      - replace (x <? 1)%Z with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
    eexists. split.
    - eapply msteps_trans; [exact RUN1|].
      stepn F_18898 D_18898; rwH. rewrite EZ.                                                      (* [comment removed for export] *)
      stepiv F_1889c D_1889c (Z_to_bv 64 (sp0 - 3136)) ltac:(zval).                                (* [comment removed for export] *)
      stepiv F_188a0 D_188a0 (Z_to_bv 64 nd) ltac:(zval).                                         (* [comment removed for export] *)
      stepiv F_188a4 D_188a4 (Z_to_bv 64 P) ltac:(zval).                                          (* [comment removed for export] *)
      stepb_tk F_188a8 D_188a8 ltac:(rwH; apply c_lts_neg_0 || idtac; unfold c_lts, bv_lts; rewrite bv_signed_hi by (unorm; lia);
                                     rewrite bv_signed_small by (unorm; lia); unorm; apply Z.ltb_lt; lia).   (* [comment removed for export] *)
      stepn F_188b0 D_188b0.                                                                       (* [comment removed for export] *)
      stepn F_188b4 D_188b4.                                                                       (* [comment removed for export] *)
      stepiv F_188b8 D_188b8 (Z_to_bv 64 P) ltac:(gres; rwH; imm_norm; rewrite v_addiw_Z by lia; f_equal; lia). (* [comment removed for export] *)
      stepiv F_188bc D_188bc (Z_to_bv 64 nd) ltac:(zval).                                         (* [comment removed for export] *)
      stepn F_188c0 D_188c0.                                                                       (* [comment removed for export] *)
      stepST F_188c4 D_188c4 (Z_to_bv 64 (sp0 - 3296)) (Z_to_bv 64 nd) ltac:(sok).               (* [comment removed for export] *)
      stepb_ft F_188c8 D_188c8 ltac:(rewrite c_lts_Z by lia; apply Z.ltb_ge; lia).               (* [comment removed for export] *)
      stepn F_188cc D_188cc.                                                                       (* [comment removed for export] *)
      stepiv F_188d0 D_188d0 (Z_to_bv 64 P) ltac:(gres; rwH; imm_norm; rewrite v_addiw_Z by lia; f_equal; lia). (* [comment removed for export] *)
      stepLD8 F_188d4 D_188d4 (Z_to_bv 64 pl).                                                    (* [comment removed for export] *)
      stepn F_188d8 D_188d8; rwH; rewrite (v_subw_Z 2147483647 pl) by lia.                       (* [comment removed for export] *)
      stepb_ft F_188dc D_188dc ltac:(rewrite c_lts_Z by lia; apply Z.ltb_ge; lia).               (* [comment removed for export] *)
      stepn F_188e0 D_188e0.                                                                       (* [comment removed for export] *)
      stepLD8 F_188e4 D_188e4 (Z_to_bv 64 pl).                                                    (* [comment removed for export] *)
      stepn F_188e8 D_188e8; rewrite (v_addw_Z pl P) by lia.                                     (* [comment removed for export] *)
      stepn F_188ec D_188ec; rwH.                                                                  (* [comment removed for export] *)
      stepST F_188f0 D_188f0 (Z_to_bv 64 (sp0 - 3280)) (Z_to_bv 64 (pl + P)) ltac:(sok).         (* [comment removed for export] *)
      stepb_ft F_188f4 D_188f4 ltac:(rwH; rewrite c_lts_Z by lia; apply Z.ltb_ge; lia).          (* [comment removed for export] *)
      stepLD8 F_188f8 D_188f8 (Z_to_bv 64 (pl + P)).                                              (* [comment removed for export] *)
      stepb_ft F_188fc D_188fc ltac:(rwH; rewrite c_lts_Z by lia; apply Z.ltb_ge; lia).          (* [comment removed for export] *)
      stepn F_18900 D_18900.                                                                       (* [comment removed for export] *)
      stepn F_18904 D_18904; rwH.                                                                  (* [comment removed for export] *)
      stepST F_18908 D_18908 (Z_to_bv 64 (sp0 - 3304)) (Z_to_bv 64 0) ltac:(sok).                (* [comment removed for export] *)
      stepb_ft F_1890c D_1890c ltac:(cond_vm).                                                     (* [comment removed for export] *)
      stepLD8 F_18910 D_18910 (Z_to_bv 64 (pl + P)).                                              (* [comment removed for export] *)
      stepb_tk F_18914 D_18914 ltac:(rwH; rewrite c_lts_Z by lia; apply Z.ltb_ge; lia).          (* [comment removed for export] *)
      stepLBU F_18990 D_18990 (Z_to_bv 8 0) ltac:(addr_norm; rdn_solve).                           (* [comment removed for export] *)
      stepn F_18994 D_18994.                                                                       (* [comment removed for export] *)
      stepb_ft F_18998 D_18998 ltac:(apply c_eq_refl).                                             (* [comment removed for export] *)
      stepLD8 F_1899c D_1899c pfx.                                                                 (* [comment removed for export] *)
      stepLD8 F_189a0 D_189a0 (Z_to_bv 64 pl).                                                    (* [comment removed for export] *)
      stepn F_189a4 D_189a4.                                                                       (* [comment removed for export] *)
      stepn F_189a8 D_189a8.                                                                       (* [comment removed for export] *)
      unfold seg3M. apply mst_refl.
    - repeat split; gres; rwH; try reflexivity; try bveq.
      intros x0 Hx0. cbv [In] in Hx0.
      repeat (destruct Hx0 as [<-|Hx0]; [gres; apply QK; intros E; discriminate E|]). destruct Hx0.
  Qed.
End CD.
