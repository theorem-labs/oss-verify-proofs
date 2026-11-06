(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool String Lia.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim StoreOk.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Frame.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import Hoare SeqExec RefMemcpyLib ZStores.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VLin VLinalg VWord2 VState VLogic VGamma VAbs VAbsSound VAbsSound2 VAbsSound3 VStep VStepMem VStepSound VStepMemSound VStepMemSound2 VCert VContract VContractSound VContractSound2 VContractSound3 VContractSound4 VState2 VStepMem2 VGamma2 VStepMem2SoundA VStepMem2SoundB VStepMem2SoundC VStepMem2SoundD VContractA VCert2 VContract2 VContract2Iface VContractASound1 VContractASound2 VContractASound4 VContractASoundI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition JUNK6 : Z := 2264.

Section S.
  Variable SEGS : list Segment.
  Variable P : vparams2.
  Variable E : venv2.
  Variables mem0 rom : word -> option byte.
  Variable CI : cimg.
  Let P1 := p1 P.
  Let E1 := ev1 E.
  Hypothesis PO2 : params_ok2 SEGS P.
  #[warnings="-notation-for-abbreviation"] Notation gamma2P := (gamma2 SEGS P E mem0).
  Hypothesis SHOFF : vp_shoff P = SBz.
  Hypothesis ROM_HI : forall a : word, SBz <= bv_unsigned a -> seg_rom SEGS a = None.
  Hypothesis FSLEN : forall len ssl, vp_fs P = Some (len, ssl) -> FS_FRAMES + FS_NCLASSES * 2 ^ FS_SSL < len.
  Hypothesis FS_SOME : vp_fs P <> None.
  Hypothesis FRAME40 : vp_frame (p1 P) < 2 ^ 40.
  Lemma HKJ6 : 0 <= JUNK6 /\ JUNK6 + 8 <= 2272.
  Proof. unfold JUNK6. lia. Qed.
  #[warnings="-notation-for-abbreviation"] Notation rng_facts6 := (rng_facts SEGS JUNK6).

  Variable tgt : Z.
  Variable MCELLS : (word -> option byte) -> Prop.
  Hypothesis MCELLS_OK : forall A nu regs mem, gamma2P A nu regs mem -> MCELLS mem.

  Definition RUN_spec6 : Prop := forall mem (a b usp K : Z) (bufa bufb : list byte) regs (ra : word),
    MCELLS mem -> rng_facts6 mem usp a K bufa -> rng_facts6 mem usp b K bufb ->
    bv_unsigned (nth (Z.to_nat K) bufb B0) = 0 ->
    SBz + 2280 <= usp < 2 ^ 64 ->
    (forall x, usp - JUNK6 <= x < usp -> store_ok SEGS mem (wordZ x) 1 = true) ->
    ret_ok ra -> getr regs 1%bv = ra -> getr regs 2%bv = wordZ usp -> getr regs 10%bv = wordZ a -> getr regs 11%bv = wordZ b ->
    exists regs' (dlt : Z) m',
      msteps SEGS (mkst regs (wordZ tgt) mem rom) (mkst regs' ra m' rom)
      /\ -1 <= dlt <= 1 /\ bv_unsigned (getr regs' 10%bv) = zwrap 64 dlt
      /\ getr regs' 2%bv = wordZ usp /\ getr regs' 1%bv = ra
      /\ (forall r : reg, bv_unsigned r <> 0 -> ~ In (bv_unsigned r) CALLER_SAVED -> getr regs' r = getr regs r)
      /\ (forall x : word, (bv_unsigned x < usp - JUNK6 \/ usp <= bv_unsigned x) -> m' x = mem x)
      /\ (forall x, mem x <> None -> m' x <> None).
  Hypothesis RUN : RUN_spec6.

  Theorem i_strcmp_post : contract_post2 SEGS P E mem0 rom CI C_i_strcmp tgt.
  Proof.
    intros A spoff l nu regs mem ra HC HG2 MEMO Hsp HK Hret Hra.
    pose proof HG2 as (HG1 & HE & HM & HF2 & HDD & RGN & LIVE & BEL2 & GL2 & FI2 & MOK).
    pose proof (gamma2_lgamma _ _ _ _ _ _ _ _ HG2) as HL.
    pose proof (PO1 _ _ PO2) as PO. pose proof PO as (P0 & Psphi & PS & PF & PW & PR & PP & PB).
    pose proof HE as (HEV1 & HD2 & HFS & HZO & HKC). pose proof HEV1 as (E1a & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E11 & E12).
    pose proof (proj1 (proj2 HG1)) as HM1. pose proof HM1 as (MF & MD & MP & MFM). pose proof (proj1 (proj2 (proj2 HG1))) as HF1.
    destruct (env_facts SEGS P E mem0 PO2 FSLEN FS_SOME A nu regs mem HG2) as (flen & fssl & EFS & [FS1 FS2] & FS3 & FS5 & APsf & HMsp & SPHI & Pfr & _ & SP0al & SPLO).
    unfold HIGH_MEM_BEG, HIGH_MEM_END in *.
    (* [comment removed for export] *)
    assert (HKR : - vp_frame P1 <= spoff - 2272 /\ spoff <= 0 /\ exists wr, In wr (vp_wstack P1) /\ fst wr <= spoff - 2272 /\ spoff <= snd wr).
    { destruct HK as [HK'|HK']; [cbn in HK'; discriminate|]. apply in_ranges_sound in HK' as (wlo & whi & Hw & W1 & W2).
      destruct (PR _ Hw). cbn [fst snd contract2_K] in *. unfold K_i_strcmp, P1, E1 in *. split; [lia|]. split; [lia|].
      exists (wlo, whi). cbn. split; [exact Hw|lia]. }
    destruct HKR as (K1 & K2 & KW).
    set (usp := e_sp0 E1 + spoff) in *.
    assert (USP : SBz + 2280 <= usp < 2 ^ 64) by (unfold usp, SBz, P1, E1 in *; lia).
    assert (JOK : forall x, usp - JUNK6 <= x < usp -> store_ok SEGS mem (wordZ x) 1 = true).
    { intros x Hx. unfold JUNK6 in Hx. apply (proj1 (MF x ltac:(unfold usp, P1, E1 in *; lia))). }
    assert (R2 : getr regs 2%bv = wordZ usp).
    { apply (reg_word SEGS P1 E1 (zpatch P E mem0 mem) (v1 A) nu regs mem 2%bv (lsymc SP0 spoff) usp HG1);
        [vm_compute; lia|exact Hsp| |unfold usp, P1, E1 in *; lia].
      rewrite eval_lsymc. rewrite (HF1 SP0 (e_sp0 E1)) by reflexivity. reflexivity. }
    (* [comment removed for export] *)
    cbn [contract_apply2] in HC. unfold ca_i_strcmp in HC. cbv zeta in HC.
    destruct (get_reg2 A A0r) as [ae|] eqn:Eae; [|discriminate HC].
    destruct (get_reg2 A A1r) as [be|] eqn:Ebe; [|discriminate HC]. unfold get_reg2 in Eae, Ebe.
    destruct (rodata_cstr_len (p1 P) (Some be)) as [kb|] eqn:Ecs; [|discriminate HC].
    destruct (in_ranges (vp_segs (p1 P)) (lc be) (kb + 1)) eqn:Esg; cbn [negb] in HC; [|discriminate HC].
    destruct (img_str_ok P (lc be) kb) eqn:IOK; cbn [negb] in HC; [|discriminate HC].
    pose proof (reg_val SEGS P1 E1 (zpatch P E mem0 mem) (v1 A) nu regs mem 10%bv ae HG1 ltac:(vm_compute; lia) Eae) as [V10 B10].
    pose proof (reg_val SEGS P1 E1 (zpatch P E mem0 mem) (v1 A) nu regs mem 11%bv be HG1 ltac:(vm_compute; lia) Ebe) as [V11 B11].
    (* [comment removed for export] *)
    destruct (rodata_cstr_sound SEGS P1 E1 (zpatch P E mem0 mem) PO mem _ _ HEV1 HM1 Ecs) as [be' (Ebe' & Cbe & Hk0 & Hb0 & Hbk & NZ & ZK)].
    injection Ebe' as <-. set (b := lc be) in *.
    assert (R11 : getr regs 11%bv = wordZ b).
    { apply wordZ_eq_u. rewrite V11, (eval_is_const _ _ Cbe). apply zwrap_id. unfold b, P1 in *. lia. }
    unfold img_str_ok in IOK.
    destruct (img_rng_facts SEGS P E mem0 PO2 SHOFF ROM_HI FSLEN FS_SOME 2272 JUNK6 HKJ6 A nu regs mem spoff b kb (kb + 1) HG2 ltac:(replace (b + (kb + 1)) with (b + kb + 1) by lia; exact IOK) ltac:(lia) ltac:(lia) Esg K1) as (bufb & FB).
    assert (ZKB : bv_unsigned (nth (Z.to_nat kb) bufb B0) = 0).
    { destruct FB as (Hbufb & Lb & _). destruct ZK as [bb [Rb Ub]].
      pose proof (rdn_nth SEGS mem (length bufb) (wordZ b) bufb (Z.to_nat kb) Hbufb ltac:(lia)) as X.
      rewrite wordZ_add_nat, Z2Nat.id in X by lia. rewrite Rb in X. injection X as <-. exact Ub. }
    (* [comment removed for export] *)
    assert (FIN : forall a bufa, getr regs 10%bv = wordZ a -> rng_facts6 mem usp a kb bufa ->
      of_ca (let '(v, B1) := afresh (v1 A) (Some (-255), Some 255) in ca_ok1 (with_v1 A B1) v) = CR2OkN l ->
      exists A1 v regs' mem' nu',
           In (A1, v) l
        /\ msteps SEGS (mkst regs (wordZ tgt) mem rom) (mkst regs' ra mem' rom)
        /\ gamma2P (contract_frame2 C_i_strcmp A1 spoff v) nu' regs' mem'
        /\ getr regs' 1%bv = ra
        /\ ext (vs2_next A) nu nu' /\ (vs2_next A <= vs2_next (contract_frame2 C_i_strcmp A1 spoff v))%positive
        /\ frame_mod mem mem' (unit_regions2 P E)
        /\ flags_step P E A (contract_frame2 C_i_strcmp A1 spoff v) nu nu' mem mem').
    { intros a bufa R10 FA HC'.
      destruct (RUN mem a b usp kb bufa bufb regs ra (MCELLS_OK _ _ _ _ HG2) FA FB ZKB USP JOK Hret Hra R2 R10 R11)
        as (regs' & dlt & m' & MS & Hd & Q10 & Q2 & Q1 & QK & QM & QG).
      pose proof (afresh_sound (v1 A) nu (Some (-255), Some 255) dlt HL ltac:(split; cbn; lia)) as AFS.
      destruct (afresh (v1 A) (Some (-255), Some 255)) as [v B1] eqn:EAF.
      cbn [of_ca ca_ok1] in HC'. injection HC' as <-.
      destruct AFS as (nu' & XB & LB & Hv). destruct v as [e|]; [|destruct Hv]. destruct Hv as [Ve Be].
      destruct (post_val SEGS P E mem0 rom PO2 FSLEN FS_SOME 2272 JUNK6 HKJ6 C_i_strcmp A spoff nu nu' regs regs' mem m' B1 e dlt eq_refl
                  HG2 MEMO K1 K2 KW XB LB Ve Be Q10 QK QM QG) as (G & X1 & X2 & X3 & X4).
      exists (with_v1 A B1), (Some e), regs', m', nu'.
      split; [left; reflexivity|]. split; [exact MS|]. split; [exact G|]. split; [exact Q1|]. auto. }
    destruct (range_check P A ae (lconst (kb + 1)) false) as [r lo hi|rr| |m1] eqn:RC; [| |discriminate HC|discriminate HC].
    - (* [comment removed for export] *)
      destruct (range_check_ld_rgn_inv P A ae (lconst (kb + 1)) r lo hi RC) as (B & HBS & C1 & C2 & C3 & HGr & HKr & LET).
      cbv zeta in LET. destruct LET as (LO & HI & RLO & RHI & HRA & HFZ).
      pose proof (rgn_get_in _ _ _ HGr) as [Hr HBr].
      set (off := laddc (lsub ae (lsym B)) (- vr_disp r)) in *.
      assert (Eoff : eval nu ae = rbase nu r + eval nu off) by (unfold off; rewrite <- HBr, eval_off; lia).
      pose proof (bnd_sound (v1 A) nu off HL) as Bo. pose proof (bnd_sound (v1 A) nu (ladd off (lconst (kb + 1))) HL) as Bo1.
      unfold lo_of in LO. unfold hi_of in HI.
      destruct (bnd (v1 A) off) as [olo ohi] eqn:Ebo. cbn [fst] in LO. subst olo.
      destruct (bnd (v1 A) (ladd off (lconst (kb + 1)))) as [olo1 ohi1] eqn:Ebo1. cbn [snd] in HI. subst ohi1.
      destruct Bo as [Bo _]. destruct Bo1 as [_ Bo1]. cbn [fst snd lo_le hi_ge] in Bo, Bo1. rewrite eval_ladd, eval_lconst in Bo1.
      set (ov := eval nu off) in *. set (a := rbase nu r + ov) in *.
      destruct (rgn_rng_facts SEGS P E mem0 PO2 SHOFF ROM_HI FSLEN FS_SOME 2272 JUNK6 HKJ6 A nu regs mem spoff B r lo hi ov kb HG2 HGr HKr RLO RHI HRA HFZ
                  Bo ltac:(lia) ltac:(lia) K1 K2) as (bufa & FA & HRB).
      fold a in FA, HRB. pose proof FA as (_ & _ & HR2 & HR1 & _).   (* [comment removed for export] *)
      assert (R10 : getr regs 10%bv = wordZ a).
      { apply wordZ_eq_u. rewrite V10, Eoff. fold ov. fold a. apply zwrap_id. lia. }
      exact (FIN a bufa R10 FA HC).
    - (* [comment removed for export] *)
      destruct (range_check_ld_v1_inv P A ae (lconst (kb + 1)) rr RC) as [(so & slo & shi & -> & RRs & Hab & Hsa & Hsw)|[(doff & -> & RRd)|(ilo & ihi & ->)]];
        [|discriminate HC|discriminate HC].
      pose proof (readable_range_stack P1 (v1 A) ae (lconst (kb + 1)) so slo shi RRs) as SRs.
      destruct (stack_range_sound P1 E1 (v1 A) nu ae (lconst (kb + 1)) false so slo shi HL HF1 SRs) as (_ & Es & Ss1 & Ss2 & Ss3 & Ss4 & _).
      rewrite eval_lconst in Ss2.
      set (sov := eval nu so) in *. set (a := e_sp0 E1 + sov) in *.
      destruct (above_sp_sound A spoff slo shi Hsp Hab) as [BAD|ASP]; [lia|].
      destruct (stack_rng_facts SEGS P E mem0 PO2 SHOFF ROM_HI FSLEN FS_SOME FRAME40 2272 JUNK6 HKJ6 A nu regs mem spoff slo shi sov kb HG2 Hsa Hsw
                  Ss3 Ss1 ltac:(lia) Ss4 ltac:(lia) K1 ASP) as (bufa & FA & HR1 & HR2).
      fold a in FA, HR1, HR2. unfold HIGH_MEM_BEG, HIGH_MEM_END in HR1, HR2.
      assert (R10 : getr regs 10%bv = wordZ a).
      { apply wordZ_eq_u. rewrite V10, Es. apply zwrap_id. unfold a, sov, P1, E1 in *. lia. }
      exact (FIN a bufa R10 FA HC).
  Qed.

  Theorem i_strcmp_dead : contract_dead2 SEGS P E mem0 CI C_i_strcmp.
  Proof.
    intros A spoff nu regs mem HC HG2.
    pose proof HG2 as (HG1 & HE & HM & HF2 & HDD & RGN & LIVE & BEL2 & GL2 & FI2 & MOK).
    pose proof (gamma2_lgamma _ _ _ _ _ _ _ _ HG2) as HL. pose proof (proj1 (proj2 (proj2 HG1))) as HF1.
    cbn [contract_apply2] in HC. unfold ca_i_strcmp in HC. cbv zeta in HC.
    destruct (get_reg2 A A0r) as [ae|] eqn:Eae; [|discriminate HC].
    destruct (get_reg2 A A1r) as [be|] eqn:Ebe; [|discriminate HC]. unfold get_reg2 in Eae, Ebe.
    destruct (rodata_cstr_len (p1 P) (Some be)) as [kb|] eqn:Ecs; [|discriminate HC].
    destruct (in_ranges (vp_segs (p1 P)) (lc be) (kb + 1)); cbn [negb] in HC; [|discriminate HC].
    destruct (img_str_ok P (lc be) kb); cbn [negb] in HC; [|discriminate HC].
    destruct (range_check P A ae (lconst (kb + 1)) false) as [r lo hi|rr| |m1] eqn:RC.
    - destruct (afresh _ _); discriminate HC.
    - destruct rr; try discriminate HC; destruct (afresh _ _); discriminate HC.
    - pose proof (rodata_cstr_sound SEGS P1 E1 (zpatch P E mem0 mem) (PO1 _ _ PO2) mem _ _ (proj1 HE) (proj1 (proj2 HG1)) Ecs) as [be' (Ebe' & Cbe & Hk0 & _)].
      exact (range_check_not_dead SEGS P E mem0 PO2 A nu regs mem ae (lconst (kb + 1)) false HG2 ltac:(rewrite eval_lconst; lia) RC).
    - discriminate HC.
  Qed.
End S.
