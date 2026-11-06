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
(* [comment removed for export] *)
Definition JUNK5 : Z := 2216.    (* [comment removed for export] *)

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
  (* [comment removed for export] *)
  Hypothesis FS_SOME : vp_fs P <> None.
  Hypothesis FRAME40 : vp_frame (p1 P) < 2 ^ 40.

  (* [comment removed for export] *)
  Lemma HKJ5 : 0 <= JUNK5 /\ JUNK5 + 8 <= 2224.
  Proof. unfold JUNK5. lia. Qed.
  #[local] Notation str_facts5 := (str_facts SEGS JUNK5).

  Variable tgt : Z.
  Variable MCELLS : (word -> option byte) -> Prop.
  Hypothesis MCELLS_OK : forall A nu regs mem, gamma2P A nu regs mem -> MCELLS mem.

  Definition RUN_spec5 : Prop := forall mem (s usp K : Z) (buf : list byte) regs (ra : word),
    MCELLS mem -> str_facts5 mem usp s K buf ->
    SBz + 2224 <= usp < 2 ^ 64 ->
    (forall a, usp - JUNK5 <= a < usp -> store_ok SEGS mem (wordZ a) 1 = true) ->
    ret_ok ra -> getr regs 1%bv = ra -> getr regs 2%bv = wordZ usp -> getr regs 10%bv = wordZ s ->
    exists regs' (i : Z) m',
      msteps SEGS (mkst regs (wordZ tgt) mem rom) (mkst regs' ra m' rom)
      /\ 0 <= i <= K /\ bv_unsigned (nth (Z.to_nat i) buf B0) = 0
      /\ (forall j, 0 <= j < i -> bv_unsigned (nth (Z.to_nat j) buf B0) <> 0)
      /\ getr regs' 10%bv = Z_to_bv 64 i /\ getr regs' 2%bv = wordZ usp /\ getr regs' 1%bv = ra
      /\ (forall r : reg, bv_unsigned r <> 0 -> ~ In (bv_unsigned r) CALLER_SAVED -> getr regs' r = getr regs r)
      /\ (forall x : word, (bv_unsigned x < usp - JUNK5 \/ usp <= bv_unsigned x) -> m' x = mem x)
      /\ (forall x, mem x <> None -> m' x <> None).
  Hypothesis RUN : RUN_spec5.


  (* [comment removed for export] *)
  Definition post_concl A spoff l nu regs mem (ra : word) : Prop :=
    exists A1 v regs' mem' nu',
         In (A1, v) l
      /\ msteps SEGS (mkst regs (wordZ tgt) mem rom) (mkst regs' ra mem' rom)
      /\ gamma2P (contract_frame2 C_i_strlen A1 spoff v) nu' regs' mem'
      /\ getr regs' 1%bv = ra
      /\ ext (vs2_next A) nu nu' /\ (vs2_next A <= vs2_next (contract_frame2 C_i_strlen A1 spoff v))%positive
      /\ frame_mod mem mem' (unit_regions2 P E)
      /\ flags_step P E A (contract_frame2 C_i_strlen A1 spoff v) nu nu' mem mem'.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma post_v1 A spoff l nu regs mem (ra : word) pe :
    gamma2P A nu regs mem -> vs_memo A = [] ->
    get_reg (v1 A) 2 = Some (lsymc SP0 spoff) ->
    - vp_frame P1 <= spoff - 2224 -> spoff <= 0 ->
    (exists wr, In wr (vp_wstack P1) /\ fst wr <= spoff - 2224 /\ spoff <= snd wr) ->
    ret_ok ra -> getr regs 1%bv = ra -> getr regs 2%bv = wordZ (e_sp0 E1 + spoff) ->
    get_reg (v1 A) A0r = Some pe ->
    of_ca (ca_i_strlen_v1 P A pe) = CR2OkN l ->
    post_concl A spoff l nu regs mem ra.
  Proof.
    intros HG2 MEMO Hsp K1 K2 KW Hret Hra R2 Epe HC.
    pose proof HG2 as (HG1 & HE & HM & HF2 & HDD & RGN & LIVE & BEL2 & GL2 & FI2 & MOK).
    pose proof (gamma2_lgamma _ _ _ _ _ _ _ _ HG2) as HL.
    pose proof (PO1 _ _ PO2) as PO. pose proof PO as (P0 & Psphi & PS & PF & PW & PR & PP & PB).
    pose proof HE as (HEV1 & HD2 & HFS & HZO & HKC).
    pose proof (proj1 (proj2 HG1)) as HM1. pose proof HM1 as (MF & MD & MP & MFM). pose proof (proj1 (proj2 (proj2 HG1))) as HF1.
    destruct (env_facts SEGS P E mem0 PO2 FSLEN FS_SOME A nu regs mem HG2) as (flen & fssl & EFS & [FS1 FS2] & FS3 & FS5 & APsf & HMsp & SPHI & Pfr & E1a & SP0al & SPLO).
    unfold HIGH_MEM_BEG, HIGH_MEM_END in *.
    set (usp := e_sp0 E1 + spoff) in *.
    assert (USP : SBz + 2224 <= usp < 2 ^ 64) by (unfold usp, SBz, P1, E1 in *; lia).
    assert (JOK : forall a, usp - JUNK5 <= a < usp -> store_ok SEGS mem (wordZ a) 1 = true).
    { intros a Ha. unfold JUNK5 in Ha. apply (proj1 (MF a ltac:(unfold usp, P1, E1 in *; lia))). }
    pose proof (reg_val SEGS P1 E1 (zpatch P E mem0 mem) (v1 A) nu regs mem 10%bv pe HG1 ltac:(vm_compute; lia) Epe) as [V10 B10].
    unfold ca_i_strlen_v1 in HC. cbv zeta in HC. unfold c_strlen, getA in HC. rewrite Epe in HC.
    destruct (rodata_cstr_len (p1 P) (Some pe)) as [k|] eqn:Ecs.
    - (* [comment removed for export] *)
      destruct (in_ranges (vp_segs (p1 P)) (lc pe) (k + 8)) eqn:Esg; [|discriminate HC]. cbv iota beta in HC.
      destruct (img_str_ok P (lc pe) k) eqn:IOK; [|discriminate HC]. cbn [of_ca ca_ok1] in HC. injection HC as <-.
      destruct (rodata_cstr_sound SEGS P1 E1 (zpatch P E mem0 mem) PO mem _ _ HEV1 HM1 Ecs) as [pe' (Epe' & Cpe & Hk & Hp0 & Hpk & NZ & ZK)].
      injection Epe' as <-. set (a := lc pe) in *.
      assert (R10 : getr regs 10%bv = wordZ a).
      { apply wordZ_eq_u. rewrite V10, (eval_is_const _ _ Cpe). apply zwrap_id. unfold a, P1 in *. lia. }
      destruct (img_str_facts SEGS P E mem0 PO2 SHOFF ROM_HI FSLEN FS_SOME 2224 JUNK5 HKJ5 A nu regs mem spoff a k HG2 IOK NZ ZK Esg K1) as (buf & Lbuf & SF & NZB).
      destruct (RUN mem a usp k buf regs ra (MCELLS_OK _ _ _ _ HG2) SF USP JOK Hret Hra R2 R10)
        as (regs' & i & m' & MS & Hi & Zi & NZi & Q10 & Q2 & Q1 & QK & QM & QG).
      assert (Ei : i = k).
      { destruct (Z_lt_le_dec i k) as [LT|]; [|lia]. exfalso. apply (NZB (Z.to_nat i) ltac:(lia)). exact Zi. }
      subst i.
      destruct (post_val SEGS P E mem0 rom PO2 FSLEN FS_SOME 2224 JUNK5 HKJ5 C_i_strlen A spoff nu nu regs regs' mem m' (v1 A) (lconst k) k eq_refl HG2 MEMO K1 K2 KW (aext_refl _ _) HL
                  (eval_lconst _ _) (lin_below_lconst _ _) ltac:(rewrite Q10, u_Z_to_bv64; reflexivity) QK QM QG) as (G & X1 & X2 & X3 & X4).
      exists (with_v1 A (v1 A)), (Some (lconst k)), regs', m', nu.
      split; [left; reflexivity|]. split; [exact MS|]. split; [exact G|]. split; [exact Q1|]. auto.
    - (* [comment removed for export] *)
      destruct (is_sp_rel pe) eqn:SPR; [|discriminate HC]. cbn [negb] in HC.
      destruct (dead_lin (v1 A) (lsub pe (lsym SP0))) eqn:Ed; [discriminate HC|].
      pose proof (bnd_sound (v1 A) nu (lsub pe (lsym SP0)) HL) as Hbd. unfold lo_of, hi_of in HC.
      destruct (bnd (v1 A) (lsub pe (lsym SP0))) as [[plo|] [phi|]]; try discriminate HC. cbn [fst snd] in HC.
      destruct Hbd as [Hplo Hphi]; cbn [fst snd lo_le hi_ge] in Hplo, Hphi. rewrite eval_lsub, eval_lsym, (HF1 SP0 (e_sp0 E1) eq_refl) in Hplo, Hphi.
      destruct (find_nul_bound (v1 A) phi) as [H|] eqn:Ef; [|discriminate HC].
      destruct (Z.ltb_spec 0 (H + 8)); [discriminate HC|]. destruct (Z.ltb_spec plo (- vp_frame (p1 P))); [discriminate HC|].
      destruct (above_sp A plo (H + 1)) eqn:ASP; cbn [negb] in HC.
      2:{ exfalso. destruct (fresh_sym (v1 A)) as [s0 A0]; destruct (lin_is_const _); [discriminate HC|]. destruct (aassume _ _) as [[|] ?]; discriminate HC. }
      destruct (stack_addressable A plo (H + 1)) eqn:SA; cbn [negb] in HC.
      2:{ exfalso. destruct (fresh_sym (v1 A)) as [s0 A0]; destruct (lin_is_const _); [discriminate HC|]. destruct (aassume _ _) as [[|] ?]; discriminate HC. }
      destruct (stack_shadow_words_ok P plo (H + 1)) eqn:SW; cbn [negb] in HC.
      2:{ exfalso. destruct (fresh_sym (v1 A)) as [s0 A0]; destruct (lin_is_const _); [discriminate HC|]. destruct (aassume _ _) as [[|] ?]; discriminate HC. }
      destruct (find_nul_bound_sound SEGS P1 E1 (zpatch P E mem0 mem) PO (v1 A) nu regs mem phi H HG1 Ef) as [z [bz (Hz1 & Hz2 & Rz & Uz)]].
      destruct (above_sp_sound A spoff plo (H + 1) Hsp ASP) as [BAD|ASP']; [lia|].
      set (p := eval nu pe) in *. set (ov := p - e_sp0 E1) in *.
      assert (R10 : getr regs 10%bv = wordZ p).
      { apply wordZ_eq_u. rewrite V10. apply zwrap_id. unfold p, P1, E1 in *. lia. }
      destruct (stack_str_facts SEGS P E mem0 PO2 SHOFF ROM_HI FSLEN FS_SOME FRAME40 2224 JUNK5 HKJ5 A nu regs mem spoff plo H ov z bz HG2 SA SW ltac:(unfold P1 in *; lia)
                  ltac:(unfold ov, p; lia) ltac:(unfold ov, p; lia) ltac:(lia) ltac:(lia) Rz Uz K1 ASP') as (buf & Lbuf & SF & HR1 & HR2).
      assert (R10' : getr regs 10%bv = wordZ (e_sp0 E1 + ov)) by (replace (e_sp0 E1 + ov) with p by (unfold ov; lia); exact R10).
      destruct (RUN mem (e_sp0 E1 + ov) usp (z - ov) buf regs ra (MCELLS_OK _ _ _ _ HG2) SF USP JOK Hret Hra R2 R10')
        as (regs' & i & m' & MS & Hi & Zi & NZi & Q10 & Q2 & Q1 & QK & QM & QG).
      (* [comment removed for export] *)
      pose proof (fresh_sym_box_sound (v1 A) nu (Some 0, Some (H - plo)) i HL ltac:(split; cbn; unfold ov, p in *; lia)) as FS.
      destruct (fresh_sym (v1 A)) as [s A1']. set (A2 := asetbox A1' s (Some 0, Some (H - plo))) in *.
      destruct FS as (X1 & L2 & V2 & S2 & N2).
      assert (FIN : forall A3, aext (v1 A) A3 nu (vupd nu s i) -> lgamma A3 (vupd nu s i) -> (s < vs_next A3)%positive ->
                    l = [(with_v1 A A3, Some (lsym s))] -> post_concl A spoff l nu regs mem ra).
      { intros A3 X3 L3 S3 ->.
        destruct (post_val SEGS P E mem0 rom PO2 FSLEN FS_SOME 2224 JUNK5 HKJ5 C_i_strlen A spoff nu (vupd nu s i) regs regs' mem m' A3 (lsym s) i eq_refl HG2 MEMO K1 K2 KW X3 L3
                    ltac:(rewrite eval_lsym; exact V2) ltac:(apply lin_below_lsym; exact S3) ltac:(rewrite Q10, u_Z_to_bv64; reflexivity) QK QM QG)
          as (G & Y1 & Y2 & Y3 & Y4).
        exists (with_v1 A A3), (Some (lsym s)), regs', m', (vupd nu s i).
        split; [left; reflexivity|]. split; [exact MS|]. split; [exact G|]. split; [exact Q1|]. auto. }
      cbv iota beta zeta in HC.
      destruct (lin_is_const (lsub pe (lsym SP0))) eqn:Ec.
      + cbn [of_ca ca_ok1] in HC. injection HC as <-. exact (FIN A2 X1 L2 S2 eq_refl).
      + pose proof (aassume_sound A2 (vupd nu s i) (laddc (ladd (lsym s) (lsub pe (lsym SP0))) (- H)) L2) as AS.
        destruct (aassume A2 _) as [ok A3] eqn:Eas. cbn [fst snd] in AS.
        assert (Hle : eval (vupd nu s i) (laddc (ladd (lsym s) (lsub pe (lsym SP0))) (- H)) <= 0).
        { rewrite eval_laddc, eval_ladd, eval_lsym, V2, eval_lsub, eval_lsym.
          rewrite ((proj1 X1 : ext _ _ _) SP0) by (pose proof (proj1 (lg_below _ _ HL)); unfold LAST_FIXED, SP0 in *; lia).
          rewrite (HF1 SP0 (e_sp0 E1) eq_refl).
          rewrite (eval_ext_below (vs_next (v1 A)) nu (vupd nu s i) pe (proj1 X1)) by exact B10.
          unfold ov, p in *. lia. }
        destruct (AS Hle ltac:(apply lin_below_laddc, lin_below_ladd; [apply lin_below_lsym; exact S2|apply lin_below_lsub; [eapply lin_below_mono; [exact (proj1 (proj2 X1))|exact B10]|apply lin_below_lsym; pose proof (proj1 (lg_below _ _ L2)); unfold LAST_FIXED, SP0 in *; lia]]))
          as (Hok & L3 & X3). subst ok. cbn [of_ca ca_ok1] in HC. injection HC as <-.
        apply (FIN A3); [eapply aext_trans; [exact X1|exact X3] | exact L3 | destruct X3 as (_ & X3b & _); clear -X3b S2; lia | reflexivity].
  Qed.

  (* [comment removed for export] *)

  Lemma post_cands A spoff l nu regs mem (ra : word) pe cl :
    gamma2P A nu regs mem -> vs_memo A = [] ->
    get_reg (v1 A) 2 = Some (lsymc SP0 spoff) ->
    - vp_frame P1 <= spoff - 2224 -> spoff <= 0 ->
    (exists wr, In wr (vp_wstack P1) /\ fst wr <= spoff - 2224 /\ spoff <= snd wr) ->
    ret_ok ra -> getr regs 1%bv = ra -> getr regs 2%bv = wordZ (e_sp0 E1 + spoff) ->
    get_reg (v1 A) A0r = Some pe -> ptr_candidates (v1 A) pe = Some cl ->
    of_ca (ca_i_strlen_cands P A cl) = CR2OkN l ->
    post_concl A spoff l nu regs mem ra.
  Proof.
    intros HG2 MEMO Hsp K1 K2 KW Hret Hra R2 Epe HPC HC.
    pose proof HG2 as (HG1 & HE & HM & HF2 & HDD & RGN & LIVE & BEL2 & GL2 & FI2 & MOK).
    pose proof (gamma2_lgamma _ _ _ _ _ _ _ _ HG2) as HL.
    pose proof (PO1 _ _ PO2) as PO. pose proof PO as (P0 & Psphi & PS & PF & PW & PR & PP & PB).
    pose proof HE as (HEV1 & HD2 & HFS & HZO & HKC).
    pose proof (proj1 (proj2 HG1)) as HM1. pose proof HM1 as (MF & MD & MP & MFM).
    destruct (env_facts SEGS P E mem0 PO2 FSLEN FS_SOME A nu regs mem HG2) as (flen & fssl & EFS & [FS1 FS2] & FS3 & FS5 & APsf & HMsp & SPHI & Pfr & E1a & SP0al & SPLO).
    unfold HIGH_MEM_BEG, HIGH_MEM_END in *.
    set (usp := e_sp0 E1 + spoff) in *.
    assert (USP : SBz + 2224 <= usp < 2 ^ 64) by (unfold usp, SBz, P1, E1 in *; lia).
    assert (JOK : forall a, usp - JUNK5 <= a < usp -> store_ok SEGS mem (wordZ a) 1 = true).
    { intros a Ha. unfold JUNK5 in Ha. apply (proj1 (MF a ltac:(unfold usp, P1, E1 in *; lia))). }
    pose proof (reg_val SEGS P1 E1 (zpatch P E mem0 mem) (v1 A) nu regs mem 10%bv pe HG1 ltac:(vm_compute; lia) Epe) as [V10 B10].
    unfold ca_i_strlen_cands in HC.
    destruct (rodata_cands (p1 P) 8 (img_str_ok P) cl) as [[klo khi]|] eqn:RC; [|discriminate HC].
    set (a := eval nu pe) in *.
    destruct (rodata_cands_sound P 8 (img_str_ok P) cl klo khi a RC (ptr_candidates_sound A nu pe cl HL HPC)) as (k & Ecs & Esg & IOK & Hk).
    destruct (rodata_cstr_sound SEGS P1 E1 (zpatch P E mem0 mem) PO mem _ _ HEV1 HM1 Ecs) as [pe' (Epe' & Cpe & Hk0 & Hp0 & Hpk & NZ & ZK)].
    injection Epe' as <-. cbn [lc lconst] in Hp0, Hpk, NZ, ZK.
    assert (R10 : getr regs 10%bv = wordZ a).
    { apply wordZ_eq_u. rewrite V10. apply zwrap_id. unfold a, P1 in *. lia. }
    destruct (img_str_facts SEGS P E mem0 PO2 SHOFF ROM_HI FSLEN FS_SOME 2224 JUNK5 HKJ5 A nu regs mem spoff a k HG2 IOK NZ ZK Esg K1) as (buf & Lbuf & SF & NZB).
    destruct (RUN mem a usp k buf regs ra (MCELLS_OK _ _ _ _ HG2) SF USP JOK Hret Hra R2 R10)
      as (regs' & i & m' & MS & Hi & Zi & NZi & Q10 & Q2 & Q1 & QK & QM & QG).
    assert (Ei : i = k).
    { destruct (Z_lt_le_dec i k) as [LT|]; [|lia]. exfalso. apply (NZB (Z.to_nat i) ltac:(lia)). exact Zi. }
    subst i.
    pose proof (afresh_sound (v1 A) nu (Some klo, Some khi) k HL ltac:(split; cbn; lia)) as AFS.
    destruct (afresh (v1 A) (Some klo, Some khi)) as [v B1] eqn:EAF.
    cbn [of_ca ca_ok1] in HC. injection HC as <-.
    destruct AFS as (nu' & XB & LB & Hv). destruct v as [e|]; [|destruct Hv]. destruct Hv as [Ve Be].
    destruct (post_val SEGS P E mem0 rom PO2 FSLEN FS_SOME 2224 JUNK5 HKJ5 C_i_strlen A spoff nu nu' regs regs' mem m' B1 e k eq_refl HG2 MEMO K1 K2 KW XB LB Ve Be ltac:(rewrite Q10, u_Z_to_bv64; reflexivity) QK QM QG)
      as (G & X1 & X2 & X3 & X4).
    exists (with_v1 A B1), (Some e), regs', m', nu'.
    split; [left; reflexivity|]. split; [exact MS|]. split; [exact G|]. split; [exact Q1|]. auto.
  Qed.

  (* [comment removed for export] *)

  Lemma post_rgn5 A spoff l nu regs mem (ra : word) pe B :
    gamma2P A nu regs mem -> vs_memo A = [] ->
    get_reg (v1 A) 2 = Some (lsymc SP0 spoff) ->
    - vp_frame P1 <= spoff - 2224 -> spoff <= 0 ->
    (exists wr, In wr (vp_wstack P1) /\ fst wr <= spoff - 2224 /\ spoff <= snd wr) ->
    ret_ok ra -> getr regs 1%bv = ra -> getr regs 2%bv = wordZ (e_sp0 E1 + spoff) ->
    get_reg (v1 A) A0r = Some pe -> base_syms A pe = [B] ->
    of_ca (ca_i_strlen_rgn P A pe B) = CR2OkN l ->
    post_concl A spoff l nu regs mem ra.
  Proof.
    intros HG2 MEMO Hsp K1 K2 KW Hret Hra R2 Epe EBS HC.
    pose proof HG2 as (HG1 & HE & HM & HF2 & HDD & RGN & LIVE & BEL2 & GL2 & FI2 & MOK).
    pose proof (gamma2_lgamma _ _ _ _ _ _ _ _ HG2) as HL.
    pose proof (PO1 _ _ PO2) as PO. pose proof PO as (P0 & Psphi & PS & PF & PW & PR & PP & PB).
    pose proof HE as (HEV1 & HD2 & HFS & HZO & HKC).
    pose proof (proj1 (proj2 HG1)) as HM1. pose proof HM1 as (MF & MD & MP & MFM). pose proof (proj1 (proj2 (proj2 HG1))) as HF1.
    destruct (env_facts SEGS P E mem0 PO2 FSLEN FS_SOME A nu regs mem HG2) as (flen & fssl & EFS & [FS1 FS2] & FS3 & FS5 & APsf & HMsp & SPHI & Pfr & E1a & SP0al & SPLO).
    unfold HIGH_MEM_BEG, HIGH_MEM_END in *.
    set (usp := e_sp0 E1 + spoff) in *.
    assert (USP : SBz + 2224 <= usp < 2 ^ 64) by (unfold usp, SBz, P1, E1 in *; lia).
    assert (JOK : forall a, usp - JUNK5 <= a < usp -> store_ok SEGS mem (wordZ a) 1 = true).
    { intros a Ha. unfold JUNK5 in Ha. apply (proj1 (MF a ltac:(unfold usp, P1, E1 in *; lia))). }
    pose proof (reg_val SEGS P1 E1 (zpatch P E mem0 mem) (v1 A) nu regs mem 10%bv pe HG1 ltac:(vm_compute; lia) Epe) as [V10 B10].
    unfold ca_i_strlen_rgn in HC. cbv zeta in HC.
    destruct (Z.eqb_spec (lcoef pe B) 1) as [C1|]; cbn [negb orb] in HC; [|discriminate HC].
    destruct (Z.eqb_spec (lcoef pe SP0) 0) as [C2|]; cbn [negb andb orb] in HC; [|discriminate HC].
    destruct (Z.eqb_spec (lcoef pe DATA) 0) as [C3|]; cbn [negb andb orb] in HC; [|discriminate HC].
    destruct (rgn_get (vs_rgn A) B) as [r|] eqn:HGr; [|discriminate HC].
    pose proof (rgn_get_in _ _ _ HGr) as [Hr HBr].
    destruct (rk_app (vr_kind r)) eqn:RKA; cbn [negb] in HC; [|discriminate HC].
    assert (HK : match vr_kind r with RK_fake _ _ | RK_arg => True | _ => False end) by (destruct (vr_kind r); first [exact I | discriminate RKA]).
    assert (NSH : is_shadow r = false) by (unfold is_shadow; destruct (vr_kind r); first [reflexivity | contradiction]).
    set (off := laddc (lsub pe (lsym B)) (- vr_disp r)) in *.
    assert (Eoff : eval nu pe = rbase nu r + eval nu off) by (unfold off; rewrite <- HBr, eval_off; lia).
    destruct (dead_lin (v1 A) off) eqn:Ed; [discriminate HC|].
    pose proof (bnd_sound (v1 A) nu off HL) as Hbd. unfold lo_of, hi_of in HC.
    destruct (bnd (v1 A) off) as [[plo|] [phi|]]; try discriminate HC. cbn [fst snd] in HC.
    destruct Hbd as [Hplo Hphi]; cbn [fst snd lo_le hi_ge] in Hplo, Hphi.
    destruct (rgn_nul_bound r phi) as [H|] eqn:Enb; [|discriminate HC].
    destruct (Z.ltb_spec plo (vr_lo r)) as [|RLO]; [discriminate HC|].
    destruct (Z.ltb_spec (vr_hi r) (H + 1)) as [|RHI]; cbn [orb] in HC; [discriminate HC|].
    destruct (rgn_addressable A r plo (H + 1)) eqn:HRA; cbn [negb] in HC; [|discriminate HC].
    destruct (frames_shadow_zone_ok P) eqn:HFZ; cbn [negb andb] in HC; [|discriminate HC].
    destruct (frames_zone_ok P) eqn:HFZB; cbn [negb] in HC; [|discriminate HC].
    destruct (rgn_nul_bound_sound SEGS P E mem0 A nu regs mem r phi H HG2 Hr NSH Enb) as (z & bz & Hz1 & Hz2 & Rz & Uz).
    set (ov := eval nu off) in *. set (x := rbase nu r + ov) in *.
    destruct (rgn_str_facts SEGS P E mem0 PO2 SHOFF ROM_HI FSLEN FS_SOME 2224 JUNK5 HKJ5 A nu regs mem spoff B r plo H ov z bz HG2 HGr HK RLO ltac:(lia) HRA HFZ HFZB
                ltac:(unfold ov; lia) ltac:(unfold ov; lia) ltac:(lia) Rz Uz K1 K2) as (buf & SF & HRB).
    fold x in SF, HRB. pose proof SF as (_ & _ & HR2 & HR1 & _).   (* [comment removed for export] *)
    assert (R10 : getr regs 10%bv = wordZ x).
    { apply wordZ_eq_u. rewrite V10, Eoff. fold ov. fold x. apply zwrap_id. lia. }
    destruct (RUN mem x usp (z - ov) buf regs ra (MCELLS_OK _ _ _ _ HG2) SF USP JOK Hret Hra R2 R10)
      as (regs' & i & m' & MS & Hi & Zi & NZi & Q10 & Q2 & Q1 & QK & QM & QG).
    (* [comment removed for export] *)
    pose proof (fresh_sym_box_sound (v1 A) nu (Some 0, Some (H - plo)) i HL ltac:(split; cbn; unfold ov in *; lia)) as FS.
    destruct (fresh_sym (v1 A)) as [s A1']. set (A2 := asetbox A1' s (Some 0, Some (H - plo))) in *.
    destruct FS as (X1 & L2 & V2 & S2 & N2).
    assert (FIN : forall A3, aext (v1 A) A3 nu (vupd nu s i) -> lgamma A3 (vupd nu s i) -> (s < vs_next A3)%positive ->
                  l = [(with_v1 A A3, Some (lsym s))] -> post_concl A spoff l nu regs mem ra).
    { intros A3 X3 L3 S3 ->.
      destruct (post_val SEGS P E mem0 rom PO2 FSLEN FS_SOME 2224 JUNK5 HKJ5 C_i_strlen A spoff nu (vupd nu s i) regs regs' mem m' A3 (lsym s) i eq_refl HG2 MEMO K1 K2 KW X3 L3
                  ltac:(rewrite eval_lsym; exact V2) ltac:(apply lin_below_lsym; exact S3) ltac:(rewrite Q10, u_Z_to_bv64; reflexivity) QK QM QG)
        as (G & Y1 & Y2 & Y3 & Y4).
      exists (with_v1 A A3), (Some (lsym s)), regs', m', (vupd nu s i).
      split; [left; reflexivity|]. split; [exact MS|]. split; [exact G|]. split; [exact Q1|]. auto. }
    cbv iota beta zeta in HC.
    destruct (lin_is_const off) eqn:Ec.
    + cbn [of_ca ca_ok1] in HC. injection HC as <-. exact (FIN A2 X1 L2 S2 eq_refl).
    + pose proof (aassume_sound A2 (vupd nu s i) (laddc (ladd (lsym s) off) (- H)) L2) as AS.
      destruct (aassume A2 _) as [ok A3] eqn:Eas. cbn [fst snd] in AS.
      assert (Hle : eval (vupd nu s i) (laddc (ladd (lsym s) off) (- H)) <= 0).
      { rewrite eval_laddc, eval_ladd, eval_lsym, V2.
        rewrite (eval_ext_below (vs_next (v1 A)) nu (vupd nu s i) off (proj1 X1)).
        2:{ unfold off. apply lin_below_laddc, lin_below_lsub; [exact B10|]. apply lin_below_lsym.
            destruct BEL2 as (_ & BR & _). rewrite <- HBr. exact (proj1 (BR r Hr)). }
        fold ov. unfold ov in *. lia. }
      destruct (AS Hle) as (Hok & L3 & X3).
      { apply lin_below_laddc, lin_below_ladd; [apply lin_below_lsym; exact S2|].
        eapply lin_below_mono; [exact (proj1 (proj2 X1))|]. unfold off. apply lin_below_laddc, lin_below_lsub; [exact B10|].
        apply lin_below_lsym. destruct BEL2 as (_ & BR & _). rewrite <- HBr. exact (proj1 (BR r Hr)). }
      subst ok. cbn [of_ca ca_ok1] in HC. injection HC as <-.
      apply (FIN A3); [eapply aext_trans; [exact X1|exact X3] | exact L3 | destruct X3 as (_ & X3b & _); clear -X3b S2; lia | reflexivity].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem i_strlen_post : contract_post2 SEGS P E mem0 rom CI C_i_strlen tgt.
  Proof.
    intros A spoff l nu regs mem ra HC HG2 MEMO Hsp HK Hret Hra.
    pose proof HG2 as (HG1 & HE & _). pose proof (PO1 _ _ PO2) as PO. pose proof PO as (P0 & Psphi & PS & PF & PW & PR & PP & PB).
    pose proof HE as (HEV1 & _). pose proof HEV1 as (E1a & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E11 & E12).
    pose proof (proj1 (proj2 (proj2 HG1))) as HF1.
    assert (HKR : - vp_frame P1 <= spoff - 2224 /\ spoff <= 0 /\ exists wr, In wr (vp_wstack P1) /\ fst wr <= spoff - 2224 /\ spoff <= snd wr).
    { destruct HK as [HK'|HK']; [cbn in HK'; discriminate|]. apply in_ranges_sound in HK' as (wlo & whi & Hw & W1 & W2).
      destruct (PR _ Hw). cbn [fst snd contract2_K] in *. unfold K_i_strlen, P1, E1 in *. split; [lia|]. split; [lia|].
      exists (wlo, whi). cbn. split; [exact Hw|lia]. }
    destruct HKR as (K1 & K2 & KW).
    assert (R2 : getr regs 2%bv = wordZ (e_sp0 E1 + spoff)).
    { apply (reg_word SEGS P1 E1 (zpatch P E mem0 mem) (v1 A) nu regs mem 2%bv (lsymc SP0 spoff) (e_sp0 E1 + spoff) HG1);
        [vm_compute; lia|exact Hsp| |unfold P1, E1 in *; lia].
      rewrite eval_lsymc. rewrite (HF1 SP0 (e_sp0 E1)) by reflexivity. reflexivity. }
    cbn [contract_apply2] in HC. unfold ca_i_strlen in HC.
    destruct (get_reg2 A A0r) as [pe|] eqn:Epe; [|discriminate HC]. unfold get_reg2 in Epe.
    destruct (base_syms A pe) as [|B0 [|B1 Bt]] eqn:EBS; [| |discriminate HC].
    - destruct (ptr_candidates (v1 A) pe) as [[|c1 [|c2 ct]]|] eqn:EPC; cbv iota beta in HC;
        first [ exact (post_cands A spoff l nu regs mem ra pe _ HG2 MEMO Hsp K1 K2 KW Hret Hra R2 Epe EPC HC)
              | exact (post_v1 A spoff l nu regs mem ra pe HG2 MEMO Hsp K1 K2 KW Hret Hra R2 Epe HC) ].
    - exact (post_rgn5 A spoff l nu regs mem ra pe B0 HG2 MEMO Hsp K1 K2 KW Hret Hra R2 Epe EBS HC).
  Qed.

  Theorem i_strlen_dead : contract_dead2 SEGS P E mem0 CI C_i_strlen.
  Proof.
    intros A spoff nu regs mem HC HG2.
    pose proof HG2 as (HG1 & HE & HM & HF2 & HDD & RGN & LIVE & BEL2 & GL2 & FI2 & MOK).
    pose proof (gamma2_lgamma _ _ _ _ _ _ _ _ HG2) as HL.
    pose proof (PO1 _ _ PO2) as PO.
    pose proof HE as (HEV1 & _). pose proof (proj1 (proj2 HG1)) as HM1. pose proof (proj1 (proj2 (proj2 HG1))) as HF1.
    cbn [contract_apply2] in HC. unfold ca_i_strlen in HC.
    destruct (get_reg2 A A0r) as [pe|] eqn:Epe; [|discriminate HC]. unfold get_reg2 in Epe.
    pose proof (reg_val SEGS P1 E1 (zpatch P E mem0 mem) (v1 A) nu regs mem 10%bv pe HG1 ltac:(vm_compute; lia) Epe) as [V10 B10].
    destruct (base_syms A pe) as [|B0 [|B1 Bt]] eqn:EBS; [| |discriminate HC].
    - assert (HC' : of_ca (ca_i_strlen_v1 P A pe) = CR2Dead).
      { destruct (ptr_candidates (v1 A) pe) as [[|c1 [|c2 ct]]|] eqn:EPC; cbv iota beta in HC; try exact HC.
        exfalso. unfold ca_i_strlen_cands in HC. destruct (rodata_cands _ _ _ _) as [[klo khi]|]; [|discriminate HC].
        destruct (afresh _ _) as [v B1]. discriminate HC. }
      clear HC. unfold ca_i_strlen_v1 in HC'. cbv zeta in HC'. unfold c_strlen, getA in HC'. rewrite Epe in HC'.
      destruct (rodata_cstr_len (p1 P) (Some pe)) as [k|] eqn:Ecs.
      + destruct (in_ranges (vp_segs (p1 P)) (lc pe) (k + 8)); cbv iota beta in HC'; [|discriminate HC'].
        destruct (img_str_ok P (lc pe) k); discriminate HC'.
      + destruct (is_sp_rel pe); [|discriminate HC']. cbn [negb] in HC'.
        destruct (dead_lin (v1 A) (lsub pe (lsym SP0))) eqn:Ed; [exact (dead_lin_false (v1 A) nu _ HL Ed)|].
        pose proof (bnd_sound (v1 A) nu (lsub pe (lsym SP0)) HL) as Hbd. unfold lo_of, hi_of in HC'.
        destruct (bnd (v1 A) (lsub pe (lsym SP0))) as [[plo|] [phi|]]; try discriminate HC'.
        destruct Hbd as [Hplo Hphi]; cbn [fst snd lo_le hi_ge] in Hplo, Hphi. rewrite eval_lsub, eval_lsym, (HF1 SP0 (e_sp0 E1) eq_refl) in Hplo, Hphi.
        cbn [fst snd] in HC'.
        destruct (find_nul_bound (v1 A) phi) as [H|] eqn:Ef; [|discriminate HC'].
        destruct (Z.ltb_spec 0 (H + 8)); [discriminate HC'|]. destruct (Z.ltb_spec plo (- vp_frame (p1 P))); [discriminate HC'|].
        destruct (find_nul_bound_sound SEGS P1 E1 (zpatch P E mem0 mem) PO (v1 A) nu regs mem phi H HG1 Ef) as [z [bz (Hz1 & Hz2 & Rz & Uz)]].
        pose proof (fresh_sym_box_sound (v1 A) nu (Some 0, Some (H - plo)) 0 HL ltac:(split; cbn; lia)) as FS.
        destruct (fresh_sym (v1 A)) as [s A1']. set (A2 := asetbox A1' s (Some 0, Some (H - plo))) in *.
        destruct FS as (X1 & L2 & V2 & S2 & N2). cbv iota beta zeta in HC'.
        destruct (lin_is_const (lsub pe (lsym SP0))).
        { destruct (above_sp _ _ _); [|discriminate HC']. destruct (stack_addressable _ _ _); [|discriminate HC'].
          destruct (stack_shadow_words_ok _ _ _); discriminate HC'. }
        pose proof (aassume_sound A2 (vupd nu s 0) (laddc (ladd (lsym s) (lsub pe (lsym SP0))) (- H)) L2) as AS.
        destruct (aassume A2 _) as [ok A3] eqn:Eas. cbn [fst snd] in AS.
        assert (Hle : eval (vupd nu s 0) (laddc (ladd (lsym s) (lsub pe (lsym SP0))) (- H)) <= 0).
        { rewrite eval_laddc, eval_ladd, eval_lsym, V2, eval_lsub, eval_lsym.
          rewrite ((proj1 X1 : ext _ _ _) SP0) by (pose proof (proj1 (lg_below _ _ HL)); unfold LAST_FIXED, SP0 in *; lia).
          rewrite (HF1 SP0 (e_sp0 E1) eq_refl).
          rewrite (eval_ext_below (vs_next (v1 A)) nu (vupd nu s 0) pe (proj1 X1)) by exact B10. lia. }
        destruct (AS Hle ltac:(apply lin_below_laddc, lin_below_ladd; [apply lin_below_lsym; exact S2|apply lin_below_lsub; [eapply lin_below_mono; [exact (proj1 (proj2 X1))|exact B10]|apply lin_below_lsym; pose proof (proj1 (lg_below _ _ L2)); unfold LAST_FIXED, SP0 in *; lia]]))
          as (Hok & _). subst ok.
        destruct (above_sp _ _ _); [|discriminate HC']. destruct (stack_addressable _ _ _); [|discriminate HC'].
        destruct (stack_shadow_words_ok _ _ _); discriminate HC'.
    - unfold ca_i_strlen_rgn in HC. cbv zeta in HC.
      destruct (Z.eqb_spec (lcoef pe B0) 1) as [C1|]; cbn [negb orb] in HC; [|discriminate HC].
      destruct (Z.eqb_spec (lcoef pe SP0) 0) as [C2|]; cbn [negb andb orb] in HC; [|discriminate HC].
      destruct (Z.eqb_spec (lcoef pe DATA) 0) as [C3|]; cbn [negb andb orb] in HC; [|discriminate HC].
      destruct (rgn_get (vs_rgn A) B0) as [r|] eqn:HGr; [|discriminate HC].
      pose proof (rgn_get_in _ _ _ HGr) as [Hr HBr].
      destruct (rk_app (vr_kind r)) eqn:RKA; cbn [negb] in HC; [|discriminate HC].
      assert (NSH : is_shadow r = false) by (unfold is_shadow; destruct (vr_kind r); first [reflexivity | discriminate RKA]).
      set (off := laddc (lsub pe (lsym B0)) (- vr_disp r)) in *.
      assert (Eoff : eval nu pe = rbase nu r + eval nu off) by (unfold off; rewrite <- HBr, eval_off; lia).
      destruct (dead_lin (v1 A) off) eqn:Ed; [exact (dead_lin_false (v1 A) nu _ HL Ed)|].
      pose proof (bnd_sound (v1 A) nu off HL) as Hbd. unfold lo_of, hi_of in HC.
      destruct (bnd (v1 A) off) as [[plo|] [phi|]]; try discriminate HC. cbn [fst snd] in HC.
      destruct Hbd as [Hplo Hphi]; cbn [fst snd lo_le hi_ge] in Hplo, Hphi.
      destruct (rgn_nul_bound r phi) as [H|] eqn:Enb; [|discriminate HC].
      destruct (Z.ltb_spec plo (vr_lo r)) as [|RLO]; [discriminate HC|].
      destruct (Z.ltb_spec (vr_hi r) (H + 1)) as [|RHI]; cbn [orb] in HC; [discriminate HC|].
      destruct (rgn_addressable A r plo (H + 1)); cbn [negb] in HC; [|discriminate HC].
      destruct (frames_shadow_zone_ok P); cbn [negb andb] in HC; [|discriminate HC].
      destruct (frames_zone_ok P); cbn [negb] in HC; [|discriminate HC].
      destruct (rgn_nul_bound_sound SEGS P E mem0 A nu regs mem r phi H HG2 Hr NSH Enb) as (z & bz & Hz1 & Hz2 & Rz & Uz).
      pose proof (fresh_sym_box_sound (v1 A) nu (Some 0, Some (H - plo)) 0 HL ltac:(split; cbn; lia)) as FS.
      destruct (fresh_sym (v1 A)) as [s A1']. set (A2 := asetbox A1' s (Some 0, Some (H - plo))) in *.
      destruct FS as (X1 & L2 & V2 & S2 & N2). cbv iota beta zeta in HC.
      destruct (lin_is_const off); [discriminate HC|].
      assert (Boff : lin_below off (vs_next (v1 A)) = true).
      { unfold off. apply lin_below_laddc, lin_below_lsub; [exact B10|]. apply lin_below_lsym.
        destruct BEL2 as (_ & BR & _). rewrite <- HBr. exact (proj1 (BR r Hr)). }
      pose proof (aassume_sound A2 (vupd nu s 0) (laddc (ladd (lsym s) off) (- H)) L2) as AS.
      destruct (aassume A2 _) as [ok A3] eqn:Eas. cbn [fst snd] in AS.
      assert (Hle : eval (vupd nu s 0) (laddc (ladd (lsym s) off) (- H)) <= 0).
      { rewrite eval_laddc, eval_ladd, eval_lsym, V2. rewrite (eval_ext_below (vs_next (v1 A)) nu (vupd nu s 0) off (proj1 X1) Boff). lia. }
      destruct (AS Hle) as (Hok & _).
      { apply lin_below_laddc, lin_below_ladd; [apply lin_below_lsym; exact S2|]. eapply lin_below_mono; [exact (proj1 (proj2 X1))|exact Boff]. }
      subst ok. discriminate HC.
  Qed.
End S.
