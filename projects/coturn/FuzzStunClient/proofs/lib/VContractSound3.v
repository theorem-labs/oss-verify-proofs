(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Bool Lia String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim StoreOk.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Frame.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import SeqExec Hoare ZStores RefMemcpyLib.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VLinalg VWord2 VState VLogic VAbs VAbsSound VAbsSound2 VAbsSound3 VStep VStepMem VGamma VStepSound VStepMemSound VStepMemSound2 VCert VContract VContractSound VContractSound2.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import LiaKeep.  (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

Notation B0 := (Z_to_bv 8 0).

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma min_opt_spec l m : min_opt l = Some m -> In m l /\ forall x, In x l -> m <= x.
Proof.
  revert m. induction l as [|x t IH]; intros m H; cbn [min_opt] in H; [discriminate|].
  destruct (min_opt t) as [m'|] eqn:E.
  - injection H as <-. destruct (IH m' eq_refl) as [Hin Hmin].
    split; [destruct (Z.min_spec x m') as [[_ ->]|[_ ->]]; [left; reflexivity|right; exact Hin]|].
    intros y [<-|Hy]; [lia|]. pose proof (Hmin y Hy). lia.
  - injection H as <-. split; [left; reflexivity|]. intros y [<-|Hy]; [lia|].
    exfalso. destruct t; [destruct Hy|]. cbn [min_opt] in E. destruct (min_opt t); discriminate.
Qed.

Lemma rom_cstr_len_spec rom fuel : forall a k0 k,
  rom_cstr_len rom a fuel k0 = Some k ->
  exists m, 0 <= m /\ k = k0 + m /\
    (forall j, 0 <= j < m -> 0 < a + j /\ exists b, pm_get (Z.to_pos (a + j)) rom = Some b /\ b <> 0) /\
    (0 < a + m /\ pm_get (Z.to_pos (a + m)) rom = Some 0).
Proof.
  induction fuel as [|f IH]; intros a k0 k H; cbn [rom_cstr_len] in H; [discriminate|].
  destruct (Z.ltb_spec 0 a); [|discriminate].
  destruct (pm_get (Z.to_pos a) rom) as [b|] eqn:Eb; [|discriminate].
  destruct (Z.eqb_spec b 0) as [->|Hb].
  - injection H as <-. exists 0. split; [lia|]. split; [lia|]. split; [intros; lia|]. rewrite Z.add_0_r. auto.
  - destruct (IH _ _ _ H) as [m (Hm&Hk&Hj&Hz)]. exists (m + 1). split; [lia|]. split; [lia|]. split.
    + intros j Hj0. destruct (Z.eq_dec j 0) as [->|Hjn].
      * rewrite Z.add_0_r. split; [lia|]. exists b. auto.
      * destruct (Hj (j - 1) ltac:(lia)) as [P [b' Q]]. replace (a + 1 + (j - 1)) with (a + j) in * by lia. split; [lia|]. exists b'. exact Q.
    + replace (a + (m + 1)) with (a + 1 + m) by lia. exact Hz.
Qed.

Lemma const_zero_byte_spec o val sz : forall i phi z,
  const_zero_byte o val i sz phi = Some z ->
  exists i', (i <= i' < i + sz)%nat /\ z = o + Z.of_nat i' /\ phi <= z /\ Z.land (Z.shiftr val (8 * Z.of_nat i')) 255 = 0.
Proof.
  induction sz as [|sz IH]; intros i phi z H; cbn [const_zero_byte] in H; [discriminate|].
  destruct (Z.leb_spec phi (o + Z.of_nat i)); destruct (Z.eqb_spec (Z.land (Z.shiftr val (8 * Z.of_nat i)) 255) 0); cbn [andb] in H.
  - injection H as <-. exists i. repeat split; auto; lia.
  - destruct (IH _ _ _ H) as [i' (A&B&C&D)]. exists i'. repeat split; auto; lia.
  - destruct (IH _ _ _ H) as [i' (A&B&C&D)]. exists i'. repeat split; auto; lia.
  - destruct (IH _ _ _ H) as [i' (A&B&C&D)]. exists i'. repeat split; auto; lia.
Qed.

Lemma slot_zero_bytes_spec slots phi z :
  In z (slot_zero_bytes slots phi) ->
  exists o sz v i', In (o, (sz, Some v)) slots /\ lin_is_const v = true /\ (i' < Z.to_nat sz)%nat /\
    z = o + Z.of_nat i' /\ phi <= z /\ Z.land (Z.shiftr (Z.land (lc v) (2 ^ (8 * sz) - 1)) (8 * Z.of_nat i')) 255 = 0.
Proof.
  unfold slot_zero_bytes. rewrite in_flat_map. intros [[o [sz [v|]]] [Hin Hz]]; [|destruct Hz].
  destruct (lin_is_const v && (phi <=? o + sz - 1)) eqn:E; [|destruct Hz]. apply andb_prop in E as [Ec _].
  destruct (const_zero_byte o _ 0 (Z.to_nat sz) phi) as [z0|] eqn:Ecz; [|destruct Hz].
  destruct Hz as [<-|[]]. destruct (const_zero_byte_spec _ _ _ _ _ _ Ecz) as [i' (A&B&C&D)].
  exists o, sz, v, i'. repeat split; auto. lia.
Qed.

(* [comment removed for export] *)
Lemma nth_byte_val bs : forall j, (j < length bs)%nat ->
  bv_unsigned (nth j bs B0) = (bytes_le_to_Z bs / 2 ^ (8 * Z.of_nat j)) mod 256.
Proof.
  induction bs as [|b bs IH]; intros j Hj; [cbn in Hj; lia|].
  pose proof (u8_range b) as Hb. pose proof (bytes_le_to_Z_nonneg bs) as Hnn.
  assert (Hcons : bytes_le_to_Z (b :: bs) = bv_unsigned b + 256 * bytes_le_to_Z bs).
  { cbn [bytes_le_to_Z]. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256. rewrite Z.lor_comm.
    rewrite (lor_disjoint _ _ 8); [lia | lia | apply Z.mul_nonneg_nonneg; lia
      | change (2 ^ 8) with 256; apply Z.mod_mul; lia | change (2 ^ 8) with 256; lia]. }
  destruct j as [|j].
  - cbn [nth]. rewrite Hcons. rewrite Z.mul_0_r, Z.pow_0_r, Z.div_1_r. rewrite Z.mul_comm, Z.mod_add by lia. symmetry. apply Z.mod_small. lia.
  - cbn [nth]. cbn in Hj. rewrite (IH j) by lia. rewrite Hcons. f_equal.
    replace (8 * Z.of_nat (S j)) with (8 + 8 * Z.of_nat j) by lia. rewrite Z.pow_add_r by lia. change (2 ^ 8) with 256.
    rewrite <- Z.div_div by (try apply pow2_pos; lia). f_equal.
    rewrite Z.mul_comm, Z.div_add by lia. rewrite Z.div_small by lia. lia.
Qed.

(* [comment removed for export] *)
Section CS3.
  Variable SEGS : list Segment.
  Variable P : vparams.
  Variable E : venv.
  Variable mem0 : word -> option byte.
  Variable rom : word -> option byte.
  Variable CI : cimg.
  Hypothesis PO : params_ok SEGS P.

  Notation gammaP := (gamma SEGS P E mem0).
  Notation MCP := (MC SEGS P E mem0).

  (* [comment removed for export] *)
  Lemma rom_byte_sound mem a b :
    env_ok P E -> MCP mem -> 0 < a -> pm_get (Z.to_pos a) (vp_rom P) = Some b ->
    exists bb, rdn SEGS mem (wordZ a) 1 = Some [bb] /\ bv_unsigned bb = b /\ 0 <= a < vp_splo P - vp_frame P.
  Proof.
    intros HE HM Ha Hg. pose proof PO as (P0&P1&PS&PF&PW&PR&PP&PB).
    destruct (PB a b Ha Hg) as [Hpr [bb [Hrom Hbb]]]. destruct (in_ranges_sound _ _ _ Hpr) as [plo [phi (Hin&Q1&Q2)]].
    destruct (PP _ _ Hin). destruct HM as (MF&MD&MP&MFM).
    exists bb. rewrite rdn_1, (MP plo phi a Hin ltac:(lia)), Hrom. split; [reflexivity|]. split; [exact Hbb|lia].
  Qed.

  (* [comment removed for export] *)
  Lemma rodata_cstr_sound mem p k :
    env_ok P E -> MCP mem -> rodata_cstr_len P p = Some k ->
    exists e, p = Some e /\ lin_is_const e = true /\ 0 <= k /\ 0 < lc e /\ lc e + k < vp_splo P - vp_frame P /\
      (forall j, 0 <= j < k -> exists bb, rdn SEGS mem (wordZ (lc e + j)) 1 = Some [bb] /\ bv_unsigned bb <> 0) /\
      (exists bb, rdn SEGS mem (wordZ (lc e + k)) 1 = Some [bb] /\ bv_unsigned bb = 0).
  Proof.
    intros HE HM H. unfold rodata_cstr_len in H. destruct p as [e|]; [|discriminate].
    destruct (lin_is_const e) eqn:Ec; [|discriminate]. destruct (in_ranges (vp_pristine P) (lc e) 1); [|discriminate].
    destruct (rom_cstr_len_spec _ _ _ _ _ H) as [m (Hm&->&Hj&(Hzp&Hz))].
    exists e. split; [reflexivity|]. split; [exact Ec|]. split; [lia|].
    destruct (rom_byte_sound mem _ _ HE HM Hzp Hz) as [bz (Rz&Uz&Az)].
    split; [destruct (Z.eq_dec m 0) as [->|]; [lia|]; destruct (Hj 0 ltac:(lia)) as [X _]; lia|].
    split; [lia|]. split.
    - intros j Hj0. destruct (Hj j ltac:(lia)) as [Pj [b (Gb&Nb)]]. destruct (rom_byte_sound mem _ _ HE HM Pj Gb) as [bb (Rb&Ub&Ab)].
      exists bb. rewrite Z.add_0_l in *. split; [exact Rb|lia].
    - exists bz. rewrite Z.add_0_l. split; [exact Rz|exact Uz].
  Qed.

  (* [comment removed for export] *)
  Lemma rdn_bytes_vals mem a (k : nat) (Q : Z -> byte -> Prop) :
    0 <= a -> a + Z.of_nat k <= 2 ^ 64 ->
    (forall j, 0 <= j < Z.of_nat k -> exists b, rdn SEGS mem (wordZ (a + j)) 1 = Some [b] /\ Q j b) ->
    exists bs, rdn SEGS mem (wordZ a) k = Some bs /\ length bs = k /\ forall j, (j < k)%nat -> Q (Z.of_nat j) (nth j bs B0).
  Proof.
    intros Ha Hk HQ. destruct (rdn_bytes SEGS mem a k Ha Hk) as [bs [Hbs Hlen]].
    { intros j Hj. destruct (HQ j Hj) as [b [Hb _]]. eauto. }
    exists bs. split; [exact Hbs|]. split; [exact Hlen|]. intros j Hj.
    destruct (HQ (Z.of_nat j) ltac:(lia)) as [b [Hb HQb]].
    pose proof (rdn_nth SEGS mem k (wordZ a) bs j Hbs Hj) as X.
    replace (wordZ a + nat_to_word j)%bv with (wordZ (a + Z.of_nat j)) in X by (symmetry; apply wordZ_add_nat).
    rewrite Hb in X. injection X as ->. exact HQb.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Variable a_strcmp : Z.
  Hypothesis STRCMP : forall mem (l r : word) (K : nat) (la lb : list byte) regs (ret : word),
    rdn SEGS mem l (S K) = Some la -> rdn SEGS mem r (S K) = Some lb ->
    bv_unsigned (nth K lb B0) = 0 ->
    bv_unsigned l + Z.of_nat K < 2 ^ 64 -> bv_unsigned r + Z.of_nat K < 2 ^ 64 ->
    ret_ok ret -> getr regs 1%bv = ret -> getr regs 10%bv = l -> getr regs 11%bv = r ->
    exists regs' (dlt : Z),
      msteps SEGS (mkst regs (wordZ a_strcmp) mem rom) (mkst regs' ret mem rom)
      /\ (forall x : reg, bv_unsigned x <> 0 -> ~ In (bv_unsigned x) CALLER_SAVED -> getr regs' x = getr regs x)
      /\ getr regs' 1%bv = getr regs 1%bv
      /\ - 255 <= dlt <= 255 /\ getr regs' 10%bv = Z_to_bv 64 dlt.

  #[using="PO STRCMP"] Theorem strcmp_post : contract_post SEGS P E mem0 rom CI C_strcmp a_strcmp.
  Proof.
    intros A spoff A1 v nu regs mem ra Happ HGm Hsp HKw Hret Hra.
    pose proof (gamma_lgamma _ _ _ _ _ _ _ _ HGm) as HL.
    pose proof HGm as (HE&HM&HF&HS&HC&HMo&HV&HR&HSl&HG&HN&HB).
    pose proof HE as (E1&E2&E3&E4&E5&E6&E7&E8&E9&E11&E12). pose proof PO as (P0&P1&PS&_).
    cbn [contract_apply] in Happ. unfold c_strcmp, getA in Happ.
    destruct (rodata_cstr_len P (get_reg A A1r)) as [kb|] eqn:Ecs; [|discriminate].
    destruct (rodata_cstr_sound mem _ _ HE HM Ecs) as [be (Ebe&Cbe&Hkb&Hb0&Hbk&NZ&ZK)]. rewrite Ebe in Happ.
    destruct (get_reg A A0r) as [ae|] eqn:Eae; [|discriminate].
    destruct (in_ranges (vp_segs P) (lc be) (kb + 1)) eqn:Esg; [|discriminate]. cbn [negb] in Happ.
    pose proof (readable_range_sound SEGS P E mem0 PO A nu regs mem ae (lconst (kb + 1)) _ HGm ltac:(rewrite eval_lconst; lia) eq_refl) as RA.
    assert (MAIN : readable SEGS mem (eval nu ae) (kb + 1) ->
              (let '(v0, A1') := afresh A (Some (-255), Some 255) in CROk A1' v0) = CROk A1 v ->
              exists regs' mem' nu',
                msteps SEGS (mkst regs (wordZ a_strcmp) mem rom) (mkst regs' ra mem' rom) /\
                gammaP (contract_frame C_strcmp A1 spoff v) nu' regs' mem' /\ getr regs' 1%bv = ra /\
                ext (vs_next A) nu nu' /\ (vs_next A <= vs_next (contract_frame C_strcmp A1 spoff v))%positive /\
                frame_mod mem mem' (unit_regions P E)).
    { intros RA' EQ.
      (* [comment removed for export] *)
      destruct RA' as (Ra0&Ra1&RaB).
      destruct (rdn_bytes_vals mem (eval nu ae) (S (Z.to_nat kb)) (fun _ _ => True) Ra0 ltac:(lia)) as [la (Hla&Lla&_)].
      { intros j Hj. destruct (RaB j ltac:(lia)) as [b Hb]. eauto. }
      destruct (rdn_bytes_vals mem (lc be) (S (Z.to_nat kb)) (fun j b => j = kb -> bv_unsigned b = 0) ltac:((ltac2:(LK.k [@E3; @E4; @E5; @E7; @E8; @E9; @E11; @Hb0; @Lla; @E1; @E2; @P0; @P1; @Hkb; @Hbk]); lia)) ltac:((ltac2:(LK.k [@E3; @E4; @E5; @E7; @E8; @E9; @E11; @Hb0; @Lla; @E1; @E2; @P0; @P1; @Hkb; @Hbk]); lia))) as [lb (Hlb&Llb&QB)].
      { intros j Hj. destruct (Z.eq_dec j kb) as [->|Hne].
        - destruct ZK as [bb [Rb Ub]]. exists bb. auto.
        - destruct (NZ j ltac:(lia)) as [bb [Rb Ub]]. exists bb. split; [exact Rb|intros; lia]. }
      assert (R10 : getr regs 10%bv = wordZ (eval nu ae)) by (apply (reg_word SEGS P E mem0 A nu regs mem 10%bv ae _ HGm); [vm_compute; (ltac2:(LK.k [@E3; @E7; @E8; @E9; @E11; @Lla; @Llb; @E4; @E5; @Hkb; @Ra0; @Ra1]); lia)|exact Eae|reflexivity|(ltac2:(LK.k [@E3; @E7; @E8; @E9; @E11; @Lla; @Llb; @E4; @E5; @Hkb; @Ra0; @Ra1]); lia)]).
      assert (R11 : getr regs 11%bv = wordZ (lc be)).
      { apply (reg_word SEGS P E mem0 A nu regs mem 11%bv be _ HGm); [vm_compute; (ltac2:(LK.k [@E3; @E7; @E8; @E9; @E11; @Lla; @Llb; @E1; @E2; @E4; @E5; @P0; @P1; @Hkb; @Hb0; @Hbk]); lia)|exact Ebe|apply eval_is_const; exact Cbe|(ltac2:(LK.k [@E3; @E7; @E8; @E9; @E11; @Lla; @Llb; @E1; @E2; @E4; @E5; @P0; @P1; @Hkb; @Hb0; @Hbk]); lia)]. }
      destruct (STRCMP mem (wordZ (eval nu ae)) (wordZ (lc be)) (Z.to_nat kb) la lb regs ra Hla Hlb
                  (QB (Z.to_nat kb) ltac:((ltac2:(LK.k [@E3; @E7; @E8; @E9; @E11; @Lla; @Llb; @E1; @E2; @E4; @E5; @P0; @Hkb; @Hb0; @Hbk; @Ra1; @Ra0; @P1]); lia)) ltac:((ltac2:(LK.k [@E3; @E7; @E8; @E9; @E11; @Lla; @Llb; @E1; @E2; @E4; @E5; @P0; @Hkb; @Hb0; @Hbk; @Ra1; @Ra0; @P1]); lia))) ltac:(rewrite u_wordZ; (ltac2:(LK.k [@E3; @E7; @E8; @E9; @E11; @Lla; @Llb; @E1; @E2; @E4; @E5; @P0; @Hkb; @Hb0; @Hbk; @Ra1; @Ra0; @P1]); lia)) ltac:(rewrite u_wordZ; (ltac2:(LK.k [@E3; @E7; @E8; @E9; @E11; @Lla; @Llb; @E1; @E2; @E4; @E5; @P0; @Hkb; @Hb0; @Hbk; @Ra1; @Ra0; @P1]); lia)) Hret Hra R10 R11)
        as [regs' [dlt (RUN&HKr&Hra'&Hd&R10')]].
      pose proof (afresh_sound A nu (Some (-255), Some 255) dlt HL ltac:(split; cbn; lia)) as FR.
      destruct (afresh A (Some (-255), Some 255)) as [v1 A1x]. injection EQ as EA Ev. subst A1 v.
      destruct FR as [nu' (X1&L1&V1)]. destruct v1 as [e1|]; [|destruct V1]. destruct V1 as [V1 B1].
      exists regs', mem, nu'.
      destruct (gamma_call_post SEGS P E mem0 rom PO A (contract_frame C_strcmp A1x spoff (Some e1)) nu nu' regs regs' mem mem []
                  HGm (proj1 X1) ltac:(destruct (contract_frame_shape C_strcmp A1x spoff (Some e1)) as (_&_&_&_&F5&_); rewrite F5; exact (proj1 (proj2 X1)))
                  ltac:(apply lgamma_contract_frame; [exact L1|exact B1]))
        as [HG' FM'].
      - eapply (gamma_regs_contract_frame SEGS P E mem0 C_strcmp A A1x spoff (Some e1) nu nu' regs regs'); try eassumption.
        + right. split; [exact HR|destruct HB as (_&_&RBl&_); exact RBl].
        + exact (proj1 X1).
        + destruct X1 as (_&_&(SR&_)). exact SR.
        + rewrite R10', u_Z_to_bv64, V1. reflexivity.
      - intros off w v0 Hin. destruct (contract_frame_shape C_strcmp A1x spoff (Some e1)) as (F1&_). rewrite F1 in Hin. cbn in Hin.
        destruct X1 as (_&_&(_&SS&_)). rewrite SS in Hin. left. split; [exact Hin|intros x _; exact I].
      - intros ga w v0 Hin. destruct (contract_frame_shape C_strcmp A1x spoff (Some e1)) as (_&F2&_). rewrite F2 in Hin.
        destruct X1 as (_&_&(_&_&SG&_)). rewrite SG in Hin. split; [exact Hin|intros x _; exact I].
      - intros lo' hi' Hin. destruct (contract_frame_shape C_strcmp A1x spoff (Some e1)) as (_&_&F3&_). apply F3 in Hin as [Hin _].
        destruct X1 as (_&_&(_&_&_&SN&_)). rewrite SN in Hin. left. split; [exact Hin|intros x _; exact I].
      - apply frame_mod_refl.
      - intros x Hx. exfalso. apply Hx. exact I.
      - split; [exact RUN|]. split; [exact HG'|]. split; [rewrite Hra'; exact Hra|].
        split; [exact (proj1 X1)|]. split; [|exact FM'].
        destruct (contract_frame_shape C_strcmp A1x spoff (Some e1)) as (_&_&_&_&F5&_). rewrite F5. exact (proj1 (proj2 X1)). }
    destruct (readable_range P A ae (lconst (kb + 1))); try discriminate; try (destruct RA; fail).
    all: apply (MAIN ltac:(rewrite eval_lconst in RA; exact RA) Happ).
  Qed.

  Theorem strcmp_dead : contract_dead SEGS P E mem0 CI C_strcmp.
  Proof.
    intros A spoff nu regs mem Happ HGm. pose proof (gamma_lgamma _ _ _ _ _ _ _ _ HGm) as HL. pose proof HGm as (HE&HM&_).
    cbn [contract_apply] in Happ. unfold c_strcmp, getA in Happ.
    destruct (rodata_cstr_len P (get_reg A A1r)) as [kb|] eqn:Ecs; [|discriminate].
    destruct (rodata_cstr_sound mem _ _ HE HM Ecs) as [be (Ebe&Cbe&Hkb&_)]. rewrite Ebe in Happ.
    destruct (get_reg A A0r) as [ae|]; [|discriminate]. destruct (negb _); [discriminate|].
    pose proof (readable_range_sound SEGS P E mem0 PO A nu regs mem ae (lconst (kb + 1)) _ HGm ltac:(rewrite eval_lconst; lia) eq_refl) as RA.
    destruct (readable_range P A ae (lconst (kb + 1))); try discriminate; try exact RA.
    all: destruct (afresh A _); discriminate.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  #[using="PO"] Lemma find_nul_bound_sound A nu regs mem phi H :
    gammaP A nu regs mem -> find_nul_bound A phi = Some H ->
    exists z b, phi <= z <= H /\ (- vp_frame P <= z < 0) /\
                rdn SEGS mem (wordZ (e_sp0 E + z)) 1 = Some [b] /\ bv_unsigned b = 0.
  Proof.
    intros HGm Hf. pose proof HGm as (HE&HM&HF&HS&HC&HMo&HV&HR&HSl&HG&HN&HB).
    pose proof HE as (E1&E2&E3&E4&E5&E6&E7&E8&E9&E11&E12). pose proof PO as (P0&P1&_).
    unfold find_nul_bound in Hf.
    (* [comment removed for export] *)
    assert (FACT : forall bb, min_opt (map snd (List.filter (fun f : Z * Z => phi <=? fst f) (vs_nul A))) = Some bb ->
              exists z b, phi <= z <= bb /\ (- vp_frame P <= z < 0) /\ rdn SEGS mem (wordZ (e_sp0 E + z)) 1 = Some [b] /\ bv_unsigned b = 0).
    { intros bb Hm. destruct (min_opt_spec _ _ Hm) as [Hin _]. apply in_map_iff in Hin as [[lo hi] [Ehi Hin]]. cbn in Ehi. subst hi.
      apply filter_In in Hin as [Hin Hle]. cbn in Hle. apply Z.leb_le in Hle.
      destruct (HN _ _ Hin) as [z [b (Q1&Q2&Q3&Q4)]]. exists z, b. repeat split; auto; (ltac2:(LK.k [@E1; @E3; @E4; @E5; @E7; @E8; @E9; @E11; @E12; @Hle; @Q1; @Q2]); lia). }
    (* [comment removed for export] *)
    assert (SLOT : forall zz, min_opt (slot_zero_bytes (vs_slots A) phi) = Some zz ->
              exists b, phi <= zz /\ (- vp_frame P <= zz < 0) /\ rdn SEGS mem (wordZ (e_sp0 E + zz)) 1 = Some [b] /\ bv_unsigned b = 0).
    { intros zz Hm. destruct (min_opt_spec _ _ Hm) as [Hin _].
      destruct (slot_zero_bytes_spec _ _ _ Hin) as [o [sz [v [i' (Hsl&Hc&Hi&Ez&Hphi&Hbyte)]]]].
      destruct (HSl _ _ _ Hsl) as [(R1&R2&R3) CH]. cbn [cell_holds] in CH. destruct CH as [bs [Hbs Hval]].
      pose proof (rdn_length _ _ _ _ _ Hbs) as Hlen.
      pose proof (rdn_nth SEGS mem (Z.to_nat sz) (wordZ (e_sp0 E + o)) bs i' Hbs Hi) as Hb.
      rewrite wordZ_add_nat in Hb. rewrite Ez. replace (e_sp0 E + (o + Z.of_nat i')) with (e_sp0 E + o + Z.of_nat i') by lia.
      exists (nth i' bs B0). split; [lia|]. split; [lia|]. split; [exact Hb|].
      rewrite (nth_byte_val bs i') by lia. rewrite Hval, (eval_is_const nu v Hc).
      change 255 with (2 ^ 8 - 1) in Hbyte. rewrite !land_lowmask, Z.shiftr_div_pow2 in Hbyte by (ltac2:(LK.k [@E3; @E7; @E8; @E9; @E11; @Hi; @Hlen; @E1; @E4; @E5; @E12; @P0; @R2]); lia).
      unfold zwrap. change 256 with (2 ^ 8). exact Hbyte. }
    destruct (min_opt (map snd _)) as [bb|] eqn:M1; destruct (min_opt (slot_zero_bytes _ _)) as [zz|] eqn:M2; try discriminate; injection Hf as <-.
    - destruct (Z.min_spec bb zz) as [[_ ->]|[_ ->]].
      + destruct (FACT bb eq_refl) as [z [b X]]. exists z, b. exact X.
      + destruct (SLOT zz eq_refl) as [b (Y1&Y2&Y3&Y4)]. exists zz, b. repeat split; auto; lia.
    - destruct (FACT bb eq_refl) as [z [b X]]. exists z, b. exact X.
    - destruct (SLOT zz eq_refl) as [b (Y1&Y2&Y3&Y4)]. exists zz, b. repeat split; auto; lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Variable a_strlen rc_lo rc_hi : Z.
  (* [comment removed for export] *)
  Hypothesis RC_PRISTINE : exists plo phi, In (plo, phi) (vp_pristine P) /\ plo <= rc_lo /\ rc_hi <= phi.
  Hypothesis STRLEN : forall mem (s : word) (buf : list byte) (K : Z) regs (ret : word),
    rdn SEGS mem s (length buf) = Some buf -> 0 <= K -> K + 8 <= Z.of_nat (length buf) ->
    bv_unsigned s + Z.of_nat (length buf) < 2 ^ 64 -> bv_unsigned (nth (Z.to_nat K) buf B0) = 0 ->
    (forall i, rc_lo <= i < rc_hi -> mem (Z_to_bv 64 i) = None) ->
    ret_ok ret -> getr regs 1%bv = ret -> getr regs 10%bv = s ->
    exists regs' (i : Z),
      msteps SEGS (mkst regs (wordZ a_strlen) mem rom) (mkst regs' ret mem rom)
      /\ (forall x : reg, bv_unsigned x <> 0 -> ~ In (bv_unsigned x) CALLER_SAVED -> getr regs' x = getr regs x)
      /\ getr regs' 1%bv = getr regs 1%bv
      /\ 0 <= i <= K /\ bv_unsigned (nth (Z.to_nat i) buf B0) = 0
      /\ (forall j, 0 <= j < i -> bv_unsigned (nth (Z.to_nat j) buf B0) <> 0)
      /\ getr regs' 10%bv = Z_to_bv 64 i.

  Lemma rc_clear mem : MCP mem -> forall i, rc_lo <= i < rc_hi -> mem (Z_to_bv 64 i) = None.
  Proof.
    intros (MF&MD&MP&MFM) i Hi. destruct RC_PRISTINE as [plo [phi (Hin&Q1&Q2)]].
    exact (MP plo phi i Hin ltac:(lia)).
  Qed.

  (* [comment removed for export] *)
  Lemma strlen_finish A A1 nu nu' regs regs' mem spoff (ra : word) (v : absval) (i : Z) :
    gammaP A nu regs mem -> aext A A1 nu nu' -> lgamma A1 nu' ->
    match v with Some e => eval nu' e = i /\ lin_below e (vs_next A1) = true | None => False end ->
    0 <= i < 2 ^ 64 ->
    (forall x : reg, bv_unsigned x <> 0 -> ~ In (bv_unsigned x) CALLER_SAVED -> getr regs' x = getr regs x) ->
    getr regs' 1%bv = getr regs 1%bv -> getr regs 1%bv = ra -> getr regs' 10%bv = Z_to_bv 64 i ->
    gammaP (contract_frame C_strlen A1 spoff v) nu' regs' mem /\ getr regs' 1%bv = ra /\
    ext (vs_next A) nu nu' /\ (vs_next A <= vs_next (contract_frame C_strlen A1 spoff v))%positive /\
    frame_mod mem mem (unit_regions P E).
  Proof.
    intros HGm X1 L1 V1 Hi HKr Hra' Hra R10'.
    pose proof HGm as (HE&HM&HF&HS&HC&HMo&HV&HR&HSl&HG&HN&HB).
    destruct v as [e1|]; [|destruct V1]. destruct V1 as [V1 B1].
    destruct (gamma_call_post SEGS P E mem0 rom PO A (contract_frame C_strlen A1 spoff (Some e1)) nu nu' regs regs' mem mem []
                HGm (proj1 X1) ltac:(destruct (contract_frame_shape C_strlen A1 spoff (Some e1)) as (_&_&_&_&F5&_); rewrite F5; exact (proj1 (proj2 X1)))
                ltac:(apply lgamma_contract_frame; [exact L1|exact B1]))
      as [HG' FM'].
    - eapply (gamma_regs_contract_frame SEGS P E mem0 C_strlen A A1 spoff (Some e1) nu nu' regs regs'); try eassumption.
      + right. split; [exact HR|destruct HB as (_&_&RBl&_); exact RBl].
      + exact (proj1 X1).
      + destruct X1 as (_&_&(SR&_)). exact SR.
      + rewrite R10', u_Z_to_bv64, V1. rewrite ?(zwrap_id 64 i Hi). reflexivity.
    - intros off w v0 Hin. destruct (contract_frame_shape C_strlen A1 spoff (Some e1)) as (F1&_). rewrite F1 in Hin. cbn in Hin.
      destruct X1 as (_&_&(_&SS&_)). rewrite SS in Hin. left. split; [exact Hin|intros x _; exact I].
    - intros ga w v0 Hin. destruct (contract_frame_shape C_strlen A1 spoff (Some e1)) as (_&F2&_). rewrite F2 in Hin.
      destruct X1 as (_&_&(_&_&SG&_)). rewrite SG in Hin. split; [exact Hin|intros x _; exact I].
    - intros lo' hi' Hin. destruct (contract_frame_shape C_strlen A1 spoff (Some e1)) as (_&_&F3&_). apply F3 in Hin as [Hin _].
      destruct X1 as (_&_&(_&_&_&SN&_)). rewrite SN in Hin. left. split; [exact Hin|intros x _; exact I].
    - apply frame_mod_refl.
    - intros x Hx. exfalso. apply Hx. exact I.
    - split; [exact HG'|]. split; [rewrite Hra'; exact Hra|]. split; [exact (proj1 X1)|]. split; [|exact FM'].
      destruct (contract_frame_shape C_strlen A1 spoff (Some e1)) as (_&_&_&_&F5&_). rewrite F5. exact (proj1 (proj2 X1)).
  Qed.

  #[using="PO rc_lo rc_hi RC_PRISTINE STRLEN"] Theorem strlen_post : contract_post SEGS P E mem0 rom CI C_strlen a_strlen.
  Proof.
    intros A spoff A1 v nu regs mem ra Happ HGm Hsp HKw Hret Hra.
    pose proof (gamma_lgamma _ _ _ _ _ _ _ _ HGm) as HL.
    pose proof HGm as (HE&HM&HF&HS&HC&HMo&HV&HR&HSl&HG&HN&HB).
    pose proof HE as (E1&E2&E3&E4&E5&E6&E7&E8&E9&E11&E12). pose proof PO as (P0&P1&PS&_).
    cbn [contract_apply] in Happ. unfold c_strlen, getA in Happ.
    destruct (rodata_cstr_len P (get_reg A A0r)) as [k|] eqn:Ecs.
    - (* [comment removed for export] *)
      destruct (rodata_cstr_sound mem _ _ HE HM Ecs) as [pe (Epe&Cpe&Hk&Hp0&Hpk&NZ&ZK)]. rewrite Epe in Happ.
      destruct (in_ranges (vp_segs P) (lc pe) (k + 8)) eqn:Esg; [|discriminate]. injection Happ as <- <-.
      destruct (in_ranges_sound _ _ _ Esg) as [slo [shi (Hsin&Q1&Q2)]]. destruct (PS _ _ Hsin) as (S0&S1&SB).
      set (a := lc pe) in *.
      destruct (rdn_bytes_vals mem a (Z.to_nat (k + 8)) (fun j b => (j < k -> bv_unsigned b <> 0) /\ (j = k -> bv_unsigned b = 0)) ltac:(lia) ltac:(lia)) as [buf (Hbuf&Lbuf&Qbuf)].
      { intros j Hj. destruct (Z_lt_le_dec j k) as [Hjk|Hjk].
        - destruct (NZ j ltac:(lia)) as [bb [Rb Ub]]. exists bb. split; [exact Rb|]. split; [auto|intros; lia].
        - destruct (Z.eq_dec j k) as [->|Hne].
          + destruct ZK as [bb [Rb Ub]]. exists bb. split; [exact Rb|]. split; [intros; lia|auto].
          + destruct (rdn1_any SEGS mem (wordZ (a + j)) (SB (a + j) ltac:(lia))) as [bb Rb]. exists bb. split; [exact Rb|]. split; intros; lia. }
      assert (R10 : getr regs 10%bv = wordZ a).
      { apply (reg_word SEGS P E mem0 A nu regs mem 10%bv pe _ HGm); [vm_compute; lia|exact Epe|apply eval_is_const; exact Cpe|lia]. }
      destruct (STRLEN mem (wordZ a) buf k regs ra ltac:(rewrite Lbuf; exact Hbuf) ltac:((ltac2:(LK.k [@E3; @E4; @E5; @E7; @E8; @E9; @E11; @Hk; @Lbuf; @E1; @E2; @P0; @Hp0; @Q2; @S1; @P1]); lia)) ltac:(rewrite Lbuf; (ltac2:(LK.k [@E3; @E4; @E5; @E7; @E8; @E9; @E11; @Hk; @Lbuf; @E1; @E2; @P0; @Hp0; @Q2; @S1; @P1]); lia)) ltac:(rewrite u_wordZ, Lbuf; (ltac2:(LK.k [@E3; @E4; @E5; @E7; @E8; @E9; @E11; @Hk; @Lbuf; @E1; @E2; @P0; @Hp0; @Q2; @S1; @P1]); lia))
                  (proj2 (Qbuf (Z.to_nat k) ltac:((ltac2:(LK.k [@E3; @E4; @E5; @E7; @E8; @E9; @E11; @Hk; @Lbuf; @E1; @E2; @P0; @Hp0; @Q2; @S1; @P1]); lia))) ltac:((ltac2:(LK.k [@E3; @E4; @E5; @E7; @E8; @E9; @E11; @Hk; @Lbuf; @E1; @E2; @P0; @Hp0; @Q2; @S1; @P1]); lia))) (rc_clear mem HM) Hret Hra R10)
        as [regs' [i (RUN&HKr&Hra'&Hi&Zi&NZi&R10')]].
      assert (Ei : i = k).
      { destruct (Z_lt_le_dec i k) as [Hlt|]; [|lia]. exfalso. apply (proj1 (Qbuf (Z.to_nat i) ltac:((ltac2:(LK.k [@E3; @E4; @E5; @E7; @E8; @E9; @E11; @Hk; @Lbuf; @Hi; @Hlt; @E1; @E2; @P0; @Hp0; @Q2; @S1]); lia))) ltac:((ltac2:(LK.k [@E3; @E4; @E5; @E7; @E8; @E9; @E11; @Hk; @Lbuf; @Hi; @Hlt; @E1; @E2; @P0; @Hp0; @Q2; @S1]); lia))). exact Zi. }
      subst i. exists regs', mem, nu.
      destruct (strlen_finish A A nu nu regs regs' mem spoff ra (Some (lconst k)) k HGm (aext_refl _ _) HL
                  ltac:(split; [apply eval_lconst|apply lin_below_lconst]) ltac:(lia) HKr Hra' Hra R10') as (G1&G2&G3&G4&G5).
      split; [exact RUN|]. split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. split; [exact G4|exact G5].
    - (* [comment removed for export] *)
      destruct (get_reg A A0r) as [pe|] eqn:Epe; [|discriminate].
      destruct (is_sp_rel pe); [|discriminate]. cbn [negb] in Happ.
      destruct (dead_lin A (lsub pe (lsym SP0))) eqn:Ed; [discriminate|].
      pose proof (bnd_sound A nu (lsub pe (lsym SP0)) HL) as Hbd.
      destruct (bnd A (lsub pe (lsym SP0))) as [[plo|] [phi|]]; try discriminate.
      destruct Hbd as [Hplo Hphi]; cbn [fst snd lo_le hi_ge] in Hplo, Hphi. rewrite eval_lsub, eval_lsym, (nu_SP0 E nu HF) in Hplo, Hphi.
      destruct (find_nul_bound A phi) as [H|] eqn:Ef; [|discriminate].
      destruct (Z.ltb_spec 0 (H + 8)); [discriminate|]. destruct (Z.ltb_spec plo (- vp_frame P)); [discriminate|].
      destruct (find_nul_bound_sound A nu regs mem phi H HGm Ef) as [z [bz (Hz1&Hz2&Rz&Uz)]].
      set (p := eval nu pe) in *. set (ov := p - e_sp0 E) in *.
      (* [comment removed for export] *)
      set (K := z - ov).
      destruct (rdn_bytes_vals mem p (Z.to_nat (K + 8)) (fun j b => j = K -> b = bz) ltac:((ltac2:(LK.k [@E1; @E3; @E4; @E5; @E7; @E8; @E9; @E11; @E12; @Hplo; @H0; @H1; @Hz1; @Hz2; @E2; @P1; @Hphi]); lia)) ltac:((ltac2:(LK.k [@E1; @E3; @E4; @E5; @E7; @E8; @E9; @E11; @E12; @Hplo; @H0; @H1; @Hz1; @Hz2; @E2; @P1; @Hphi]); lia))) as [buf (Hbuf&Lbuf&Qbuf)].
      { intros j Hj. destruct (Z.eq_dec j K) as [->|Hne].
        - exists bz. replace (p + K) with (e_sp0 E + z) by lia. split; [exact Rz|auto].
        - destruct (MC_frame_ok SEGS P E mem0 mem (p + j) HM) as [_ [bb Rb]]; [lia|]. exists bb. split; [exact Rb|intros; lia]. }
      assert (R10 : getr regs 10%bv = wordZ p).
      { apply (reg_word SEGS P E mem0 A nu regs mem 10%bv pe _ HGm); [vm_compute; lia|exact Epe|reflexivity|lia]. }
      destruct (STRLEN mem (wordZ p) buf K regs ra ltac:(rewrite Lbuf; exact Hbuf) ltac:((ltac2:(LK.k [@E1; @E3; @E4; @E5; @E7; @E8; @E9; @E11; @E12; @Hphi; @H0; @Hz1; @Hz2; @Lbuf; @E2; @P1; @Hplo; @H1]); lia)) ltac:(rewrite Lbuf; (ltac2:(LK.k [@E1; @E3; @E4; @E5; @E7; @E8; @E9; @E11; @E12; @Hphi; @H0; @Hz1; @Hz2; @Lbuf; @E2; @P1; @Hplo; @H1]); lia)) ltac:(rewrite u_wordZ, Lbuf; (ltac2:(LK.k [@E1; @E3; @E4; @E5; @E7; @E8; @E9; @E11; @E12; @Hphi; @H0; @Hz1; @Hz2; @Lbuf; @E2; @P1; @Hplo; @H1]); lia))
                  ltac:(rewrite (Qbuf (Z.to_nat K) ltac:((ltac2:(LK.k [@E1; @E3; @E4; @E5; @E7; @E8; @E9; @E11; @E12; @Hphi; @H0; @Hz1; @Hz2; @Lbuf; @E2; @P1; @Hplo; @H1]); lia)) ltac:((ltac2:(LK.k [@E1; @E3; @E4; @E5; @E7; @E8; @E9; @E11; @E12; @Hphi; @H0; @Hz1; @Hz2; @Lbuf; @E2; @P1; @Hplo; @H1]); lia))); exact Uz) (rc_clear mem HM) Hret Hra R10)
        as [regs' [i (RUN&HKr&Hra'&Hi&Zi&NZi&R10')]].
      (* [comment removed for export] *)
      pose proof (fresh_sym_box_sound A nu (Some 0, Some (H - plo)) i HL ltac:(split; cbn; lia)) as FS.
      destruct (fresh_sym A) as [s A1']. set (A2 := asetbox A1' s (Some 0, Some (H - plo))) in *.
      destruct FS as (X1&L2&V2&S2&N2).
      assert (FIN : forall A3, aext A A3 nu (vupd nu s i) -> lgamma A3 (vupd nu s i) -> (s < vs_next A3)%positive -> A1 = A3 -> v = Some (lsym s) ->
                exists regs'0 mem' nu', msteps SEGS (mkst regs (wordZ a_strlen) mem rom) (mkst regs'0 ra mem' rom) /\
                  gammaP (contract_frame C_strlen A1 spoff v) nu' regs'0 mem' /\ getr regs'0 1%bv = ra /\
                  ext (vs_next A) nu nu' /\ (vs_next A <= vs_next (contract_frame C_strlen A1 spoff v))%positive /\ frame_mod mem mem' (unit_regions P E)).
      { intros A3 X3 L3 S3 -> ->. exists regs', mem, (vupd nu s i).
        destruct (strlen_finish A A3 nu (vupd nu s i) regs regs' mem spoff ra (Some (lsym s)) i HGm X3 L3
                    ltac:(split; [rewrite eval_lsym; exact V2|apply lin_below_lsym; exact S3]) ltac:(lia) HKr Hra' Hra R10') as (G1&G2&G3&G4&G5).
        split; [exact RUN|]. split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. split; [exact G4|exact G5]. }
      destruct (lin_is_const (lsub pe (lsym SP0))) eqn:Ec.
      + injection Happ as <- <-. exact (FIN A2 X1 L2 S2 eq_refl eq_refl).
      + pose proof (aassume_sound A2 (vupd nu s i) (laddc (ladd (lsym s) (lsub pe (lsym SP0))) (- H)) L2) as AS.
        destruct (aassume A2 _) as [ok A3] eqn:Eas. cbn [fst snd] in AS.
        assert (Hle : eval (vupd nu s i) (laddc (ladd (lsym s) (lsub pe (lsym SP0))) (- H)) <= 0).
        { rewrite eval_laddc, eval_ladd, eval_lsym, V2, eval_lsub, eval_lsym.
          rewrite ((proj1 X1 : ext _ _ _) SP0) by (pose proof (proj1 (lg_below _ _ HL)); unfold LAST_FIXED, SP0 in *; lia).
          rewrite (nu_SP0 E nu HF).
          rewrite (eval_ext_below (vs_next A) nu (vupd nu s i) pe (proj1 X1)) by exact (proj2 (reg_val SEGS P E mem0 A nu regs mem 10%bv pe HGm ltac:(vm_compute; lia) Epe)).
          unfold K, ov, p in *. lia. }
        destruct (AS Hle ltac:(apply lin_below_laddc, lin_below_ladd; [apply lin_below_lsym; exact S2|apply lin_below_lsub; [eapply lin_below_mono; [exact (proj1 (proj2 X1))|exact (proj2 (reg_val SEGS P E mem0 A nu regs mem 10%bv pe HGm ltac:(vm_compute; (ltac2:(LK.k [@E3; @E7; @E8; @E9; @E11; @Lbuf; @N2; @AS; @Hle; @E4; @E5; @H2]); lia)) Epe))]|apply lin_below_lsym; pose proof (proj1 (lg_below _ _ L2)); unfold LAST_FIXED, SP0 in *; (ltac2:(LK.k [@E3; @E7; @E8; @E9; @E11; @Lbuf; @N2; @AS; @Hle; @E4; @E5; @H2]); lia)]]))
          as (Hok&L3&X3). subst ok. injection Happ as <- <-.
        apply (FIN A3); [eapply aext_trans; [exact X1|exact X3]|exact L3|destruct X3 as (_&X3b&_); clear - X3b S2; lia|reflexivity|reflexivity].
  Qed.

  Theorem strlen_dead : contract_dead SEGS P E mem0 CI C_strlen.
  Proof.
    intros A spoff nu regs mem Happ HGm. pose proof (gamma_lgamma _ _ _ _ _ _ _ _ HGm) as HL.
    pose proof HGm as (HE&HM&HF&HS&HC&HMo&HV&HR&HSl&HG&HN&HB).
    cbn [contract_apply] in Happ. unfold c_strlen, getA in Happ.
    destruct (rodata_cstr_len P (get_reg A A0r)) as [k|] eqn:Ecs.
    - destruct (rodata_cstr_sound mem _ _ HE HM Ecs) as [pe (Epe&_)]. rewrite Epe in Happ.
      destruct (in_ranges (vp_segs P) (lc pe) (k + 8)); discriminate.
    - destruct (get_reg A A0r) as [pe|] eqn:Epe; [|discriminate].
      destruct (is_sp_rel pe); [|discriminate]. cbn [negb] in Happ.
      destruct (dead_lin A (lsub pe (lsym SP0))) eqn:Ed; [exact (dead_lin_false A nu _ HL Ed)|].
      pose proof (bnd_sound A nu (lsub pe (lsym SP0)) HL) as Hbd.
      destruct (bnd A (lsub pe (lsym SP0))) as [[plo|] [phi|]]; try discriminate.
      destruct Hbd as [Hplo Hphi]; cbn [fst snd lo_le hi_ge] in Hplo, Hphi. rewrite eval_lsub, eval_lsym, (nu_SP0 E nu HF) in Hplo, Hphi.
      destruct (find_nul_bound A phi) as [H|] eqn:Ef; [|discriminate].
      destruct (Z.ltb_spec 0 (H + 8)); [discriminate|]. destruct (Z.ltb_spec plo (- vp_frame P)); [discriminate|].
      destruct (find_nul_bound_sound A nu regs mem phi H HGm Ef) as [z [bz (Hz1&Hz2&Rz&Uz)]].
      pose proof (fresh_sym_box_sound A nu (Some 0, Some (H - plo)) 0 HL ltac:(split; cbn; lia)) as FS.
      destruct (fresh_sym A) as [s A1']. set (A2 := asetbox A1' s (Some 0, Some (H - plo))) in *.
      destruct FS as (X1&L2&V2&S2&N2).
      destruct (lin_is_const (lsub pe (lsym SP0))); [discriminate|].
      pose proof (aassume_sound A2 (vupd nu s 0) (laddc (ladd (lsym s) (lsub pe (lsym SP0))) (- H)) L2) as AS.
      destruct (aassume A2 _) as [ok A3] eqn:Eas. cbn [fst snd] in AS.
      assert (Hle : eval (vupd nu s 0) (laddc (ladd (lsym s) (lsub pe (lsym SP0))) (- H)) <= 0).
      { rewrite eval_laddc, eval_ladd, eval_lsym, V2, eval_lsub, eval_lsym.
        rewrite ((proj1 X1 : ext _ _ _) SP0) by (pose proof (proj1 (lg_below _ _ HL)); unfold LAST_FIXED, SP0 in *; lia).
        rewrite (nu_SP0 E nu HF).
        rewrite (eval_ext_below (vs_next A) nu (vupd nu s 0) pe (proj1 X1)) by exact (proj2 (reg_val SEGS P E mem0 A nu regs mem 10%bv pe HGm ltac:(vm_compute; lia) Epe)).
        lia. }
      destruct (AS Hle ltac:(apply lin_below_laddc, lin_below_ladd; [apply lin_below_lsym; exact S2|apply lin_below_lsub; [eapply lin_below_mono; [exact (proj1 (proj2 X1))|exact (proj2 (reg_val SEGS P E mem0 A nu regs mem 10%bv pe HGm ltac:(vm_compute; lia) Epe))]|apply lin_below_lsym; pose proof (proj1 (lg_below _ _ L2)); unfold LAST_FIXED, SP0 in *; lia]]))
        as (Hok&_). subst ok. discriminate.
  Qed.
End CS3.
