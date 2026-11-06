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
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import LiaKeep.  (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition JUNK7 : Z := 4552.

Lemma in_ranges_within l lo k x n :
  in_ranges l lo k = true -> lo <= x -> x + n <= lo + k -> in_ranges l x n = true.
Proof.
  intros H H1 H2. unfold in_ranges in *. apply existsb_exists in H as ([a b] & Hin & C). cbn [fst snd] in C.
  apply andb_prop in C as [C1 C2]. apply Z.leb_le in C1. apply Z.leb_le in C2.
  apply existsb_exists. exists (a, b). split; [exact Hin|]. cbn [fst snd]. apply andb_true_intro. split; apply Z.leb_le; lia.
Qed.

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
  Lemma HKJ7 : 0 <= JUNK7 /\ JUNK7 + 8 <= 4560.
  Proof. unfold JUNK7. lia. Qed.

  (* [comment removed for export] *)
  Definition opnd_facts (mem : word -> option byte) (usp x n : Z) (buf : list byte) : Prop :=
       rdn SEGS mem (wordZ x) (length buf) = Some buf /\ length buf = Z.to_nat n
    /\ 0 <= x /\ x + n < 2 ^ 64
    /\ (0 < n ->
           (forall g, x / 8 <= g < (x + n - 1) / 8 -> mem (wordZ (SBz + g)) = Some (Z_to_bv 8 0))
        /\ (exists b1 : byte, mem (wordZ (SBz + (x + n - 1) / 8)) = Some b1 /\ (bv_unsigned b1 = 0 \/ (x + n - 1) mod 8 < bv_unsigned b1 < 8))
        /\ (exists w : word, rdn SEGS mem (wordZ ((SBz + x / 8) / 8 * 8)) 8 = Some (word_to_le_bytes 8 w))
        /\ (exists w : word, rdn SEGS mem (wordZ ((SBz + (x + n - 1) / 8) / 8 * 8)) 8 = Some (word_to_le_bytes 8 w))
        /\ SBz + (x + n - 1) / 8 + 8 < usp - JUNK7
        /\ (x + n <= LOW_MEM_END \/ HIGH_MEM_BEG <= x /\ x + n <= HIGH_MEM_END - 1)
        /\ (usp <= x \/ x + n <= usp - JUNK7)).

  Variable tgt : Z.
  Variable MCELLS : (word -> option byte) -> Prop.
  Hypothesis MCELLS_OK : forall A nu regs mem, gamma2P A nu regs mem -> MCELLS mem.

  Definition RUN_spec7 : Prop := forall mem (a b n usp : Z) (bufa bufb : list byte) regs (ra : word),
    MCELLS mem -> 0 <= n <= 2 ^ 40 -> opnd_facts mem usp a n bufa -> opnd_facts mem usp b n bufb ->
    SBz + 4568 <= usp < 2 ^ 64 ->
    (forall x, usp - JUNK7 <= x < usp -> store_ok SEGS mem (wordZ x) 1 = true) ->
    ret_ok ra -> getr regs 1%bv = ra -> getr regs 2%bv = wordZ usp ->
    getr regs 10%bv = wordZ a -> getr regs 11%bv = wordZ b -> getr regs 12%bv = wordZ n ->
    exists regs' (dlt : Z) m',
      msteps SEGS (mkst regs (wordZ tgt) mem rom) (mkst regs' ra m' rom)
      /\ -255 <= dlt <= 255 /\ bv_unsigned (getr regs' 10%bv) = zwrap 64 dlt
      /\ getr regs' 2%bv = wordZ usp /\ getr regs' 1%bv = ra
      /\ (forall r : reg, bv_unsigned r <> 0 -> ~ In (bv_unsigned r) CALLER_SAVED -> getr regs' r = getr regs r)
      /\ (forall x : word, (bv_unsigned x < usp - JUNK7 \/ usp <= bv_unsigned x) -> m' x = mem x)
      /\ (forall x, mem x <> None -> m' x <> None).
  Hypothesis RUN : RUN_spec7.

  (* [comment removed for export] *)
  Lemma opnd_of_rng mem usp x n buf : 0 < n -> rng_facts SEGS JUNK7 mem usp x (n - 1) buf -> opnd_facts mem usp x n buf.
  Proof.
    intros Hn (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12). unfold opnd_facts.
    replace (x + (n - 1) + 1) with (x + n) in * by lia. replace (x + (n - 1)) with (x + n - 1) in * by lia.
    split; [exact R1|]. split; [lia|]. split; [lia|]. split; [lia|]. intros _.
    split; [exact R10|]. split; [exact R11|].
    pose proof (div8_facts (SBz + x / 8)). pose proof (div8_facts (SBz + (x + n - 1) / 8)).
    pose proof (word_floor_mono SBz x (x + n - 1) ltac:(lia)).
    split; [apply R12; [lia|lia|apply Z_mod_mult]|].
    split; [apply R12; [lia|lia|apply Z_mod_mult]|].
    split; [exact R9|]. split; [exact R7|exact R8].
  Qed.

  (* [comment removed for export] *)
  Lemma opnd_empty mem usp x : 0 <= x < 2 ^ 64 -> opnd_facts mem usp x 0 [].
  Proof. intros Hx. unfold opnd_facts. cbn [length rdn]. repeat split; try lia; try reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma readable_range_img_inv A de ne lo hi :
    readable_range P1 A de ne = RR_img lo hi ->
    lo_of A de = Some lo /\ hi_of A (ladd de ne) = Some hi /\ in_ranges (vp_segs P1) lo (hi - lo) = true.
  Proof.
    unfold readable_range.
    destruct (is_sp_rel de); [intros X; exfalso; pose proof (stack_range_shape (p1 P) A de ne false) as SH; unfold P1 in X; rewrite X in SH; exact SH|].
    destruct (is_data_rel de).
    - destruct (dead_lin A _); [discriminate|]. destruct (lo_of A _); [|discriminate]. destruct (_ <? 0); [discriminate|].
      destruct (hi_of A _); [|discriminate]. destruct (0 <? _); discriminate.
    - destruct (negb _); [discriminate|]. destruct (lo_of A de) as [l|]; [|discriminate]. destruct (hi_of A (ladd de ne)) as [h|]; [|discriminate].
      destruct (in_ranges (vp_segs P1) l (h - l)) eqn:IR; [|discriminate]. intros X. injection X as <- <-. auto.
  Qed.

  Lemma range_check_ld_img_inv A de ne lo hi :
    range_check P A de ne false = RA_v1 (RR_img lo hi) -> readable_range P1 (v1 A) de ne = RR_img lo hi.
  Proof.
    unfold range_check. destruct (base_syms A de) as [|B [|B2 t]]; try discriminate.
    - unfold P1. destruct (readable_range (p1 P) (v1 A) de ne) as [off lo' hi'|doff|ilo ihi| |m]; try discriminate;
        [repeat match goal with |- (if ?c then _ else _) = _ -> _ => destruct c; try discriminate end|].
      intros X. injection X as <- <-. reflexivity.
    - destruct (negb (lcoef de B =? 1) || negb ((lcoef de SP0 =? 0) && (lcoef de DATA =? 0))); [discriminate|].
      destruct (rgn_get (vs_rgn A) B) as [r|]; [|discriminate].
      destruct (vr_kind r); try discriminate;
        (destruct (dead_lin (v1 A) _ || dead_lin (v1 A) _); [discriminate|]);
        destruct (lo_of (v1 A) _); try discriminate; destruct (hi_of (v1 A) _); try discriminate;
        repeat match goal with |- (if ?c then _ else _) = _ -> _ => destruct c; try discriminate end.
  Qed.

  (* [comment removed for export] *)
  #[using="PO2 SHOFF ROM_HI FSLEN FS_SOME FRAME40"] Lemma opnd_sound A nu regs mem spoff pe ne n nhi (w : word) :
    gamma2P A nu regs mem -> opnd_check P A pe ne nhi = OC_ok ->
    lin_below pe (vs_next (v1 A)) = true -> bv_unsigned w = zwrap 64 (eval nu pe) ->
    n = eval nu ne -> 0 <= n <= nhi ->
    - vp_frame P1 <= spoff - 4560 -> spoff <= 0 ->
    get_reg (v1 A) 2 = Some (lsymc SP0 spoff) ->
    let usp := e_sp0 E1 + spoff in
    exists x buf, w = wordZ x /\ opnd_facts mem usp x n buf.
  Proof.
    intros HG2 HOC Bpe Vw En Hn K1 K2 Hsp usp.
    pose proof (bv_unsigned_in_range 64 w) as Wr. change (bv_modulus 64) with (2 ^ 64) in Wr.
    destruct (Z.eq_dec n 0) as [N0|N0].
    { (* [comment removed for export] *)
      exists (bv_unsigned w), []. split; [apply wordZ_eq_u; reflexivity|]. rewrite N0. apply opnd_empty. lia. }
    pose proof HG2 as (HG1 & HE & HM & HF2 & HDD & RGN & LIVE & BEL2 & GL2 & FI2 & MOK).
    pose proof (gamma2_lgamma _ _ _ _ _ _ _ _ HG2) as HL.
    pose proof (PO1 _ _ PO2) as PO. pose proof PO as (P0 & Psphi & PS & PF & PW & PR & PP & PB).
    pose proof HE as (HEV1 & HD2 & HFS & HZO & HKC). pose proof (proj1 (proj2 HG1)) as (MF & MD & MP & MFM). pose proof (proj1 (proj2 (proj2 HG1))) as HF1.
    destruct (env_facts SEGS P E mem0 PO2 FSLEN FS_SOME A nu regs mem HG2) as (flen & fssl & EFS & [FS1 FS2] & FS3 & FS5 & APsf & HMsp & SPHI & Pfr & _ & SP0al & SPLO).
    unfold HIGH_MEM_BEG, HIGH_MEM_END in *.
    unfold opnd_check in HOC.
    destruct (range_check P A pe ne false) as [r lo hi|rr| |m1] eqn:RC; [| |discriminate HOC|discriminate HOC].
    - (* [comment removed for export] *)
      destruct (range_check_ld_rgn_inv P A pe ne r lo hi RC) as (B & HBS & C1 & C2 & C3 & HGr & HKr & LET).
      cbv zeta in LET. destruct LET as (LO & HI & RLO & RHI & HRA & HFZ).
      pose proof (rgn_get_in _ _ _ HGr) as [Hr HBr].
      set (off := laddc (lsub pe (lsym B)) (- vr_disp r)) in *.
      assert (Eoff : eval nu pe = rbase nu r + eval nu off) by (unfold off; rewrite <- HBr, eval_off; lia).
      pose proof (bnd_sound (v1 A) nu off HL) as Bo. pose proof (bnd_sound (v1 A) nu (ladd off ne) HL) as Bo1.
      unfold lo_of in LO. unfold hi_of in HI.
      destruct (bnd (v1 A) off) as [olo ohi] eqn:Ebo. cbn [fst] in LO. subst olo.
      destruct (bnd (v1 A) (ladd off ne)) as [olo1 ohi1] eqn:Ebo1. cbn [snd] in HI. subst ohi1.
      destruct Bo as [Bo _]. destruct Bo1 as [_ Bo1]. cbn [fst snd lo_le hi_ge] in Bo, Bo1. rewrite eval_ladd in Bo1. rewrite <- En in Bo1.
      set (ov := eval nu off) in *.
      destruct (rgn_rng_facts SEGS P E mem0 PO2 SHOFF ROM_HI FSLEN FS_SOME 4560 JUNK7 HKJ7 A nu regs mem spoff B r lo hi ov (n - 1) HG2 HGr HKr RLO RHI HRA HFZ
                  Bo ltac:(lia) ltac:(lia) K1 K2) as (buf & FA & HRB). pose proof FA as (_ & _ & HR2 & HR1 & _).   (* [comment removed for export] *)
      exists (rbase nu r + ov), buf. split; [apply wordZ_eq_u; rewrite Vw, Eoff; fold ov; apply zwrap_id; lia|].
      apply opnd_of_rng; [lia|exact FA].
    - destruct rr as [so slo shi|doff|ilo ihi| |msg]; try discriminate HOC.
      + (* [comment removed for export] *)
        destruct (range_check_ld_v1_inv P A pe ne _ RC) as [(so' & slo' & shi' & EQ & RRs & Hab & Hsa & Hsw)|[(doff & EQ & _)|(ilo & ihi & EQ)]]; try discriminate EQ.
        injection EQ as <- <- <-.
        pose proof (readable_range_stack P1 (v1 A) pe ne so slo shi RRs) as SRs.
        destruct (stack_range_sound P1 E1 (v1 A) nu pe ne false so slo shi HL HF1 SRs) as (_ & Es & Ss1 & Ss2 & Ss3 & Ss4 & _).
        rewrite <- En in Ss2. set (sov := eval nu so) in *.
        destruct (above_sp_sound A spoff slo shi Hsp Hab) as [BAD|ASP]; [lia|].
        destruct (stack_rng_facts SEGS P E mem0 PO2 SHOFF ROM_HI FSLEN FS_SOME FRAME40 4560 JUNK7 HKJ7 A nu regs mem spoff slo shi sov (n - 1) HG2 Hsa Hsw
                    Ss3 Ss1 ltac:(lia) Ss4 ltac:(lia) K1 ASP) as (buf & FA & HR1 & HR2). unfold HIGH_MEM_BEG, HIGH_MEM_END in HR1, HR2.
        exists (e_sp0 E1 + sov), buf. split; [apply wordZ_eq_u; rewrite Vw, Es; apply zwrap_id; unfold sov, P1, E1 in *; lia|].
        apply opnd_of_rng; [lia|exact FA].
      + (* [comment removed for export] *)
        destruct (Z.leb_spec 8 (vp_datal P)) as [DATAL|]; [|discriminate HOC].
        destruct (range_check_ld_v1_inv P A pe ne _ RC) as [(so' & slo' & shi' & EQ & _)|[(doff' & EQ & RRd)|(ilo & ihi & EQ)]]; try discriminate EQ.
        injection EQ as <-.
        destruct (readable_range_data_inv P E (v1 A) nu pe ne doff HL HF1 RRd) as [D1 D2]. rewrite <- En in D2.
        set (ov := eval nu pe - e_data E1) in *.
        destruct (data_range_facts SEGS P E mem0 SHOFF ROM_HI FSLEN DATAL A nu regs mem ov n HG2 FS_SOME D1 D2 ltac:(lia)) as (DACC & HMd & D8 & APds & DRD).
        pose proof HEV1 as (E1a & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E11 & E12).
        assert (W : w = wordZ (e_data E1 + ov)).
        { apply wordZ_eq_u. rewrite Vw. unfold ov. replace (e_data E1 + (eval nu pe - e_data E1)) with (eval nu pe) by lia.
          apply zwrap_id. unfold ov, P1, E1 in *. lia. }
        destruct (rdn_bytes SEGS mem (e_data E1 + ov) (Z.to_nat n) ltac:(unfold ov, P1, E1 in *; lia) ltac:(rewrite Z2Nat.id by lia; unfold ov, P1, E1 in *; lia))
          as (buf & Hbuf & Lbuf).
        { intros i Hi. rewrite Z2Nat.id in Hi by lia. replace (e_data E1 + ov + i) with (e_data E1 + (ov + i)) by lia. apply DRD. unfold ov, P1, E1 in *. lia. }
        exists (e_data E1 + ov), buf. split; [exact W|].
        destruct (DACC ltac:(lia)) as (ZG & LG & W1 & W2). destruct (HMd ltac:(lia)) as [HM1 HM2]. unfold HIGH_MEM_BEG, HIGH_MEM_END in HM1, HM2.
        unfold opnd_facts. rewrite Lbuf. split; [exact Hbuf|]. split; [reflexivity|]. split; [unfold ov, P1, E1 in *; lia|]. split; [unfold ov, P1, E1 in *; lia|].
        intros _. split; [exact ZG|]. split; [exact LG|]. split; [exact W1|]. split; [exact W2|].
        split; [unfold SBz, usp, JUNK7; apply (arith_shdK_low (e_sp0 E1) (vp_frame P1) spoff (e_data E1 + ov + n - 1) 4560 JUNK7); unfold JUNK7, ov, P1, E1 in *; (ltac2:(LK.k [@Hn; @N0; @HMsp; @E5; @E11; @Lbuf; @K1; @K2; @FS1; @SPHI; @SP0al; @D1; @D2; @APds; @E4; @HM1; @HM2]); lia)|].
        split; [apply band_ok_str, (band_ok_in (e_data E1) (e_size E1) _ _ (proj1 HM1)); unfold HIGH_MEM_END; unfold ov, P1, E1 in *; lia|].
        unfold usp, JUNK7. destruct APds as [X|X]; unfold P1, E1 in *; [right|left]; lia.
      + (* [comment removed for export] *)
        pose proof (range_check_ld_img_inv A pe ne ilo ihi RC) as RRi.
        destruct (readable_range_img_inv (v1 A) pe ne ilo ihi RRi) as (LOi & HIi & IR).
        pose proof (bnd_sound (v1 A) nu pe HL) as Bp. pose proof (bnd_sound (v1 A) nu (ladd pe ne) HL) as Bp1.
        unfold lo_of in LOi. unfold hi_of in HIi.
        destruct (bnd (v1 A) pe) as [plo phi] eqn:Ebp. cbn [fst] in LOi. subst plo.
        destruct (bnd (v1 A) (ladd pe ne)) as [plo1 phi1] eqn:Ebp1. cbn [snd] in HIi. subst phi1.
        destruct Bp as [Bp _]. destruct Bp1 as [_ Bp1]. cbn [fst snd lo_le hi_ge] in Bp, Bp1. rewrite eval_ladd, <- En in Bp1.
        destruct (Z.eqb_spec nhi 0) as [NH0|NH0]; [lia|].
        destruct (lin_is_const pe) eqn:Cpe; cbn [andb] in HOC; [|discriminate HOC].
        destruct (img_addressable P (lc pe) (lc pe + nhi)) eqn:IA; [|discriminate HOC].
        pose proof IA as IA'. unfold img_addressable in IA'.
        apply andb_prop in IA' as [IA' _]. apply andb_prop in IA' as [IA' _]. apply andb_prop in IA' as [IA' I3].
        apply andb_prop in IA' as [I1 I2]. apply Z.leb_le in I1. apply Z.ltb_lt in I2. apply Z.leb_le in I3. unfold LOW_MEM_END in I3.
        set (x := lc pe) in *. rewrite (eval_is_const _ _ Cpe) in Vw, Bp, Bp1. fold x in Vw, Bp, Bp1.
        assert (W : w = wordZ x) by (apply wordZ_eq_u; rewrite Vw; apply zwrap_id; lia).
        destruct (img_rng_facts SEGS P E mem0 PO2 SHOFF ROM_HI FSLEN FS_SOME 4560 JUNK7 HKJ7 A nu regs mem spoff x (n - 1) nhi HG2
                    ltac:(exact IA) ltac:(lia) ltac:(lia)
                    ltac:(replace (n - 1 + 1) with n by lia; apply (in_ranges_within _ ilo (ihi - ilo)); [exact IR|lia|lia]) K1) as (buf & FA).
        exists x, buf. split; [exact W|]. apply opnd_of_rng; [lia|exact FA].
  Qed.

  Theorem i_bcmp_post : contract_post2 SEGS P E mem0 rom CI C_i_bcmp tgt.
  Proof.
    intros A spoff l nu regs mem ra HC HG2 MEMO Hsp HK Hret Hra.
    pose proof HG2 as (HG1 & HE & HM & HF2 & HDD & RGN & LIVE & BEL2 & GL2 & FI2 & MOK).
    pose proof (gamma2_lgamma _ _ _ _ _ _ _ _ HG2) as HL.
    pose proof (PO1 _ _ PO2) as PO. pose proof PO as (P0 & Psphi & PS & PF & PW & PR & PP & PB).
    pose proof HE as (HEV1 & HD2 & HFS & HZO & HKC). pose proof HEV1 as (E1a & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E11 & E12).
    pose proof (proj1 (proj2 HG1)) as (MF & MD & MP & MFM). pose proof (proj1 (proj2 (proj2 HG1))) as HF1.
    destruct (env_facts SEGS P E mem0 PO2 FSLEN FS_SOME A nu regs mem HG2) as (flen & fssl & EFS & [FS1 FS2] & FS3 & FS5 & APsf & HMsp & SPHI & Pfr & _ & SP0al & SPLO).
    unfold HIGH_MEM_BEG, HIGH_MEM_END in *.
    assert (HKR : - vp_frame P1 <= spoff - 4560 /\ spoff <= 0 /\ exists wr, In wr (vp_wstack P1) /\ fst wr <= spoff - 4560 /\ spoff <= snd wr).
    { destruct HK as [HK'|HK']; [cbn in HK'; discriminate|]. apply in_ranges_sound in HK' as (wlo & whi & Hw & W1 & W2).
      destruct (PR _ Hw). cbn [fst snd contract2_K] in *. unfold K_i_bcmp, P1, E1 in *. split; [lia|]. split; [lia|].
      exists (wlo, whi). cbn. split; [exact Hw|lia]. }
    destruct HKR as (K1 & K2 & KW).
    set (usp := e_sp0 E1 + spoff) in *.
    assert (USP : SBz + 4568 <= usp < 2 ^ 64) by (unfold usp, SBz, P1, E1 in *; lia).
    assert (JOK : forall x, usp - JUNK7 <= x < usp -> store_ok SEGS mem (wordZ x) 1 = true).
    { intros x Hx. unfold JUNK7 in Hx. apply (proj1 (MF x ltac:(unfold usp, P1, E1 in *; lia))). }
    assert (R2 : getr regs 2%bv = wordZ usp).
    { apply (reg_word SEGS P1 E1 (zpatch P E mem0 mem) (v1 A) nu regs mem 2%bv (lsymc SP0 spoff) usp HG1);
        [vm_compute; lia|exact Hsp| |unfold usp, P1, E1 in *; lia].
      rewrite eval_lsymc. rewrite (HF1 SP0 (e_sp0 E1)) by reflexivity. reflexivity. }
    cbn [contract_apply2] in HC. unfold ca_i_bcmp in HC. cbv zeta in HC. unfold get_reg2 in HC.
    destruct (nonneg_len (v1 A) (get_reg (v1 A) A2r) MAXLEN) as [nlo nhi| |msg] eqn:En; try discriminate HC.
    destruct (nonneg_len_sound (v1 A) nu _ _ _ _ HL En) as [ne (Ene & Hn0 & Hn1 & Hn2)]. rewrite Ene in HC. cbn [lin_of] in HC. unfold MAXLEN in Hn2.
    destruct (get_reg (v1 A) A0r) as [ae|] eqn:Eae; [|discriminate HC]. destruct (get_reg (v1 A) A1r) as [be|] eqn:Ebe; [|discriminate HC].
    set (n := eval nu ne) in *.
    pose proof (reg_val SEGS P1 E1 (zpatch P E mem0 mem) (v1 A) nu regs mem 10%bv ae HG1 ltac:(vm_compute; lia) Eae) as [V10 B10].
    pose proof (reg_val SEGS P1 E1 (zpatch P E mem0 mem) (v1 A) nu regs mem 11%bv be HG1 ltac:(vm_compute; lia) Ebe) as [V11 B11].
    assert (R12 : getr regs 12%bv = wordZ n).
    { apply (reg_word SEGS P1 E1 (zpatch P E mem0 mem) (v1 A) nu regs mem 12%bv ne n HG1); [vm_compute; lia|exact Ene|reflexivity|lia]. }
    destruct (opnd_check P A ae ne nhi) eqn:OA; cbn [of_ca] in HC; [|discriminate HC|destruct (opnd_check P A be ne nhi); cbn [of_ca] in HC; discriminate HC].
    destruct (opnd_check P A be ne nhi) eqn:OB; cbn [of_ca] in HC; [|discriminate HC|discriminate HC].
    destruct (opnd_sound A nu regs mem spoff ae ne n nhi (getr regs 10%bv) HG2 OA B10 V10 eq_refl ltac:(lia) K1 K2 Hsp) as (a & bufa & R10 & FA).
    destruct (opnd_sound A nu regs mem spoff be ne n nhi (getr regs 11%bv) HG2 OB B11 V11 eq_refl ltac:(lia) K1 K2 Hsp) as (b & bufb & R11 & FB).
    destruct (RUN mem a b n usp bufa bufb regs ra (MCELLS_OK _ _ _ _ HG2) ltac:(lia) FA FB USP JOK Hret Hra R2 R10 R11 R12)
      as (regs' & dlt & m' & MS & Hd & Q10 & Q2 & Q1 & QK & QM & QG).
    pose proof (afresh_sound (v1 A) nu (Some (-255), Some 255) dlt HL ltac:(split; cbn; lia)) as AFS.
    destruct (afresh (v1 A) (Some (-255), Some 255)) as [v B1] eqn:EAF.
    cbn [of_ca ca_ok1] in HC. injection HC as <-.
    destruct AFS as (nu' & XB & LB & Hv). destruct v as [e|]; [|destruct Hv]. destruct Hv as [Ve Be].
    destruct (post_val SEGS P E mem0 rom PO2 FSLEN FS_SOME 4560 JUNK7 HKJ7 C_i_bcmp A spoff nu nu' regs regs' mem m' B1 e dlt eq_refl
                HG2 MEMO K1 K2 KW XB LB Ve Be Q10 QK QM QG) as (G & X1 & X2 & X3 & X4).
    exists (with_v1 A B1), (Some e), regs', m', nu'.
    split; [left; reflexivity|]. split; [exact MS|]. split; [exact G|]. split; [exact Q1|]. auto.
  Qed.

  Theorem i_bcmp_dead : contract_dead2 SEGS P E mem0 CI C_i_bcmp.
  Proof.
    intros A spoff nu regs mem HC HG2. pose proof (gamma2_lgamma _ _ _ _ _ _ _ _ HG2) as HL.
    cbn [contract_apply2] in HC. unfold ca_i_bcmp in HC. cbv zeta in HC. unfold get_reg2 in HC.
    destruct (nonneg_len (v1 A) (get_reg (v1 A) A2r) MAXLEN) as [nlo nhi| |msg] eqn:En; try discriminate HC;
      [|exact (nonneg_len_dead (v1 A) nu _ _ HL En)].
    destruct (nonneg_len_sound (v1 A) nu _ _ _ _ HL En) as [ne (Ene & Hn0 & Hn1 & Hn2)]. rewrite Ene in HC. cbn [lin_of] in HC.
    destruct (get_reg (v1 A) A0r) as [ae|] eqn:Eae; [|discriminate HC]. destruct (get_reg (v1 A) A1r) as [be|] eqn:Ebe; [|discriminate HC].
    assert (OCD : forall pe, opnd_check P A pe ne nhi = OC_dead -> False).
    { intros pe H0. unfold opnd_check in H0.
      destruct (range_check P A pe ne false) as [r lo hi|rr| |m1] eqn:RC; [discriminate H0| |exact (range_check_not_dead SEGS P E mem0 PO2 A nu regs mem pe ne false HG2 ltac:(lia) RC)|discriminate H0].
      destruct rr; try discriminate H0; repeat match type of H0 with (if ?c then _ else _) = _ => destruct c; try discriminate H0 end. }
    destruct (opnd_check P A ae ne nhi) eqn:OA; cbn [of_ca] in HC; [|exact (OCD ae OA)|].
    - destruct (opnd_check P A be ne nhi) eqn:OB; cbn [of_ca] in HC; [|exact (OCD be OB)|discriminate HC]. destruct (afresh _ _); discriminate HC.
    - destruct (opnd_check P A be ne nhi) eqn:OB; cbn [of_ca] in HC; [discriminate HC|exact (OCD be OB)|discriminate HC].
  Qed.
End S.
