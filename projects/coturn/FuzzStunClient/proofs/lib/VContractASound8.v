(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool String Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From Stdlib Require Import FunctionalExtensionality.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim StoreOk.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Frame.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import Hoare SeqExec StepTac RefMemcpyLib ZStores.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VLin VLinalg VWord2 VState VLogic VAbs VAbsSound VAbsSound2 VAbsSound3 VStep VStepMem VGamma VStepSound VStepMemSound VStepMemSound2 VCert VContract VContractSound VContractSound2 VContractSound3 VContractSound4 VState2 VStepMem2 VGamma2 VStepMem2SoundA VStepMem2SoundB VStepMem2SoundC VStepMem2SoundD VContractA VCert2 VContract2 VContract2Iface VContractASound1 VContractASound2 VContractASound3 VContractASound4 VContractASoundI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Stdlib.micromega.Lia.lia ::= first [ flia2 | Zify.zify; xlia zchecker ].  (* [comment removed for export] *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import LiaKeep.  (* [comment removed for export] *)
Unset Lia Cache.
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition JUNK8 : Z := 4408.

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
  (* [comment removed for export] *)
  Hypothesis SEG_IMG : forall lo hi, In (lo, hi) (vp_segs (p1 P)) -> hi <= vp_imgend P.

  #[using="Type"] Lemma HKJ8 : 0 <= JUNK8 /\ JUNK8 + 8 <= 4416.
  Proof. unfold JUNK8. lia. Qed.
  #[local] Notation str_facts8 := (str_facts SEGS JUNK8).
  #[local] Notation rng_facts8 := (rng_facts SEGS JUNK8).

  (* [comment removed for export] *)
  Variable tgt : Z.
  Variable MCELLS : (word -> option byte) -> Prop.
  Hypothesis MCELLS_OK : forall A nu regs mem, gamma2P A nu regs mem -> MCELLS mem.

  Definition RUN_spec8 : Prop := forall mem (d s n usp K : Z) (buf : list byte) regs (ra : word),
    MCELLS mem ->
    0 <= n <= 2 ^ 40 -> 0 <= d -> d + n < 2 ^ 64 ->
    str_facts8 mem usp s K buf -> 0 < s -> K + 8 <= n ->
    (d + n <= s \/ s + Z.of_nat (length buf) <= d) ->
    band_ok d n ->   (* [comment removed for export] *)
    vp_imgend P <= d ->   (* [comment removed for export] *)
    SBz + 4416 <= usp < 2 ^ 64 ->
    (usp <= d \/ d + n <= usp - JUNK8) ->
    SBz + (d + n - 1) / 8 + 8 < usp - JUNK8 ->
    (forall g, d / 8 <= g < (d + n - 1) / 8 -> mem (wordZ (SBz + g)) = Some (Z_to_bv 8 0)) ->
    (exists b1 : byte, mem (wordZ (SBz + (d + n - 1) / 8)) = Some b1 /\ (bv_unsigned b1 = 0 \/ (d + n - 1) mod 8 < bv_unsigned b1 < 8)) ->
    (forall a, (SBz + d / 8) / 8 * 8 <= a -> a <= (SBz + (d + n - 1) / 8) / 8 * 8 -> a mod 8 = 0 ->
        exists w : word, rdn SEGS mem (wordZ a) 8 = Some (word_to_le_bytes 8 w)) ->
    (forall j, 0 <= j < n -> store_ok SEGS mem (wordZ (d + j)) 1 = true) ->
    (forall a, usp - JUNK8 <= a < usp -> store_ok SEGS mem (wordZ a) 1 = true) ->
    ret_ok ra -> getr regs 1%bv = ra -> getr regs 2%bv = wordZ usp ->
    getr regs 10%bv = wordZ d -> getr regs 11%bv = wordZ s -> getr regs 12%bv = wordZ n ->
    exists regs' m' (bs : list byte),
      length bs = Z.to_nat n
      /\ msteps SEGS (mkst regs (wordZ tgt) mem rom) (mkst regs' ra m' rom)
      /\ getr regs' 10%bv = wordZ d /\ getr regs' 2%bv = wordZ usp /\ getr regs' 1%bv = ra
      /\ (forall r : reg, bv_unsigned r <> 0 -> ~ In (bv_unsigned r) CALLER_SAVED -> getr regs' r = getr regs r)
      /\ (forall x : word, (bv_unsigned x < usp - JUNK8 \/ usp <= bv_unsigned x) -> m' x = wbytes mem (wordZ d) bs x)
      /\ (forall x, mem x <> None -> m' x <> None).
  Hypothesis RUN : RUN_spec8.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="PO2 SHOFF ROM_HI FSLEN FS_SOME"] Lemma post_rgn8 A spoff nu regs mem (ra : word) de ne (n : Z) B r lo hi ov (bs : list byte) regs' m' :
    gamma2P A nu regs mem -> vs_memo A = [] ->
    get_reg (v1 A) 2 = Some (lsymc SP0 spoff) ->
    - vp_frame P1 <= spoff - 4416 -> spoff <= 0 ->
    (exists wr, In wr (vp_wstack P1) /\ fst wr <= spoff - 4416 /\ spoff <= snd wr) ->
    ret_ok ra -> getr regs 1%bv = ra ->
    get_reg (v1 A) A0r = Some de -> lin_below de (vs_next (v1 A)) = true ->
    n = eval nu ne -> 0 <= n <= 2 ^ 40 ->
    getr regs 2%bv = wordZ (e_sp0 E1 + spoff) ->
    rgn_get (vs_rgn A) B = Some r -> vr_base r = B ->
    match vr_kind r with RK_fake _ _ | RK_arg => True | _ => False end ->
    vr_lo r <= lo -> hi <= vr_hi r -> (lo < hi -> in_ranges (vr_w r) lo (hi - lo) = true) ->
    rgn_addressable A r lo hi = true -> frames_shadow_zone_ok P = true ->
    eval nu de = rbase nu r + ov -> lo <= ov -> ov + n <= hi -> 0 < n ->
    let d := rbase nu r + ov in let usp := e_sp0 E1 + spoff in
    (* [comment removed for export] *)
    length bs = Z.to_nat n ->
    msteps SEGS (mkst regs (wordZ tgt) mem rom) (mkst regs' ra m' rom) ->
    getr regs' 10%bv = wordZ d -> getr regs' 2%bv = wordZ usp -> getr regs' 1%bv = ra ->
    (forall x : reg, bv_unsigned x <> 0 -> ~ In (bv_unsigned x) CALLER_SAVED -> getr regs' x = getr regs x) ->
    (forall x : word, (bv_unsigned x < usp - JUNK8 \/ usp <= bv_unsigned x) -> m' x = wbytes mem (wordZ d) bs x) ->
    (forall x, mem x <> None -> m' x <> None) ->
    let r2' := rgn_havoc r lo hi false false in
    exists A1 v regs'' mem'' nu',
         In (A1, v) [(rgn_store_commit A r2', Some de)]
      /\ msteps SEGS (mkst regs (wordZ tgt) mem rom) (mkst regs'' ra mem'' rom)
      /\ gamma2P (contract_frame2 C_i_strncpy A1 spoff v) nu' regs'' mem''
      /\ getr regs'' 1%bv = ra
      /\ ext (vs2_next A) nu nu' /\ (vs2_next A <= vs2_next (contract_frame2 C_i_strncpy A1 spoff v))%positive
      /\ frame_mod mem mem'' (unit_regions2 P E)
      /\ flags_step P E A (contract_frame2 C_i_strncpy A1 spoff v) nu nu' mem mem''.
  Proof.
    intros HG2 MEMO Hsp K1 K2 KW Hret Hra Ede B10 En Hn R2 HGr HBr HKr RLO RHI HWr HRA HFZ Eoff Bo Bo1 Hn0 d usp
           LENs MS Q10 Q2 Q1 QK QM QG r2'.
    pose proof HG2 as (HG1 & HE & HM & HF2 & HDD & RGN & LIVE & BEL2 & GL2 & FI2 & MOK).
    pose proof (gamma2_lgamma _ _ _ _ _ _ _ _ HG2) as HL.
    pose proof (PO1 _ _ PO2) as PO. pose proof PO as (P0 & Psphi & PS & PF & PW & PR & PP & PB).
    pose proof HE as (HEV1 & HD2 & HFS & HZO & HKC). pose proof HEV1 as (E1a & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E11 & E12).
    pose proof (proj1 (proj2 HG1)) as (MF & MD & MP & MFM).
    pose proof (rgn_get_in _ _ _ HGr) as [Hr _].
    pose proof (RGN r Hr) as ROK. pose proof ROK as (RB1 & RB2 & RB3 & RDS & CELLS & PERM & NUL & KIND).
    assert (ND : is_data_shadow r = false) by (unfold is_data_shadow; destruct (vr_kind r); auto; contradiction).
    destruct (rgn_range_facts SEGS P E mem0 SHOFF ROM_HI FSLEN A nu regs mem B r lo hi ov n HG2 HGr HKr RLO RHI HRA HFZ Bo Bo1 ltac:(lia))
      as (DACC & (fa & cid & Hcid & FA1 & FA2 & FA3 & FA4 & FK) & FSnz & DRNG & _).
    cbv zeta in DACC. fold d in DACC.
    unfold env_fs in HFS. destruct (vp_fs P) as [[flen fssl]|] eqn:EFS; [|exfalso; exact (FSnz eq_refl)].
    destruct HFS as (_ & FS1 & FS2 & FS3 & FS4 & _ & _ & APsf & APdf & APds & HMsp & HMd & _ & SPHI & _).
    pose proof (FSLEN _ _ eq_refl) as FS5. clear APdf APds HMd. unfold HIGH_MEM_BEG, HIGH_MEM_END, FS_NCLASSES, FS_SSL in *.
    assert (DRANGE : fa <= d /\ d + n <= fa + fake_size cid /\ 0 <= d /\ d + n <= 2 ^ 47 - 1) by (unfold d; unfold FS_FRAMES in *; lia).
    assert (USP : 0 <= e_sp0 E1 - vp_frame P1 /\ e_sp0 E1 - vp_frame P1 <= usp - 4416 /\ usp <= e_sp0 E1 /\ e_sp0 E1 < 2 ^ 64)
      by (unfold usp, P1, E1 in *; lia).
    assert (JOK : forall a, usp - JUNK8 <= a < usp -> store_ok SEGS mem (wordZ a) 1 = true).
    { intros a Ha. unfold JUNK8 in Ha. apply (proj1 (MF a ltac:(unfold usp, P1, E1 in *; lia))). }
    (* [comment removed for export] *)
    specialize (HWr ltac:(lia)). apply in_ranges_sound in HWr as (wlo & whi & HWin & W1 & W2).
    destruct (PERM ND) as [RDp WR].
    assert (DOK : forall j, 0 <= j < n -> store_ok SEGS mem (wordZ (d + j)) 1 = true).
    { intros j Hj. destruct (WR wlo whi (ov + j) HWin ltac:(lia)) as (_ & _ & X & _). unfold d. rewrite <- Z.add_assoc. exact X. }
    (* [comment removed for export] *)
    assert (LENn : Z.of_nat (length bs) = n) by (rewrite LENs; lia).
    set (m_b := wbytes mem (wordZ d) bs) in *.
    assert (SH2 : rshape r r2') by (unfold r2', rgn_havoc; eapply rshape_trans; [apply rshape_set_cells|apply rshape_set_rnul]).
    pose proof SH2 as (SB2 & _ & SK2 & _).
    assert (INB : In (vr_base r2') (map vr_base (vs_rgn A))) by (rewrite SB2; apply in_map; exact Hr).
    set (l1 := rgn_upd (vs_rgn A) r2').
    set (l2 := match vr_kind r2' with RK_arg => havoc_other_args l1 (vr_base r2') | _ => l1 end).
    assert (SM1 : shape_map (vs_rgn A) l1).
    { unfold l1. apply rgn_upd_shape; [|exact INB]. intros x Hx EB.
      rewrite (live_ok_base_inj nu A x r LIVE Hx Hr ltac:(rewrite EB; exact SB2)). exact SH2. }
    assert (SM2 : shape_map (vs_rgn A) l2).
    { unfold l2. rewrite SK2. destruct (vr_kind r); try exact SM1. eapply shape_map_trans; [exact SM1|apply havoc_shape]. }
    pose proof LIVE as (_ & _ & _ & ND0).
    assert (MEM : forall x, In x l2 ->
              (x = r2') \/ (In x (vs_rgn A) /\ vr_base x <> vr_base r /\ ~ (vr_kind r = RK_arg /\ vr_kind x = RK_arg))
              \/ (exists y, In y (vs_rgn A) /\ vr_base y <> vr_base r /\ vr_kind r = RK_arg /\ vr_kind y = RK_arg
                               /\ x = set_rnul (set_cells y []) [])).
    { intros x Hx. unfold l2 in Hx. rewrite SK2, SB2 in Hx.
      assert (L1C : forall y, In y l1 -> y = r2' \/ (In y (vs_rgn A) /\ vr_base y <> vr_base r)).
      { intros y Hy. destruct (rgn_upd_other _ _ _ ND0 INB Hy) as [->|[Y1 Y2]]; [auto|right]. rewrite SB2 in Y2. auto. }
      destruct (vr_kind r) eqn:K0;
        try (destruct (L1C x Hx) as [->|[X1 X2]]; [left; reflexivity|right; left; repeat split; auto; intros [X _]; discriminate]).
      rewrite havoc_other_args_map in Hx. apply in_map_iff in Hx as (y & <- & Hy).
      destruct (havoc1_spec (vr_base r) y) as [[KB ->]|(KA & NBy & ->)].
      - destruct (L1C y Hy) as [->|[Y1 Y2]]; [left; reflexivity|]. right; left. split; [exact Y1|]. split; [exact Y2|].
        intros [_ X]. destruct KB as [KB|KB]; [exact (KB X)|exact (Y2 KB)].
      - destruct (L1C y Hy) as [->|[Y1 Y2]]; [exfalso; apply NBy; exact SB2|].
        right; right. exists y. repeat split; auto. }
    assert (HWIN : in_ranges (vr_w r) ov (Z.of_nat (length bs)) = true).
    { unfold in_ranges. apply existsb_exists. exists (wlo, whi). split; [exact HWin|]. cbn [fst snd]. rewrite LENn.
      apply andb_true_intro. split; apply Z.leb_le; lia. }
    destruct (rgn_write_sound SEGS P E mem0 PO2 A nu regs mem r ov bs l2 HG2 Hr ND
                ltac:(destruct (vr_kind r); auto; contradiction) ltac:(rewrite LENn; lia) HWIN SM2) as (G2 & FMb2 & FST2 & BND & SOK).
    { (* [comment removed for export] *)
      intros rx Hrx NBx. destruct (MEM rx Hrx) as [->|[(X1 & X2 & X3)|(y & Y1 & Y2 & Y3 & Y4 & ->)]].
      + exfalso. apply NBx. exact SB2.
      + exists rx. split; [exact X1|]. split; [apply rshape_refl|]. left. auto.
      + exists y. split; [exact Y1|]. split; [|right; split; reflexivity].
        eapply rshape_trans; [apply rshape_set_cells|apply rshape_set_rnul]. }
    { (* [comment removed for export] *)
      intros r' Hr' EB.
      assert (ER : r' = r2').
      { destruct (MEM r' Hr') as [->|[(X1 & X2 & X3)|(y & Y1 & Y2 & Y3 & Y4 & ->)]]; [reflexivity|exfalso; exact (X2 EB)|].
        exfalso. apply Y2. exact EB. }
      subst r'. fold d. change (wbytes mem (wordZ d) bs) with m_b.
      assert (NSH : is_shadow r = false) by (unfold is_shadow; destruct (vr_kind r); auto; contradiction).
      assert (CELLS2 : forall x, In x (vr_cells r2') -> In x (vr_cells r) /\ (fst x + fst (snd x) <= lo \/ hi <= fst x)).
      { intros [kk [ww vv]] Hin. unfold r2', rgn_havoc in Hin. cbn [vr_cells set_rnul set_cells] in Hin.
        pose proof (cm_kill_disjoint _ _ _ _ _ _ Hin). split; [eapply cm_kill_sub; exact Hin|cbn [fst snd]; lia]. }
      assert (NUL2 : forall f, In f (vr_nul r2') -> In f (vr_nul r) /\ (snd f < lo \/ hi <= fst f)).
      { intros f Hin. unfold r2', rgn_havoc in Hin. cbn [vr_nul set_rnul set_cells] in Hin.
        apply filter_In in Hin as [Hf C]. split; [exact Hf|]. apply Bool.orb_prop in C as [C|C]; [apply Z.ltb_lt in C|apply Z.leb_le in C]; lia. }
      split.
      2:{ intros kk ww e Hin. destruct BEL2 as (_ & BR & _). pose proof (proj1 (proj2 (BR r Hr))) as CB.
          destruct (CELLS2 _ Hin) as [Hold _]. exact (CB _ _ _ Hold). }
      eapply (region_ok_self SEGS P E A _ nu mem m_b r r2' HE ROK SH2 ND).
      + apply wbytes_grows.
      + unfold kind_ok in KIND. destruct (vr_kind r) as [cidf fl| | | |] eqn:K0; auto.
        destruct KIND as (_ & Hcf & _ & _ & _ & pos & Hpos & _ & Efl & _).
        pose proof (flag_addr_range (e_fs E) cidf pos Hcf Hpos) as FLR. rewrite <- Efl in FLR.
        unfold m_b. apply wblock_rdn1; rewrite ?LENn; unfold FS_FLAGS, FS_FRAMES in *; try (ltac2:(LK.k [@HBr; @Bo1; @Hn0; @LENs; @P0; @SPHI; @E4; @E5; @E11; @FA2; @DRNG; @FS5; @DRANGE; @SB2; @EB; @Bo; @FS1; @APsf; @HMsp; @FA1; @FA3; @FLR]); lia).
      + intros s0 ro G _ _. cbn [vs_rgn]. exact (shape_map_get _ _ _ _ SM2 G).
      + destruct (vr_kind r) eqn:K0; auto. cbn [vs_live]. apply (proj2 (proj1 LIVE (vr_base r))). exists r. rewrite K0. auto.
      + destruct (vr_kind r); auto; contradiction.
      + intros cc cw cv Hin. destruct (CELLS2 _ Hin) as [Hold DISJc]. cbn [fst snd] in DISJc.
        destruct (CELLS _ _ _ Hold) as (L1 & L2 & L3 & RCH). split; [lia|]. split; [lia|]. split; [lia|].
        unfold m_b. apply kept_cell; rewrite ?LENn; try (ltac2:(LK.k [@HBr; @Bo1; @Hn0; @LENs; @P0; @SPHI; @E4; @E5; @E11; @FA2; @FA4; @FS5; @DRANGE; @SB2; @EB; @RB1; @L1; @Bo; @RB2; @L3; @L2; @DISJc]); lia). exact RCH.
      + intros nlo' nhi' Hin. destruct (NUL2 _ Hin) as [Hold DISJn]. cbn [fst snd] in DISJn.
        destruct (NUL _ _ Hold) as (o0 & b0 & Y1 & Y2 & Y3 & Y4).
        exists o0, b0. split; [exact Y1|]. split; [exact Y2|]. split; [|exact Y4].
        rewrite <- Y3. unfold m_b. apply wblock_rdn1; rewrite ?LENn; unfold d; (ltac2:(LK.k [@HBr; @Bo; @Hn0; @LENs; @P0; @SPHI; @E4; @E5; @E11; @RB1; @FA2; @DRNG; @FS5; @DRANGE; @SB2; @EB; @Y1; @Y2; @Bo1; @RB2; @DISJn]); lia). }
    (* [comment removed for export] *)
    assert (QM0 : forall x : word, bv_unsigned x < usp - JUNK8 \/ usp <= bv_unsigned x -> m' x = m_b x) by exact QM.
    assert (GRW : forall x, m_b x <> None -> m' x <> None).
    { intros x Hx. destruct (Z_lt_le_dec (bv_unsigned x) d) as [X1|X1]; [|destruct (Z_lt_le_dec (bv_unsigned x) (d + n)) as [X2|X2]].
      - apply QG. intros M0. apply Hx. unfold m_b. rewrite wbytes_outside; [exact M0| |]; rewrite ?LENn, ?u_wordZ by lia; unfold in_rng; rewrite ?u_wordZ by lia; lia.
      - rewrite QM0; [exact Hx|]. unfold JUNK8, d, usp in *. unfold FS_FRAMES in *. destruct APsf as [X|X]; unfold P1, E1 in *; [left|right]; lia.
      - apply QG. intros M0. apply Hx. unfold m_b. rewrite wbytes_outside; [exact M0| |]; rewrite ?LENn, ?u_wordZ by lia; unfold in_rng; rewrite ?u_wordZ by lia; lia. }
    set (A' := mkVS2 (v1 A) l2 (vs_live A) (vs_divdef A) []) in *.
    pose proof (proj1 G2) as Gb1. cbn [v1] in Gb1.
    pose proof (gamma_junk SEGS P1 E1 (zpatch P E mem0 m_b) PO (v1 A) nu regs m_b m' spoff 4416 JUNK8 Gb1 QM0 GRW
                  ltac:(unfold JUNK8; lia) K1 K2) as Gk.
    (* [comment removed for export] *)
    set (Bst := contract_frame C_memset (killK 4416 (v1 A) spoff) spoff (Some de)).
    assert (EFR : frame_rule 4416 (v1 A) spoff (Some de) = Bst) by (apply frame_rule_killK; lia).
    destruct (killK_shape 4416 (v1 A) spoff) as (KS1 & KS2 & KS3 & KS4 & KS5 & KS6 & KS7 & KS8 & KS9).
    destruct (contract_frame_shape C_memset (killK 4416 (v1 A) spoff) spoff (Some de)) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & FR).
    assert (HLB : lgamma Bst nu).
    { apply lgamma_contract_frame; [apply lgamma_killK; exact HL|]. cbn [vbelow]. rewrite KS4. exact B10. }
    destruct (gamma_call_post SEGS P1 E1 (zpatch P E mem0 m_b) rom PO (killK 4416 (v1 A) spoff) Bst nu nu regs regs' m' m' []
                Gk (ext_refl _ _) ltac:(unfold Bst; rewrite F5; apply Pos.le_refl) HLB) as [GB _].
    { eapply (gamma_regs_contract_frame SEGS P1 E1 (zpatch P E mem0 m_b) C_memset (killK 4416 (v1 A) spoff) (killK 4416 (v1 A) spoff) spoff (Some de) nu nu regs regs');
        [right; pose proof Gk as (_&_&_&_&_&_&_&KRg&_&_&_&KBl); split; [exact KRg|destruct KBl as (_&_&KRB&_); exact KRB]
        |apply ext_refl|reflexivity|exact QK|].
      rewrite Q10, u_wordZ, Eoff by (unfold d in DRANGE; lia). unfold d. symmetry. apply zwrap_id. unfold d in DRANGE. lia. }
    { intros off' w' v' Hin. left. unfold Bst in Hin. rewrite F1 in Hin. cbn in Hin. split; [exact Hin|]. intros x _. exact I. }
    { intros g w' v' Hin. unfold Bst in Hin. rewrite F2 in Hin. split; [exact Hin|]. intros x _. exact I. }
    { intros lo' hi' Hin. left. unfold Bst in Hin. destruct (F3 _ Hin) as [Hin' _]. split; [exact Hin'|]. intros x _. exact I. }
    { apply frame_mod_refl. }
    { intros x Hx. exfalso. apply Hx. exact I. }
    assert (FMU : frame_mod m_b m' (unit_regions P1 E1)).
    { split; [|exact GRW]. intros a Ha.
      assert (NJ : ~ (usp - JUNK8 <= bv_unsigned a < usp)).
      { intros Hin. refine (proj1 (stack_R_ok SEGS P1 E1 (zpatch P E mem0 mem) PO (spoff - JUNK8) (spoff - 4416) spoff JUNK8
                                 K1 K2 ltac:(unfold JUNK8; lia) ltac:(unfold JUNK8; lia) KW HEV1 a _) Ha).
        cbn [outside]. unfold in_rng. rewrite u_wordZ by (unfold usp, JUNK8, P1, E1 in *; lia). unfold usp in Hin. intros [X _]. apply X. unfold JUNK8 in *. lia. }
      apply QM0. pose proof (bv_unsigned_in_range 64 a). lia. }
    destruct (gamma2_lift SEGS P E mem0 PO2 A' Bst nu nu regs regs' m_b m' G2 GB (ext_refl _ _)
                ltac:(unfold A', Bst; cbn [v1]; rewrite F5, KS4; apply Pos.le_refl) FMU
                ltac:(unfold globs_ok2, A', Bst; cbn [v1 with_v1]; rewrite F2, KS2; exact GL2) ltac:(right; reflexivity))
      as (G3 & FM3 & FST3).
    exists (rgn_store_commit A r2'), (Some de), regs', m', nu.
    assert (EST : contract_frame2 C_i_strncpy (rgn_store_commit A r2') spoff (Some de) = with_v1 A' Bst).
    { unfold contract_frame2, rgn_store_commit, with_v1, A', set_rgn. cbn [v1 vs_rgn vs_live vs_divdef vs_memo contract2_K].
      rewrite <- EFR, MEMO. reflexivity. }
    rewrite EST.
    split; [left; reflexivity|]. split; [exact MS|]. split; [exact G3|]. split; [exact Q1|].
    split; [apply ext_refl|]. split.
    { unfold vs2_next, A', Bst. cbn [v1 with_v1]. rewrite F5, KS4. apply Pos.le_refl. }
    split; [exact (frame_mod_trans_same _ _ _ _ FMb2 FM3)|].
    eapply flags_step_then_same; [exact FST2|]. intros y Hy. split; [unfold A', with_v1; cbn [vs_rgn]; tauto|].
    apply QM0. unfold in_flags_zone in Hy. rewrite EFS in Hy. cbv beta iota in Hy.
    unfold usp, JUNK8, FS_FLAGS, FS_FRAMES in *. rewrite u_wordZ by lia. destruct APsf as [X|X]; unfold P1, E1 in *; lia.
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="PO2 SHOFF ROM_HI FSLEN FS_SOME FRAME40 SEG_IMG"] Lemma isn_src_facts A nu regs mem spoff se nlo :
    gamma2P A nu regs mem ->
    get_reg (v1 A) 2 = Some (lsymc SP0 spoff) ->
    - vp_frame P1 <= spoff - 4416 -> spoff <= 0 ->
    get_reg (v1 A) A1r = Some se ->
    isn_src_check P A se nlo = None ->
    let usp := e_sp0 E1 + spoff in
    exists s K buf,
         getr regs 11%bv = wordZ s
      /\ str_facts8 mem usp s K buf
      /\ K + 8 <= nlo /\ 0 < s
      /\ (s + Z.of_nat (length buf) <= vp_imgend P \/ (e_sp0 E1 - vp_frame P1 <= s /\ s + Z.of_nat (length buf) <= e_sp0 E1)).
  Proof.
    intros HG2 Hsp K1 K2 Ese HC usp.
    pose proof HG2 as (HG1 & HE & HM & HF2 & HDD & RGN & LIVE & BEL2 & GL2 & FI2 & MOK).
    pose proof (gamma2_lgamma _ _ _ _ _ _ _ _ HG2) as HL.
    pose proof (PO1 _ _ PO2) as PO. pose proof PO as (P0 & Psphi & PS & PF & PW & PR & PP & PB).
    pose proof HE as (HEV1 & HD2 & HFS & HZO & HKC).
    pose proof (proj1 (proj2 HG1)) as HM1. pose proof HM1 as (MF & MD & MP & MFM). pose proof (proj1 (proj2 (proj2 HG1))) as HF1.
    destruct (env_facts SEGS P E mem0 PO2 FSLEN FS_SOME A nu regs mem HG2) as (flen & fssl & EFS & [FS1 FS2] & FS3 & FS5 & APsf & HMsp & SPHI & Pfr & E1a & SP0al & SPLO).
    unfold HIGH_MEM_BEG, HIGH_MEM_END in *.
    pose proof (reg_val SEGS P1 E1 (zpatch P E mem0 mem) (v1 A) nu regs mem 11%bv se HG1 ltac:(vm_compute; lia) Ese) as [V11 B11].
    unfold isn_src_check in HC. cbv zeta in HC.
    destruct (base_syms A se) as [|B0 [|B1 t]]; [|discriminate HC|discriminate HC].
    destruct (ptr_candidates (v1 A) se) as [cl|] eqn:HPC.
    - (* [comment removed for export] *)
      destruct (rodata_cands (p1 P) 8 _ cl) as [[klo khi]|] eqn:RC; [|discriminate HC].
      set (a := eval nu se) in *.
      destruct (rodata_cands_sound P 8 _ cl klo khi a RC (ptr_candidates_sound A nu se cl HL HPC)) as (k & Ecs & Esg & IOK & Hk).
      apply andb_prop in IOK as [IOK Ha0]. apply andb_prop in IOK as [IOK Hk8]. apply Z.leb_le in Hk8. apply Z.ltb_lt in Ha0.
      destruct (rodata_cstr_sound SEGS P1 E1 (zpatch P E mem0 mem) PO mem _ _ HEV1 HM1 Ecs) as [pe' (Epe' & Cpe & Hk0 & Hp0 & Hpk & NZ & ZK)].
      injection Epe' as <-. cbn [lc lconst] in Hp0, Hpk, NZ, ZK.
      assert (R11 : getr regs 11%bv = wordZ a).
      { apply wordZ_eq_u. rewrite V11. apply zwrap_id. unfold a, P1 in *. lia. }
      destruct (img_str_facts SEGS P E mem0 PO2 SHOFF ROM_HI FSLEN FS_SOME 4416 JUNK8 HKJ8 A nu regs mem spoff a k HG2 IOK NZ ZK Esg K1) as (buf & Lbuf & SF & NZB).
      exists a, k, buf. split; [exact R11|]. split; [exact SF|]. split; [exact Hk8|]. split; [exact Ha0|].
      left. destruct (in_ranges_sound _ _ _ Esg) as [slo [shi (Hsin & Q1 & Q2)]]. pose proof (SEG_IMG _ _ Hsin) as SI.
      rewrite Lbuf. rewrite Z2Nat.id by lia. lia.
    - (* [comment removed for export] *)
      destruct (is_sp_rel se) eqn:SPR; [|discriminate HC]. cbn [negb] in HC.
      destruct (dead_lin (v1 A) (lsub se (lsym SP0))) eqn:Ed; [discriminate HC|].
      pose proof (bnd_sound (v1 A) nu (lsub se (lsym SP0)) HL) as Hbd. unfold lo_of, hi_of in HC.
      destruct (bnd (v1 A) (lsub se (lsym SP0))) as [[plo|] [phi|]]; try discriminate HC. cbn [fst snd] in HC.
      destruct Hbd as [Hplo Hphi]; cbn [fst snd lo_le hi_ge] in Hplo, Hphi. rewrite eval_lsub, eval_lsym, (HF1 SP0 (e_sp0 E1) eq_refl) in Hplo, Hphi.
      destruct (find_nul_bound (v1 A) phi) as [H|] eqn:Ef; [|discriminate HC].
      destruct (Z.ltb_spec 0 (H + 8)); [discriminate HC|]. destruct (Z.ltb_spec plo (- vp_frame (p1 P))); [discriminate HC|].
      destruct (above_sp A plo (H + 1)) eqn:ASP; cbn [negb] in HC; [|discriminate HC].
      destruct (stack_addressable A plo (H + 1)) eqn:SA; cbn [negb] in HC; [|discriminate HC].
      destruct (stack_shadow_words_ok P plo (H + 1)) eqn:SW; cbn [negb] in HC; [|discriminate HC].
      destruct (Z.leb_spec (H - plo + 8) nlo); cbn [negb] in HC; [|discriminate HC].
      destruct (find_nul_bound_sound SEGS P1 E1 (zpatch P E mem0 mem) PO (v1 A) nu regs mem phi H HG1 Ef) as [z [bz (Hz1 & Hz2 & Rz & Uz)]].
      destruct (above_sp_sound A spoff plo (H + 1) Hsp ASP) as [BAD|ASP']; [lia|].
      set (p := eval nu se) in *. set (ov := p - e_sp0 E1) in *.
      assert (R11 : getr regs 11%bv = wordZ p).
      { apply wordZ_eq_u. rewrite V11. apply zwrap_id. unfold p, P1, E1 in *. lia. }
      destruct (stack_str_facts SEGS P E mem0 PO2 SHOFF ROM_HI FSLEN FS_SOME FRAME40 4416 JUNK8 HKJ8 A nu regs mem spoff plo H ov z bz HG2 SA SW ltac:(unfold P1 in *; lia)
                  ltac:(unfold ov, p; lia) ltac:(unfold ov, p; lia) ltac:(lia) ltac:(lia) Rz Uz K1 ASP') as (buf & Lbuf & SF & HR1 & HR2).
      exists (e_sp0 E1 + ov), (z - ov), buf.
      split; [replace (e_sp0 E1 + ov) with p by (unfold ov; lia); exact R11|]. split; [exact SF|].
      split; [unfold ov, p, P1, E1 in *; lia|]. split; [unfold ov, p, P1, E1 in *; lia|].
      right. rewrite Lbuf. rewrite Z2Nat.id by (unfold ov, p in *; lia). unfold ov, p, P1, E1 in *. lia.
  Qed.

  #[using="Type"] Lemma isn_src_not_dead A nu regs mem se nlo :
    gamma2P A nu regs mem -> isn_src_check P A se nlo = Some "dead"%string -> False.
  Proof.
    intros HG2 HC. pose proof (gamma2_lgamma _ _ _ _ _ _ _ _ HG2) as HL.
    unfold isn_src_check in HC. cbv zeta in HC.
    destruct (base_syms A se) as [|B0 [|B1 t]]; [|discriminate HC|discriminate HC].
    destruct (ptr_candidates (v1 A) se) as [cl|]; [destruct (rodata_cands _ _ _ cl); discriminate HC|].
    destruct (is_sp_rel se); [|discriminate HC]. cbn [negb] in HC.
    destruct (dead_lin (v1 A) (lsub se (lsym SP0))) eqn:Ed.
    - exact (dead_lin_false (v1 A) nu _ HL Ed).
    - destruct (lo_of (v1 A) _); [|discriminate HC]. destruct (hi_of (v1 A) _); [|discriminate HC].
      destruct (find_nul_bound (v1 A) _); [|discriminate HC].
      repeat match type of HC with (if ?c then _ else _) = _ => destruct c; try discriminate HC end.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="P1 E1 PO2 SHOFF ROM_HI FSLEN FS_SOME FRAME40 SEG_IMG MCELLS MCELLS_OK RUN"] Theorem i_strncpy_post : contract_post2 SEGS P E mem0 rom CI C_i_strncpy tgt.
  Proof.
    intros A spoff l nu regs mem ra HC HG2 MEMO Hsp HK Hret Hra.
    pose proof HG2 as (HG1 & HE & HM & HF2 & HDD & RGN & LIVE & BEL2 & GL2 & FI2 & MOK).
    pose proof (gamma2_lgamma _ _ _ _ _ _ _ _ HG2) as HL.
    pose proof (PO1 _ _ PO2) as PO. pose proof PO as (P0 & Psphi & PS & PF & PW & PR & PP & PB).
    pose proof HE as (HEV1 & HD2 & HFS & HZO & HKC). pose proof HEV1 as (E1a & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E11 & E12).
    pose proof (proj1 (proj2 HG1)) as (MF & MD & MP & MFM).
    destruct (env_facts SEGS P E mem0 PO2 FSLEN FS_SOME A nu regs mem HG2) as (flen & fssl & EFS & [FS1 FS2] & FS3 & FS5 & APsf & HMsp & SPHI & Pfr & E1a' & SP0al & SPLO).
    cbn [contract_apply2] in HC. unfold of_ca, ca_i_strncpy in HC. cbv zeta in HC.
    destruct (get_reg2 A A0r) as [de|] eqn:Ede; [|discriminate].
    destruct (get_reg2 A A1r) as [se|] eqn:Ese; [|discriminate].
    destruct (nonneg_len (v1 A) (get_reg2 A A2r) MAXLEN) as [nlo nhi| |msg] eqn:En; try discriminate.
    destruct (nonneg_len_sound (v1 A) nu _ _ _ _ HL En) as [ne (Ene & Hn0 & Hn1 & Hn2)].
    rewrite Ene in HC. cbn [lin_of] in HC. unfold MAXLEN in Hn2.
    set (n := eval nu ne) in *.
    unfold get_reg2 in Ede, Ese, Ene, En.
    assert (Hn : 0 <= n <= 2 ^ 40) by (clear -Hn0 Hn1 Hn2; lia).
    (* [comment removed for export] *)
    assert (R12 : getr regs 12%bv = wordZ n).
    { apply (reg_word SEGS P1 E1 (zpatch P E mem0 mem) (v1 A) nu regs mem 12%bv ne n HG1); [vm_compute; lia|exact Ene|reflexivity|lia]. }
    pose proof (reg_val SEGS P1 E1 (zpatch P E mem0 mem) (v1 A) nu regs mem 10%bv de HG1 ltac:(vm_compute; lia) Ede) as [V10 B10].
    assert (R2 : getr regs 2%bv = wordZ (e_sp0 E1 + spoff)).
    { apply (reg_word SEGS P1 E1 (zpatch P E mem0 mem) (v1 A) nu regs mem 2%bv (lsymc SP0 spoff) (e_sp0 E1 + spoff) HG1);
        [vm_compute; lia|exact Hsp| |].
      - rewrite eval_lsymc. rewrite (proj1 (proj2 (proj2 HG1)) SP0 (e_sp0 E1)) by reflexivity. reflexivity.
      - destruct HK as [HK'|HK']; [cbn in HK'; discriminate|]. apply in_ranges_sound in HK' as (wlo & whi & Hw & W1 & W2).
        destruct (PR _ Hw). cbn [fst snd contract2_K] in *. unfold K_i_strncpy, P1, E1 in *. lia. }
    (* [comment removed for export] *)
    assert (HKR : - vp_frame P1 <= spoff - 4416 /\ spoff <= 0 /\ exists wr, In wr (vp_wstack P1) /\ fst wr <= spoff - 4416 /\ spoff <= snd wr).
    { destruct HK as [HK'|HK']; [cbn in HK'; discriminate|]. apply in_ranges_sound in HK' as (wlo & whi & Hw & W1 & W2).
      destruct (PR _ Hw). cbn [fst snd contract2_K] in *. unfold K_i_strncpy, P1, E1 in *. split; [lia|]. split; [lia|].
      exists (wlo, whi). cbn. split; [exact Hw|lia]. }
    destruct HKR as (K1 & K2 & KW).
    set (usp := e_sp0 E1 + spoff) in *.
    assert (USP : 0 <= e_sp0 E1 - vp_frame P1 /\ e_sp0 E1 - vp_frame P1 <= usp - 4416 /\ usp <= e_sp0 E1 /\ e_sp0 E1 < 2 ^ 64)
      by (unfold usp, P1, E1 in *; lia).
    assert (JOK : forall a, usp - JUNK8 <= a < usp -> store_ok SEGS mem (wordZ a) 1 = true).
    { intros a Ha. unfold JUNK8 in Ha. apply (proj1 (MF a ltac:(unfold usp, P1, E1 in *; lia))). }
    (* [comment removed for export] *)
    destruct (range_check P A de ne true) as [r lo hi|rr| |m1] eqn:RCd; [|discriminate HC|discriminate HC|discriminate HC].
    destruct (range_check_rgn_inv P A de ne r lo hi RCd) as (B & HBS & C1 & C2 & C3 & HGr & HKr & LET).
    cbv zeta in LET. destruct LET as (LO & HI & RLO & RHI & HWr & HRA & HFZ).
    pose proof (rgn_get_in _ _ _ HGr) as [Hr HBr].
    set (off := laddc (lsub de (lsym B)) (- vr_disp r)) in *.
    assert (Eoff : eval nu de = rbase nu r + eval nu off) by (unfold off; rewrite <- HBr, eval_off; lia).
    pose proof (bnd_sound (v1 A) nu off HL) as Bo. pose proof (bnd_sound (v1 A) nu (ladd off ne) HL) as Bo1.
    unfold lo_of in LO. unfold hi_of in HI.
    destruct (bnd (v1 A) off) as [olo ohi] eqn:Ebo. cbn [fst] in LO. subst olo.
    destruct (bnd (v1 A) (ladd off ne)) as [olo1 ohi1] eqn:Ebo1. cbn [snd] in HI. subst ohi1.
    destruct Bo as [Bo _]. destruct Bo1 as [_ Bo1]. cbn [fst snd lo_le hi_ge] in Bo, Bo1. rewrite eval_ladd in Bo1. fold n in Bo1.
    set (ov := eval nu off) in *. set (d := rbase nu r + ov) in *.
    (* [comment removed for export] *)
    destruct (isn_src_check P A se nlo) as [msg|] eqn:SRC.
    { destruct (String.eqb msg "dead"); discriminate HC. }
    cbn [ca_ok1] in HC. injection HC as <-.
    destruct (isn_src_facts A nu regs mem spoff se nlo HG2 Hsp K1 K2 Ese SRC) as (s & K & buf & R11 & SF & HK8 & Hs0 & SDJ).
    pose proof SF as (SF1 & SF2 & SF3 & SF4 & SF5 & SF6 & SF7 & SF8 & SF9 & SF10 & SF11 & SF12 & SF13).
    assert (Hn8 : 8 <= n) by (clear -HK8 Hn1 SF5; lia).
    (* [comment removed for export] *)
    destruct (rgn_range_facts SEGS P E mem0 SHOFF ROM_HI FSLEN A nu regs mem B r lo hi ov n HG2 HGr HKr RLO RHI HRA HFZ Bo Bo1 ltac:(lia))
      as (_ & (fa & cid & Hcid & FA1 & FA2 & FA3 & FA4 & FK) & FSnz & DRNG & _).
    unfold env_fs in HFS. rewrite EFS in HFS.
    destruct HFS as (_ & _ & _ & _ & FS4 & _ & _ & _ & APdf & APds & _ & HMd & _ & _ & FDEP). destruct FDEP as [_ FSIMG].
    unfold HIGH_MEM_BEG, HIGH_MEM_END, FS_NCLASSES, FS_SSL in *.
    assert (DRANGE : fa <= d /\ d + n <= fa + fake_size cid /\ 0 <= d /\ d + n <= 2 ^ 47 - 1 /\ e_fs E + FS_FRAMES <= d /\ d + n < e_fs E + flen).
    { pose proof (FSLEN _ _ EFS) as FL. unfold d. clear - FA1 FA2 FA3 FA4 Bo Bo1 FS1 FS2 FL Hn. unfold FS_FRAMES, FS_NCLASSES, FS_SSL in *. lia. }
    destruct (rgn_rng_facts SEGS P E mem0 PO2 SHOFF ROM_HI FSLEN FS_SOME 4416 JUNK8 HKJ8 A nu regs mem spoff B r lo hi ov (n - 1)
                HG2 HGr HKr RLO RHI HRA HFZ Bo ltac:(lia) ltac:(lia) K1 K2) as (bufd & RF & DRB).
    cbv zeta in RF. fold usp in RF. fold d in RF.
    pose proof RF as (_ & _ & _ & _ & _ & _ & _ & RF8 & RF9 & RF10 & RF11 & RF12).
    replace (d + (n - 1) + 1) with (d + n) in RF8 by lia. replace (d + (n - 1)) with (d + n - 1) in RF9, RF10, RF11, RF12 by lia.
    (* [comment removed for export] *)
    pose proof (RGN r Hr) as (RB1 & RB2 & RB3 & RDS & CELLS & PERM & NUL & KIND).
    assert (ND : is_data_shadow r = false) by (unfold is_data_shadow; destruct (vr_kind r); auto; contradiction).
    specialize (HWr ltac:((ltac2:(LK.k [@E4; @E5; @E11; @Hn1; @HBr; @Bo; @Bo1; @HK8; @SF5; @Hn8]); lia))). apply in_ranges_sound in HWr as (wlo & whi & HWin & W1 & W2).
    destruct (PERM ND) as [RDp WR].
    assert (DOK : forall j, 0 <= j < n -> store_ok SEGS mem (wordZ (d + j)) 1 = true).
    { intros j Hj. destruct (WR wlo whi (ov + j) HWin ltac:((ltac2:(LK.k [@E4; @E5; @E11; @W1; @W2; @HBr; @Bo; @Bo1; @Hj]); lia))) as (_ & _ & X & _). unfold d. rewrite <- Z.add_assoc. exact X. }
    assert (R10 : getr regs 10%bv = wordZ d).
    { apply wordZ_eq_u. rewrite V10, Eoff. fold ov. unfold d. apply zwrap_id. clear -DRANGE Bo Bo1 Hn. lia. }
    (* [comment removed for export] *)
    assert (DISJ : d + n <= s \/ s + Z.of_nat (length buf) <= d).
    { destruct SDJ as [LOWs|[STK1 STK2]]; [right; clear -LOWs DRANGE FSIMG; unfold FS_FRAMES in *; lia|].
      unfold FS_FRAMES in *. destruct APsf as [X|X]; unfold P1, E1 in *; [left|right]; clear -X STK1 STK2 DRANGE Pfr; lia. }
    (* [comment removed for export] *)
    destruct (RUN mem d s n usp K buf regs ra (MCELLS_OK _ _ _ _ HG2) Hn ltac:((ltac2:(LK.k [@E4; @E5; @E11; @HBr; @DRANGE; @Hn1; @HK8; @FS2; @FSIMG; @HMsp; @USP]); lia)) ltac:((ltac2:(LK.k [@E4; @E5; @E11; @HBr; @DRANGE; @Hn1; @HK8; @FS2; @FSIMG; @HMsp; @USP]); lia)) SF Hs0 ltac:((ltac2:(LK.k [@E4; @E5; @E11; @HBr; @DRANGE; @Hn1; @HK8; @FS2; @FSIMG; @HMsp; @USP]); lia)) DISJ
                ltac:(apply (band_ok_sub (e_fs E) flen _ _ (proj2 FS1)); clear -DRANGE FS2; unfold HIGH_MEM_END, FS_FRAMES in *; (ltac2:(LK.k [@E4; @E5; @E11; @HBr; @DRANGE; @Hn1; @HK8; @FS2; @FSIMG; @HMsp; @USP]); lia))
                ltac:(clear -DRANGE FSIMG; unfold FS_FRAMES in *; (ltac2:(LK.k [@E4; @E5; @E11; @HBr; @DRANGE; @Hn1; @HK8; @FS2; @FSIMG; @HMsp; @USP]); lia))
                ltac:(clear -USP HMsp; unfold SBz, usp, P1, E1 in *; (ltac2:(LK.k [@E4; @E5; @E11; @HBr; @DRANGE; @Hn1; @HK8; @FS2; @FSIMG; @HMsp; @USP]); lia)))
      as (regs' & m' & bs & LENs & MS & Q10 & Q2 & Q1 & QK & QM & QG).
    { exact RF8. }
    { exact RF9. }
    { exact RF10. }
    { exact RF11. }
    { exact RF12. }
    { exact DOK. }
    { exact JOK. }
    { exact Hret. } { exact Hra. } { exact R2. } { exact R10. } { exact R11. } { exact R12. }
    (* [comment removed for export] *)
    assert (HWr' : lo < hi -> in_ranges (vr_w r) lo (hi - lo) = true).
    { intros _. unfold in_ranges. apply existsb_exists. exists (wlo, whi). split; [exact HWin|]. cbn [fst snd].
      apply andb_true_intro. split; apply Z.leb_le; lia. }
    exact (post_rgn8 A spoff nu regs mem ra de ne n B r lo hi ov bs regs' m' HG2 MEMO Hsp K1 K2 KW Hret Hra Ede B10 eq_refl Hn R2
             HGr HBr HKr RLO RHI HWr' HRA HFZ Eoff Bo Bo1 ltac:(lia) LENs MS Q10 Q2 Q1 QK QM QG).
  Qed.

  #[using="PO2"] Theorem i_strncpy_dead : contract_dead2 SEGS P E mem0 CI C_i_strncpy.
  Proof.
    intros A spoff nu regs mem HC HG2.
    pose proof (gamma2_lgamma _ _ _ _ _ _ _ _ HG2) as HL.
    cbn [contract_apply2] in HC. unfold of_ca, ca_i_strncpy in HC. cbv zeta in HC.
    destruct (get_reg2 A A0r) as [de|] eqn:Ede; [|discriminate].
    destruct (get_reg2 A A1r) as [se|] eqn:Ese; [|discriminate].
    destruct (nonneg_len (v1 A) (get_reg2 A A2r) MAXLEN) as [nlo nhi| |msg] eqn:En; try discriminate;
      [|exact (nonneg_len_dead (v1 A) nu _ _ HL En)].
    destruct (nonneg_len_sound (v1 A) nu _ _ _ _ HL En) as [ne (Ene & Hn0 & Hn1 & Hn2)]. rewrite Ene in HC. cbn [lin_of] in HC.
    destruct (range_check P A de ne true) as [r lo hi|rr| |m1] eqn:RCd; try discriminate HC.
    - destruct (isn_src_check P A se nlo) as [msg|] eqn:SRC; [|discriminate HC].
      destruct (String.eqb_spec msg "dead"); [|discriminate HC]. subst msg. exact (isn_src_not_dead A nu regs mem se nlo HG2 SRC).
    - exact (range_check_not_dead SEGS P E mem0 PO2 A nu regs mem de ne true HG2 ltac:(lia) RCd).
  Qed.
End S.
