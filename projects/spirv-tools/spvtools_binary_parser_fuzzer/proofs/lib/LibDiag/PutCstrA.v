(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Classical_Prop.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac StoreOk MemSplit Hoare ShapeAlg SRealizes MmapSim
  RefMemcpyLib LibIface LibEff LibMaskBits ZStores SymExec3 SymExec3Sound SymRun3 LibTail S1Layout.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContLib StrLib ContStmts S1Facts LiveStats.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HLib.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsGrammar PrsNeeds.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Import RunsLib.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag Require Import
  DiagTac DiagVia DiagViaS1 DiagPins DiagS1 DRep DFacts DsRoom DiagStmts SbOverflow Xsputn.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import RunRandom.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Module Ly := S1Layout.
Abbreviation SEGS := Plain.M.loaded_segments.

Definition PC_PAD : Z := 0x68988.
Definition PC_RET_PAD : Z := 0x68938.
Definition PC_RET_XS : Z := 0x68adc.
Definition PC_RETPC : Z := 0x68984.

Definition FUEL : nat := 400%nat.

Lemma ro_cstr_ro_addr : forall p n i, PrsGrammar.ro_cstr SEGS Ly.L p n -> 0 <= i < n -> ro_addr Ly.L (p + i).
Proof.
  intros p n i (Hp & Hn & Hhi & RC) Hi.
  destruct (Classical_Prop.classic (ro_addr Ly.L (p + i))) as [Y|N]; [exact Y | exfalso].
  destruct (RC (fun _ => None) ltac:(intros w _; reflexivity)) as (B0 & _ & _).
  destruct (B0 i Hi) as (c & Hc & F0).

  set (Mb := fun w : word => if Z.eqb (bv_unsigned w) (p + i) then Some (Z_to_bv 8 0) else None).
  assert (RCb : ro_clear Ly.L Mb).
  { intros w Hw. subst Mb. cbn beta. destruct (Z.eqb_spec (bv_unsigned w) (p + i)) as [Ew|]; [|reflexivity].
    exfalso. apply N. rewrite <- Ew. exact Hw. }
  destruct (RC Mb RCb) as (B1 & _ & _). destruct (B1 i Hi) as (c' & Hc' & F1).
  unfold fld in F0, F1. rewrite SeqExec.N_to_le_bytes_1_small, u64_of_Z in F0, F1 by lia.
  cbn [rdn] in F0, F1.
  replace (Mb (Z_to_bv 64 (p + i))) with (Some (Z_to_bv 8 0)) in F1 by (subst Mb; cbn beta; rewrite u64_of_Z, Z.eqb_refl by lia; reflexivity).
  destruct (seg_rom SEGS (Z_to_bv 64 (p + i))) as [b|] eqn:Eb; [|discriminate F0].
  assert (E1 : bv_unsigned (Z_to_bv 8 0) = bv_unsigned (Z_to_bv 8 c')) by congruence.
  rewrite !StrLib.u8_of_Z in E1 by lia. lia.
Qed.

Lemma rdn_of_flds : forall M p (k : nat),
  0 <= p -> p + Z.of_nat k < 2 ^ 64 ->
  (forall i, 0 <= i < Z.of_nat k -> exists c, 0 <= c < 256 /\ fld SEGS M (p + i) 1 c) ->
  exists bs, rdn SEGS M (Z_to_bv 64 p) k = Some bs.
Proof.
  intros M p k. revert p. induction k as [|k IH]; intros p Hp Hk HF; [exists []; reflexivity|].
  destruct (HF 0 ltac:(lia)) as (c & Hc & F0). destruct (IH (p + 1) ltac:(lia) ltac:(lia)) as (bs & Hbs).
  { intros i Hi. replace (p + 1 + i) with (p + (1 + i)) by lia. apply HF. lia. }
  exists (word_to_le_bytes 1 (Z_to_bv 64 c) ++ bs). change (S k) with (1 + k)%nat.
  apply (LibTail.rdn_app_Z SEGS M p 1 k); [| cbn [Z.of_nat Pos.of_succ_nat]; exact Hbs | lia | lia].
  unfold fld in F0. rewrite Z.add_0_r in F0. exact F0.
Qed.

Section PutCstr.
Context {AC : AllocCeiling}.
Context {RRND : RunRandom}.
  Variable MI : MallocIface SEGS Ly.L.
  Variable ST : StaticsIface SEGS Ly.L.
  Hypothesis DN : diag_needs MI ST.

  #[local] Notation cfg fx R pc M model := (mkCfg (@mkst fx R (Z_to_bv 64 pc) M (seg_rom SEGS)) model).

  Let MSP : 0 <= MALLOC_STACK MI. Proof. pose proof (dn_mstack MI ST DN). lia. Qed.

  Definition kn_entry (fill mlo mhi : Z) : list kentry :=
    [KWr (SA (EVar 2) (-192)) (ELit 192);
     KWr (SA (EVar 10) 0) (ELit 392);
     KRange (EVar 2) (2 ^ 40) (2 ^ 47); KRange (EVar 10) (2 ^ 40) (2 ^ 47 - 392);
     KRange (EVar 11) 0 (2 ^ 47); KRange (EVar 12) mlo mhi;
     KDisj (SA (EVar 10) 0) (ELit 392) (SA (EVar 2) (-192)) (ELit 192);
     KImg 0xe6000 0xee000;
     KWord (SA (EVar 10) 0) (N.to_nat 8) (ELit VT_OS);
     KWord (SA (EVar 10) 8) (N.to_nat 8) (ELit VT_SB);
     KWord (SA (EVar 10) 120) (N.to_nat 4) (EVar 32);
     KWord (SA (EVar 10) 136) (N.to_nat 8) (ELit 0);
     KWord (SA (EVar 10) 144) (N.to_nat 4) (ELit 0);
     KWord (SA (EVar 10) 152) (N.to_nat 8) (EAlu ALU_ADD (EVar 10) (ELit 8));
     KWord (SA (EVar 10) 160) (N.to_nat 8) (ELit LOC_IMP);
     KWord (SA (EVar 10) 248) (N.to_nat 8) (ELit 0);
     KWord (SA (EVar 10) 256) (N.to_nat 4) (ELit fill);
     KWord (SA (ELit 0) A_CTYPE_ID) (N.to_nat 8) (ELit (2 ^ 64 - 1));
     KWord (SA (ELit 0) (A_CTYPE_ID + 8)) (N.to_nat 4) (ELit 3);
     KWord (SA (ELit 0) (LOC_IMP + 16)) (N.to_nat 8) (ELit FACETS_BEG);
     KWord (SA (ELit 0) (LOC_IMP + 24)) (N.to_nat 8) (ELit FACETS_END);
     KWord (SA (ELit 0) (FACETS_BEG + 16)) (N.to_nat 8) (ELit A_CTYPE_OBJ);
     KWord (SA (ELit 0) A_CTYPE_OBJ) (N.to_nat 8) (ELit VT_CTYPE)].

  Section Call.
    Context {fx : FPState}.
    Variables (A : AS MI) (s : LibIface.SX ST) (R : bvmap 5 word) (M : mem) (model : Model).
    Variables (sp ret S ds err len p m : Z) (B : list (Z * Z)) (K : TSet).
    Variables (m0 : sbuf) (pp0 hm0 fl fill : Z).
    Hypothesis CB : callB MI ST A s R M model sp ret S.
    Hypothesis HS : 192 + XS_STK MI <= S.
    Hypothesis ROC : ro_clear Ly.L M.
    Hypothesis Ha0 : getr R 10%bv = Z_to_bv 64 ds.
    Hypothesis Ha1 : getr R 11%bv = Z_to_bv 64 p.
    Hypothesis Ha2 : getr R 12%bv = Z_to_bv 64 m.
    Hypothesis DI0 : ds_inv A M ds err len B m0 pp0 hm0 fl fill.
    Hypothesis ABOVE : above_sp MI A sp ds 392.

    Hypothesis Hp : 0 <= p /\ p + m <= 2 ^ 47 /\ 0 <= m.
    Hypothesis SRCOK : forall a, p <= a < p + m ->
        ~ zwin ds (ds + 392) a /\
        ((sp <= a /\ alloc_ceiling <= a) \/ ro_addr Ly.L a
         \/ (exists q k, In (q, k) (live MI A) /\ q <= a < q + k /\ ~ In (q, k) (str_blocks m0))).
    Hypothesis RDM : exists bs, rdn SEGS M (Z_to_bv 64 p) (Z.to_nat m) = Some bs.
    Hypothesis BUD : len + m <= DS_MAXLEN.
    Hypothesis ROOM : ds_room SEGS Ly.L MI A.
    Hypothesis POST : forall A' R' M' model' B' (J : Z -> Prop),
        retB MI ST A' s R R' M' model model' -> getr R' 10%bv = Z_to_bv 64 ds ->
        ds_rep MI A' M' ds err (len + m) B' -> blk_xfer B B' (live MI A) (live MI A') -> junk_ok MI A J ->
        eff MI A A' M M' (sp - S, sp) (fun a => ds_foot ds B a \/ ds_foot ds B' a \/ J a) ->
        srealizes SEGS (cfg fx R' ret M' model') K.

    Let w0 : Z := pp0 - str_data (ds + 72) m0.

    Definition SV1 : list word := [Z_to_bv 64 ret; getr R 8%bv; getr R 9%bv; getr R 18%bv; getr R 19%bv; getr R 20%bv; getr R 21%bv; getr R 22%bv].
    Definition SV2 : list word := [Z_to_bv 64 PC_RET_PAD; Z_to_bv 64 ds; Z_to_bv 64 p; Z_to_bv 64 (ds + 112); Z_to_bv 64 (p + m);
                                   Z_to_bv 64 p; Z_to_bv 64 (ds + 8); Z_to_bv 64 32; getr R 23%bv].

    Definition W1 (a : Z) : Prop := zwin (sp - 192) sp a \/ zwin (ds + 256) (ds + 260) a.

    Record pmid (R1 : bvmap 5 word) (M1 : mem) : Prop := PMID {
      pm_st   : stores_in W1 M M1;
      pm_sl1  : slots SEGS M1 sp SV1;
      pm_sl2  : slots SEGS M1 (sp - 96) SV2;
      pm_os   : fld SEGS M1 (sp - 80) 8 ds;
      pm_fill : fld SEGS M1 (ds + 256) 4 32;
      pm_r1 : getr R1 1%bv = Z_to_bv 64 PC_RET_XS;  pm_r2 : getr R1 2%bv = Z_to_bv 64 (sp - 192);
      pm_r3 : getr R1 3%bv = Z_to_bv 64 (ly_gp Ly.L); pm_r4 : getr R1 4%bv = Z_to_bv 64 (ly_tp Ly.L);
      pm_r8 : getr R1 8%bv = Z_to_bv 64 (ds + 8);   pm_r9 : getr R1 9%bv = Z_to_bv 64 (ds + 112);
      pm_r10 : getr R1 10%bv = Z_to_bv 64 (ds + 8); pm_r11 : getr R1 11%bv = Z_to_bv 64 p; pm_r12 : getr R1 12%bv = Z_to_bv 64 m;
      pm_r18 : getr R1 18%bv = Z_to_bv 64 p; pm_r19 : getr R1 19%bv = Z_to_bv 64 m;
      pm_cs : forall r, In r [24; 25; 26; 27]%bv -> getr R1 r = getr R r
    }.

    Lemma ctx : alloc_ceiling + S <= sp /\ sp < 2 ^ 47 /\ sp mod 16 = 0 /\ 0 <= ret < 2 ^ 64 /\
                sp <= ds /\ ds + 392 <= 2 ^ 47 /\ (forall i, 0 <= i < 392 -> ~ owned MI A (ds + i)) /\
                0 <= p /\ 0 <= m /\ p + m <= 2 ^ 47 /\ 0 <= w0 <= len /\ 0 <= len.
    Proof using AC MI ST A s R M model sp ret S ds err len p m B m0 pp0 hm0 fl fill CB DI0 ABOVE Hp.
      destruct CB as [AI MS ROC' SXI SXH [Hra Hret Hretr Hsp Hsp16 Hsphi Hgp Htp] Hceil HROOM Hwin Hown_sx Herr_sx].
      destruct ABOVE as (H1 & H2 & H3). pose proof Hp as (Hp0 & Hpn & Hn0).
      pose proof (di_pl _ _ _ _ _ _ _ _ _ _ _ _ DI0). pose proof (di_len0 _ _ _ _ _ _ _ _ _ _ _ _ DI0).
      pose proof (si_pp _ _ _ _ _ _ _ (di_sb _ _ _ _ _ _ _ _ _ _ _ _ DI0)) as H4. replace (ds + 8 + 64) with (ds + 72) in H4 by lia.
      subst w0. repeat split; try assumption; try lia.
    Qed.

    #[local] Ltac t10 T1 T0 H := apply T1; [lia | cbn; lia |]; apply T0; [cbn; lia | lia | lia | cbn; lia | exact H].

    Lemma xs_stage : forall R1 M1, 0 < m -> pmid R1 M1 -> srealizes SEGS (cfg fx R1 A_XSPUTN M1 model) K.
    Proof using AC RRND MI ST DN fx A s R M model sp ret S ds err len p m B K m0 pp0 hm0 fl fill CB HS ROC DI0 ABOVE Hp SRCOK RDM BUD ROOM POST.
      intros R1 M1 Hmpos PM.
      pose proof ctx as (Hceil & Hsphi & Hsp16 & Hretr & Hds_sp & Hds_hi & Hds_own & Hp0 & Hn0 & Hpn & Hw0 & Hlen0).
      assert (HXS0 : XS_STK MI = 208 + (16 + MALLOC_STACK MI)) by (unfold XS_STK, OVF_STK, NEW_STACK; lia). pose proof (dn_mstack MI ST DN) as HMS0.
      pose proof CB as CB0. destruct CB0 as [AI MS ROC' SXI SXH [Hra Hret _ Hsp _ _ Hgp Htp] _ HROOM Hwin Hown_sx Herr_sx].
      cbn [ly_gp ly_tp Ly.L] in Hgp, Htp. pose proof ac_bounds_lit as Hcv.
      pose proof DI0 as DI. destruct DI as [Gpos Gal Ghi Gdef Gvt SB GB Gmx Gpow Glen0 Gpl Gasz Gdj II G320 G336 G360 G368 Gerr].
      destruct PM as [ST1 SL1 SL2 FOS FFILL X1 X2 X3 X4 X8 X9 X10 X11 X12 X18 X19 XCS]. cbn [ly_gp ly_tp Ly.L] in X3, X4.
      assert (HXS : XS_STK MI = 208 + (16 + MALLOC_STACK MI)) by (unfold XS_STK, OVF_STK, NEW_STACK; lia).
      pose proof (dn_mstack MI ST DN) as HMS.

      assert (W1NO : forall a, W1 a -> ~ owned MI A a /\ ~ in_ranges (ly_img Ly.L) a /\ ~ sx_region ST a).
      { intros a [Ha|Ha]; unfold zwin in Ha.
        - pose proof (Hwin a ltac:(unfold zwin; lia)) as [H1 H2]. split; [exact H1|]. split; [apply hi_offimg; lia | exact H2].
        - split; [replace a with (ds + (a - ds)) by lia; apply Hds_own; lia|].
          split; [apply hi_offimg; lia|]. intros Hs. apply (hi_offimg (AC:=AC) a ltac:(lia)). apply ly_rw_img. apply (sx_region_rw ST). exact Hs. }
      assert (AI1 : ainv MI A M1 model) by (eapply stores_in_ainv; [exact AI | exact ST1 | intros a Ha; exact (proj1 (W1NO a Ha))]).
      assert (SX1 : sx_inv ST s M1).
      { eapply stores_in_sx; [exact SXI | exact ST1 |]. intros a Ha. pose proof (W1NO a Ha) as (_ & Hni & Hns).
        split; [exact Hns | intros Hr; apply Hni; apply ly_relro_img; exact Hr]. }
      assert (ROC1 : ro_clear Ly.L M1).
      { eapply ro_clear_frame; [exact ROC | eapply stores_in_frame_eq; [exact ST1 | intros a Ha; exact Ha] |].
        intros a (Himg & _) Hw. exact (proj1 (proj2 (W1NO a Hw)) Himg). }
      assert (SB1 : sb_inv A M1 (ds + 8) m0 pp0 hm0).
      { eapply (sb_inv_frame MI A A M M1); [exact SB | lia | lia | | intros blk Hb; destruct (si_str _ _ _ _ _ _ _ SB) as (cs & SR & _); exact (str_blocks_live MI _ _ _ _ _ SR blk Hb)].
        eapply stores_in_agree; [exact ST1|]. intros a Ha. unfold sb_fp, W1, zwin in *.
        destruct Ha as [Ha|Ha]; [lia|]. destruct m0 as [|d0 a0]; [destruct Ha|].
        destruct (si_str _ _ _ _ _ _ _ SB) as (cs & SR & _). destruct SR as (_ & _ & _ & _ & (Hd0 & _ & _ & _ & _ & HIn & _) & _).
        pose proof (live_range _ _ MI A M model d0 a0 AI HIn). lia. }

      destruct RDM as (bs & RD0).
      assert (RD : rdn SEGS M1 (Z_to_bv 64 p) (Z.to_nat m) = Some bs).
      { rewrite <- RD0. apply rdn_ext; [rewrite u64_of_Z by lia; lia|]. intros x Hx. rewrite u64_of_Z in Hx by lia.
        apply (proj1 ST1). intros Hw. unfold W1, zwin in Hw. destruct (SRCOK (bv_unsigned x) ltac:(lia)) as [Hnds Hsrc3].
        destruct Hw as [Hw|Hw]; [|apply Hnds; unfold zwin; lia].
        destruct Hsrc3 as [Hst|[Hro|(q & kq & HIn0 & Hqk & Hnb)]]; [lia | |].
        - apply (hi_offimg (AC:=AC) (bv_unsigned x)); [lia | exact (proj1 Hro)].
        - pose proof (live_range _ _ MI A M model q kq AI HIn0). lia. }

      pose proof (ai_live_nodup MI A M model AI) as ND0.
      assert (BL0 : forall b, In b (str_blocks m0) -> In b (live MI A)).
      { intros b Hb. destruct (si_str _ _ _ _ _ _ _ SB) as (cs & SR & _). exact (str_blocks_live MI _ _ _ _ _ SR b Hb). }
      apply (xsputn MI ST MSP (dn_new MI ST DN) (ds_ri SEGS Ly.L MI A m0)
               (ri_grow SEGS Ly.L MI (dn_classes MI ST DN) (dn_round_big MI ST DN) A m0 ND0 BL0 Gpow ROOM)
               (ri_step SEGS Ly.L MI A m0 BL0 Gpow)
               (ri_mono SEGS Ly.L MI A m0)
               A s R1 M1 model (sp - 192) PC_RET_XS (ds + 8) p m m0 pp0 hm0 bs K).
      -   constructor.
        + exact AI1. + exact MS. + exact (img_ro_clear_of' ST s M1 ROC1 SX1). + exact SX1. + exact SXH.
        + constructor; [exact X1 | apply bv_eq; vm_compute; reflexivity | unfold PC_RET_XS; lia | exact X2 | mlia | lia | exact X3 | exact X4].
        + lia.
        + unfold stack_room. eapply stores_in_store_ok; [exact ST1|].
          replace (Z_to_bv 64 (sp - 192 - XS_STK MI)) with (Z_to_bv 64 (sp - S + (S - 192 - XS_STK MI))) by (f_equal; lia).
          apply (mdef_store_ok_off SEGS M (sp - S) S); try lia.
          eapply store_ok_mdef_offimg; [exact HROOM | lia | lia | lia | intros x Hx; apply ly_noseg; lia].
        + intros a Ha. split; [apply (hi_unowned MI A M1 model); [exact AI1 | unfold zwin in Ha; lia] | apply (proj2 (Hwin a ltac:(unfold zwin in *; lia)))].
        + exact Hown_sx. + exact Herr_sx.
      - exact ROC1.
      - exact SB1.
      - lia. - lia.
      - eapply stores_in_mdef; [exact ST1|]. eapply mdef_sub; [exact Gdef | lia | lia].
      - exact Hmpos.
      -   intros a Ha. destruct (SRCOK a Ha) as [Hnds Hsrc3]. split; [intros Hz; apply Hnds; unfold zwin in *; lia|].
        destruct Hsrc3 as [Hst|[Hro|Hblk]]; [left; lia | right; left; exact Hro | right; right; exact Hblk].
      - lia.
      - exact RD.
      - replace (ds + 8 + 64) with (ds + 72) by lia. apply ri_init; [exact ND0 | exact BL0 | exact Gpow | subst w0; lia].
      - replace (ds + 8 + 64) with (ds + 72) by lia. subst w0. lia.
      -
        intros A' R' M' model' m' pp' hm' J RB Hr10 SB' HDsb' Hw' RI' XF JK EFF.
        pose proof RB as RB0. destruct RB as [AI' MS' FS' FDS' SX' KEPT].
        replace (ds + 8 + 64) with (ds + 72) in Hw' by lia. fold w0 in Hw'.

        assert (Hm'blk : forall d a, m' = SLong d a -> In (d, a) (live MI A') /\ 0 < d /\ d + a <= alloc_ceiling).
        { intros d a ->. destruct (si_str _ _ _ _ _ _ _ SB') as (cs' & SR' & _). destruct SR' as (_ & _ & _ & _ & (Hd & _ & _ & _ & _ & HIn & _) & _).
          pose proof (live_range _ _ MI A' M' model' d a AI' HIn). repeat split; [exact HIn | lia | lia]. }
        assert (NF : forall a, alloc_ceiling <= a -> ~ (ds + 8 <= a < ds + 112) ->
                     ~ (zwin (ds + 8) (ds + 8 + 104) a \/ sbuf_fp m0 a \/ sbuf_fp m' a \/ J a)).
        { intros a Ha Hnsb [Hz|[Hb|[Hb|Hj]]]; [unfold zwin in Hz; lia | | | destruct (JK a Hj) as (Hlo & _); lia].
          - destruct m0 as [|d0 a0]; [destruct Hb|]. cbn in Hb. unfold zwin in Hb.
            destruct (si_str _ _ _ _ _ _ _ SB) as (cs & SR & _). destruct SR as (_ & _ & _ & _ & (Hd0 & _ & _ & _ & _ & HIn & _) & _).
            pose proof (live_range _ _ MI A M model d0 a0 AI HIn). lia.
          - destruct m' as [|d1 a1]; [destruct Hb|]. cbn in Hb. unfold zwin in Hb. destruct (Hm'blk d1 a1 eq_refl) as (_ & _ & Hc). lia. }
        assert (HD1 : mdef M1 (sp - 192) 192).
        { eapply stores_in_mdef; [exact ST1|]. intros i Hi. replace (sp - 192 + i) with (sp - S + (S - 192 + i)) by lia.
          eapply (store_ok_mdef_offimg SEGS M (sp - S) S); [exact HROOM | lia | lia | lia | intros x Hx; apply ly_noseg; lia | lia]. }
        assert (AGS : agree_on (zwin (sp - 192) sp) M1 M').
        { eapply (agree_hi_via_eff MI A A' M1 M'); [exact EFF | exact AI1 | exact AI' | lia | lia | replace (sp - (sp - 192)) with 192 by lia; exact HD1 | intros a Ha; apply NF; lia | cbn; lia]. }
        assert (HDd1 : mdef M1 ds 392) by (eapply stores_in_mdef; [exact ST1 | exact Gdef]).
        assert (AGD0 : agree_on (zwin ds (ds + 8)) M1 M').
        { eapply (agree_hi_via_eff MI A A' M1 M'); [exact EFF | exact AI1 | exact AI' | lia | lia | eapply mdef_sub; [exact HDd1 | lia | lia] | intros a Ha; apply NF; lia | cbn; lia]. }
        assert (AGD1 : agree_on (zwin (ds + 112) (ds + 392)) M1 M').
        { eapply (agree_hi_via_eff MI A A' M1 M'); [exact EFF | exact AI1 | exact AI' | lia | lia | eapply mdef_sub; [exact HDd1 | lia | lia] | intros a Ha; apply NF; lia | cbn; lia]. }
        assert (SL1' : slots SEGS M' sp SV1).
        { eapply slots_agree; [exact SL1 | cbn; lia | lia | cbn [length SV1 Z.of_nat Pos.of_succ_nat Pos.succ Pos.mul Z.mul]].
          eapply agree_on_weaken; [exact AGS|]. intros a Ha. unfold zwin in *. lia. }
        assert (SL2' : slots SEGS M' (sp - 96) SV2).
        { eapply slots_agree; [exact SL2 | cbn; lia | lia | cbn [length SV2 Z.of_nat Pos.of_succ_nat Pos.succ Pos.mul Z.mul]].
          eapply agree_on_weaken; [exact AGS|]. intros a Ha. unfold zwin in *. lia. }
        assert (FOS' : fld SEGS M' (sp - 80) 8 ds).
        { eapply fld_agree; [lia | cbn; lia | exact FOS | eapply agree_on_weaken; [exact AGS|]; intros a Ha; unfold zwin in *; cbn in Ha; lia]. }
        assert (T1 : forall a (k : nat) v, ds + 112 <= a -> a + Z.of_nat k <= ds + 392 -> fld SEGS M1 a k v -> fld SEGS M' a k v).
        { intros a k v H1 H2 HF. eapply fld_agree; [lia | lia | exact HF | eapply agree_on_weaken; [exact AGD1|]; intros x Hx; unfold zwin in *; lia]. }
        assert (T0 : forall a (k : nat) v, (a + Z.of_nat k <= ds + 256 \/ ds + 260 <= a) -> (sp <= a) -> 0 <= a -> a + Z.of_nat k < 2 ^ 64 ->
                     fld SEGS M a k v -> fld SEGS M1 a k v).
        { intros a k v H1 H2 H3 H4 HF. eapply fld_agree; [lia | lia | exact HF |]. eapply stores_in_agree; [exact ST1|]. intros x Hx. unfold W1, zwin in *. lia. }
        pose proof II as II1. destruct II as [Ivt Ifl Iflr Iprec Iwid Ist Iexc Irdbuf Iloc Izero Itie Ifill Ifillr].
        assert (Jfl : fld SEGS M' (ds + 112 + 8) 4 fl) by (t10 T1 T0 Ifl).
        assert (Jst : fld SEGS M' (ds + 112 + 32) 4 0) by (t10 T1 T0 Ist).
        assert (Jrdbuf : fld SEGS M' (ds + 112 + 40) 8 (ds + 8)) by (t10 T1 T0 Irdbuf).
        assert (Jvt : fld SEGS M' ds 8 VT_OS).
        { eapply fld_agree; [lia | cbn; lia | | eapply agree_on_weaken; [exact AGD0|]; intros x Hx; unfold zwin in *; cbn in Hx; lia].
          apply T0; [cbn; lia | lia | lia | cbn; lia | exact Gvt]. }
        assert (HDM' : mdef M' ds 392).
        { intros i Hi. destruct (Z.lt_ge_cases i 8) as [Hi8|Hi8]; [|destruct (Z.lt_ge_cases i 112) as [Hi112|Hi112]].
          - revert i Hi Hi8. enough (G : mdef M' ds 8) by (intros; apply G; lia).
            eapply (mdef_via_eff MI A A' M1 M'); [exact EFF | left; lia | lia | lia | intros j Hj; apply Hds_own; lia | intros j Hj; apply NF; lia | eapply mdef_sub; [exact HDd1 | lia | lia]].
          - replace (ds + i) with (ds + 8 + (i - 8)) by lia. apply HDsb'. lia.
          - replace (ds + i) with (ds + 112 + (i - 112)) by lia. revert i Hi Hi8 Hi112.
            enough (G : mdef M' (ds + 112) 280) by (intros; apply G; lia).
            eapply (mdef_via_eff MI A A' M1 M'); [exact EFF | left; lia | lia | lia | intros j Hj; replace (ds + 112 + j) with (ds + (112 + j)) by lia; apply Hds_own; lia | intros j Hj; apply NF; lia | eapply mdef_sub; [exact HDd1 | lia | lia]]. }

        set (E3 := Eseed R' [Z_to_bv 64 (sp - 192); Z_to_bv 64 ds; Z_to_bv 64 p; getr R 23%bv; Z_to_bv 64 ret;
                              getr R 8%bv; getr R 9%bv; getr R 18%bv; getr R 19%bv; getr R 20%bv; getr R 21%bv; getr R 22%bv; Z_to_bv 64 fl]).
        assert (R'2 : getr R' 2%bv = Z_to_bv 64 (sp - 192)) by (rewrite (KEPT 2%bv) by inl; exact X2).
        assert (R'8 : getr R' 8%bv = Z_to_bv 64 (ds + 8)) by (rewrite (KEPT 8%bv) by inl; exact X8).
        assert (R'9 : getr R' 9%bv = Z_to_bv 64 (ds + 112)) by (rewrite (KEPT 9%bv) by inl; exact X9).
        assert (R'19 : getr R' 19%bv = Z_to_bv 64 m) by (rewrite (KEPT 19%bv) by inl; exact X19).
        assert (R'3 : getr R' 3%bv = Z_to_bv 64 67584) by (rewrite (KEPT 3%bv) by inl; exact X3).
        assert (R'4 : getr R' 4%bv = Z_to_bv 64 1050296) by (rewrite (KEPT 4%bv) by inl; exact X4).
        assert (HR3 : regs_ok E3 (srs sr_id [(2%bv : reg, EVar 32); (8%bv : reg, EAlu ALU_ADD (EVar 33) (ELit 8));
                                             (9%bv : reg, EAlu ALU_ADD (EVar 33) (ELit 112)); (19%bv : reg, EVar 10)]) R').
        { apply regs_ok_srs; [apply regs_ok_seed|]. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
            (split; [intros E0; discriminate E0 | evs]).
          - exact R'2.
          - rewrite alu_Z by lia. cbn [zar]. rewrite Z.mod_small by lia. exact R'8.
          - rewrite alu_Z by lia. cbn [zar]. rewrite Z.mod_small by lia. exact R'9.
          - rewrite R'19. gnorm (10%bv : reg). rewrite Hr10. reflexivity. }
        pose proof (eq_refl (Z_to_bv 64 (sp - 192))) as Esp2. pose proof (eq_refl (Z_to_bv 64 ds)) as Eds.
        assert (HK3 : know_ok SEGS E3 M'
          [KWr (SA (EVar 32) 0) (ELit 192); KWr (SA (EVar 33) 0) (ELit 392);
           KRange (EVar 32) (2 ^ 40) (2 ^ 47); KRange (EVar 33) (2 ^ 40) (2 ^ 47 - 392); KRange (EVar 10) 1 (2 ^ 47);
           KDisj (SA (EVar 33) 0) (ELit 392) (SA (EVar 32) 0) (ELit 192);
           KImg 0xe6000 0xee000;

           KWord (SA (EVar 32) 88) (N.to_nat 8) (ELit PC_RET_PAD); KWord (SA (EVar 32) 80) (N.to_nat 8) (EVar 33);
           KWord (SA (EVar 32) 72) (N.to_nat 8) (EVar 34); KWord (SA (EVar 32) 64) (N.to_nat 8) (EAlu ALU_ADD (EVar 33) (ELit 112));
           KWord (SA (EVar 32) 56) (N.to_nat 8) (EAlu ALU_ADD (EVar 34) (EVar 10)); KWord (SA (EVar 32) 48) (N.to_nat 8) (EVar 34);
           KWord (SA (EVar 32) 40) (N.to_nat 8) (EAlu ALU_ADD (EVar 33) (ELit 8)); KWord (SA (EVar 32) 32) (N.to_nat 8) (ELit 32);
           KWord (SA (EVar 32) 24) (N.to_nat 8) (EVar 35);

           KWord (SA (EVar 32) 184) (N.to_nat 8) (EVar 36); KWord (SA (EVar 32) 176) (N.to_nat 8) (EVar 37);
           KWord (SA (EVar 32) 168) (N.to_nat 8) (EVar 38); KWord (SA (EVar 32) 160) (N.to_nat 8) (EVar 39);
           KWord (SA (EVar 32) 152) (N.to_nat 8) (EVar 40); KWord (SA (EVar 32) 144) (N.to_nat 8) (EVar 41);
           KWord (SA (EVar 32) 136) (N.to_nat 8) (EVar 42); KWord (SA (EVar 32) 128) (N.to_nat 8) (EVar 43);
           KWord (SA (EVar 32) 112) (N.to_nat 8) (EVar 33);

           KWord (SA (EVar 33) 0) (N.to_nat 8) (ELit VT_OS); KWord (SA (EVar 33) 120) (N.to_nat 4) (EVar 44);
           KWord (SA (EVar 33) 144) (N.to_nat 4) (ELit 0); KWord (SA (EVar 33) 152) (N.to_nat 8) (EAlu ALU_ADD (EVar 33) (ELit 8))]).
        { repeat apply Forall_cons; try apply Forall_nil.
          - eapply (kwr_of_mdef _ _ _ _ (sp - 192) 0 192); [evs; reflexivity | lia | lia | lia | lia | replace (sp - 192 + 0) with (sp - 192) by lia].
            eapply (mdef_via_eff MI A A' M1 M'); [exact EFF | left; lia | lia | lia | intros j Hj; apply (hi_unowned MI A M model); [exact AI | lia] | intros j Hj; apply NF; lia | exact HD1].
          - eapply (kwr_of_mdef _ _ _ _ ds 0 392); [evs; reflexivity | lia | lia | lia | lia | replace (ds + 0) with ds by lia; exact HDM'].
          - eapply krange_var; [evs; reflexivity | lia | lia].
          - eapply krange_var; [evs; reflexivity | lia | lia].
          - krv Hr10.
          - kdj ds 392 (sp - 192) 192. lia.
          - apply kimg_of_clear; [lia | lia |]. intros a Ha. apply (sx_relro ST s M' a SX'). exists 0xe6000, 0xee000. split; [left; reflexivity | lia].
          - kwe (SL2' 0%nat ltac:(cbn; lia)) Esp2. - kwe (SL2' 1%nat ltac:(cbn; lia)) Esp2. - kwe (SL2' 2%nat ltac:(cbn; lia)) Esp2.
          - kwe (SL2' 3%nat ltac:(cbn; lia)) Esp2. - kwe (SL2' 4%nat ltac:(cbn; lia)) Esp2. - kwe (SL2' 5%nat ltac:(cbn; lia)) Esp2.
          - kwe (SL2' 6%nat ltac:(cbn; lia)) Esp2. - kwe (SL2' 7%nat ltac:(cbn; lia)) Esp2. - kwe (SL2' 8%nat ltac:(cbn; lia)) Esp2.
          - kwe (SL1' 0%nat ltac:(cbn; lia)) Esp2. - kwe (SL1' 1%nat ltac:(cbn; lia)) Esp2. - kwe (SL1' 2%nat ltac:(cbn; lia)) Esp2.
          - kwe (SL1' 3%nat ltac:(cbn; lia)) Esp2. - kwe (SL1' 4%nat ltac:(cbn; lia)) Esp2. - kwe (SL1' 5%nat ltac:(cbn; lia)) Esp2.
          - kwe (SL1' 6%nat ltac:(cbn; lia)) Esp2. - kwe (SL1' 7%nat ltac:(cbn; lia)) Esp2.
          - kwe FOS' Esp2.
          - eapply (kword_var _ _ _ _ ds); [eapply fld_cellw; [fld_fix Jvt | unfold VT_OS; cbn; lia] | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity ].
          - eapply (kword_var _ _ _ _ ds); [eapply fld_cellw; [fld_fix Jfl | destruct Iflr as [-> | ->]; unfold DS_FL0, DS_FLHEX; cbn; lia] | cbn; lia | evs; reflexivity | lia | lia | cbn; lia | evs; reflexivity ].
          - kwe Jst Eds.
          - kwe Jrdbuf Eds. }
        xruns HR3 HK3 FUEL [PC_RETPC] (SCR [true] [] []) 60%N.
        { repeat apply Forall_cons; try apply Forall_nil. cbn [sc_denot]. evs. destruct Iflr as [-> | ->]; vm_compute; reflexivity. }
        clear HK3. rename HR' into HR4. rename R'0 into R3. wnorm_goal.
        lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?mm _) _) _ => set (M3 := mm) end.
        regval HR4 (1%bv : reg) ret V1. regval HR4 (10%bv : reg) ds V10.
        eapply srz_msteps; [exact (ms_halt _ MS') | exact (ms_lazy _ MS') | apply (ret_at SEGS PC_RETPC R3 M3 _ (Z_to_bv 64 ret) ltac:(vm_refl_bv) V1 Hret) |].
        assert (ST3 : stores_in (fun a => zwin (ds + 136) (ds + 144) a \/ zwin (sp - 112) (sp - 96) a) M' M3) by (subst M3; stores_tower).
        assert (W3NO : forall a, zwin (ds + 136) (ds + 144) a \/ zwin (sp - 112) (sp - 96) a -> ~ owned MI A' a /\ ~ in_ranges (ly_img Ly.L) a /\ ~ sx_region ST a).
        { intros a Ha. assert (Hhi : alloc_ceiling <= a) by (unfold zwin in Ha; lia).
          split; [apply (hi_unowned MI A' M' model'); [exact AI' | exact Hhi]|]. split; [apply hi_offimg; exact Hhi|].
          intros Hs. apply (hi_offimg (AC:=AC) a Hhi). apply ly_rw_img. apply (sx_region_rw ST). exact Hs. }
        apply (POST A' R3 M3 model' (str_blocks m') (fun a => J a /\ ~ sbuf_fp m0 a)).
        +   constructor.
          * eapply stores_in_ainv; [exact AI' | exact ST3 | intros a Ha; exact (proj1 (W3NO a Ha))].
          * exact MS'. * exact FS'. * exact FDS'.
          * eapply stores_in_sx; [exact SX' | exact ST3 |]. intros a Ha. pose proof (W3NO a Ha) as (_ & Hni & Hns).
            split; [exact Hns | intros Hr; apply Hni; apply ly_relro_img; exact Hr].
          * intros r Hr. unfold callee_saved in Hr. cbn in Hr.
            repeat (destruct Hr as [<-|Hr]; [kept_chain HR4 KEPT XCS|]). destruct Hr.
        + exact V10.
        +
          exists m', pp', hm', fl, 32.
          assert (AG01 : agree_on (fun a => (zwin ds (ds + 256) a \/ zwin (ds + 260) (ds + 392) a)) M M1).
          { eapply stores_in_agree; [exact ST1|]. intros a Ha. unfold W1, zwin in *. lia. }
          eapply (ds_inv_resb MI A A' M M3); [exact DI0 | | | | | lia | rewrite Hw'; lia |].
          * eapply (sb_inv_frame MI A' A' M' M3); [exact SB' | lia | lia | | intros blk Hb; destruct blk as [d a]; exact (proj1 (Hm'blk d a ltac:(destruct m'; cbn in Hb; [destruct Hb | destruct Hb as [E|[]]; congruence])))].
            eapply stores_in_agree; [exact ST3|]. intros a Ha. unfold sb_fp, zwin in *.
            destruct Ha as [Ha|Ha]; [lia|]. destruct m' as [|d1 a1]; [destruct Ha|]. destruct (Hm'blk d1 a1 eq_refl) as (_ & Hp1 & Hc). lia.
          *
            assert (IOS1 : ios_inv M1 (ds + 112) (ds + 8) fl 32).
            { eapply (ios_inv_refill M M1); [exact II1 | lia | lia | | | replace (ds + 112 + 144) with (ds + 256) by lia; exact FFILL | right; reflexivity].
              - eapply agree_on_weaken; [exact AG01|]. intros a (Ha & Hb & Hc). unfold zwin in *. lia.
              - apply T0; [cbn; lia | lia | lia | cbn; lia | exact Iwid]. }
            assert (IOS2 : ios_inv M' (ds + 112) (ds + 8) fl 32).
            { eapply ios_inv_frame; [exact IOS1 | lia | lia | eapply agree_on_weaken; [exact AGD1|]; intros a Ha; unfold zwin in *; lia]. }
            subst M3. replace (Z_to_bv 64 (ds + 136)) with (Z_to_bv 64 (ds + 112 + 24)) by (f_equal; lia).
            lazymatch goal with |- ios_inv ?mm _ _ _ _ =>
              assert (ST3b : stores_in (zwin (sp - 112) (sp - 96)) (wbytes M' (Z_to_bv 64 (ds + 112 + 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) mm) by stores_tower end.
            eapply ios_inv_frame; [apply ios_inv_setwidth; [exact IOS2 | lia | lia] | lia | lia |].
            eapply stores_in_agree; [exact ST3b|]. intros a Ha. unfold zwin in *. lia.
          * eapply stores_in_mdef; [exact ST3 | exact HDM'].
          * intros a Ha. rewrite (proj1 ST3 (Z_to_bv 64 a)) by (rewrite u64_of_Z by (unfold zwin in Ha; lia); unfold zwin in *; lia).
            destruct Ha as [Ha|Ha]; [rewrite (AGD0 a Ha) | rewrite (AGD1 a ltac:(unfold zwin in *; lia))]; apply AG01; unfold zwin in *; lia.
          * intros d a E. destruct (Hm'blk d a E) as (HIn & Hd & Hc). pose proof (ri_shape _ _ _ _ _ _ _ _ RI') as SH. pose proof (ri_w _ _ _ _ _ _ _ _ RI') as RW.
            unfold DS_MAXBLK, DS_MAXLEN in *.
            destruct SH as [->|(d' & j & Hj & E' & Hb)].
            -- split; [pose proof (Gasz d a E); lia|]. split; [exact (Gmx d a E)|]. split; [exact (Gpow d a E) | lia].
            -- rewrite E' in E. injection E as <- <-. replace (ds + 8 + 64) with (ds + 72) in Hb by lia. fold w0 in Hb. split; [lia|]. split; [lia|]. split; [exists j; split; [exact Hj | reflexivity] | lia].
        + rewrite GB. exact (ri_xfer SEGS Ly.L MI A m0 BL0 _ _ _ RI').
        +   intros a [Hj Hnb]. destruct (JK a Hj) as (Hlo & Hni & Hmiss). split; [exact Hlo|]. split; [exact Hni|].
          intros q k Hin Hq. destruct m0 as [|d0 a0]; [exact (Hmiss q k Hin ltac:(intros []) Hq)|].
          destruct (Z.eq_dec q d0) as [->|Hne]; [destruct (Z.eq_dec k a0) as [->|Hne2]|].
          * apply Hnb. cbn. unfold zwin. lia.
          * exact (Hmiss d0 k Hin ltac:(intros [E|[]]; injection E; lia) Hq).
          * exact (Hmiss q k Hin ltac:(intros [E|[]]; injection E; lia) Hq).
        +
          assert (E01 : eff MI A A M M1 (sp - S, sp) (fun a => zwin (ds + 256) (ds + 260) a)).
          { eapply (eff_of_stores MI); [exact ST1|]. intros a [Ha|Ha]; [right; unfold W_of, zwin in *; cbn; lia | left; exact Ha]. }
          pose proof (eff_widen MI A A' M1 M' _ (sp - S, sp) _ EFF ltac:(cbn; lia) ltac:(cbn; lia)) as E12.
          assert (E23 : eff MI A' A' M' M3 (sp - S, sp) (fun a => zwin (ds + 136) (ds + 144) a)).
          { eapply (eff_of_stores MI); [exact ST3|]. intros a [Ha|Ha]; [left; exact Ha | right; unfold W_of, zwin in *; cbn; lia]. }
          assert (WUN : forall a, W_of (sp - S, sp) a -> ~ owned MI A' a).
          { intros a Ha. unfold W_of in Ha. cbn in Ha. apply (hi_unowned MI A' M' model'); [exact AI' | lia]. }
          pose proof (eff_trans _ _ _ _ _ _ _ _ _ _ (eff_trans _ _ _ _ _ _ _ _ _ _ E01 E12 WUN) E23 WUN) as E03. cbn beta in E03.
          eapply eff_weaken; [exact E03|]. intros a Ha. unfold ds_foot, DS_SIZE. rewrite GB.
          destruct Ha as [[Ha|[Hz|[Hb|[Hb|Hj]]]]|Ha].
          * left. left. unfold zwin in *. lia.
          * left. left. unfold zwin in *. lia.
          * left. right. destruct m0 as [|d0 a0]; [destruct Hb|]. exists d0, a0. split; [left; reflexivity | cbn in Hb; unfold zwin in Hb; lia].
          * right. left. right. destruct m' as [|d1 a1]; [destruct Hb|]. exists d1, a1. split; [left; reflexivity | cbn in Hb; unfold zwin in Hb; lia].
          * destruct (Classical_Prop.classic (sbuf_fp m0 a)) as [Hb|Hnb].
            -- left. right. destruct m0 as [|d0 a0]; [destruct Hb|]. exists d0, a0. split; [left; reflexivity | cbn in Hb; unfold zwin in Hb; lia].
            -- right. right. split; assumption.
          * left. left. unfold zwin in *. lia.
      - exact X10. - exact X11. - exact X12.
    Qed.

  End Call.
End PutCstr.
