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
  RefMemcpyLib LibIface LibEff LibMaskBits ZStores SymExec3 SymExec3Sound SymRun3 LibTail SumMemsetLib SumMemset S1Layout.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContLib StrLib ContStmts S1Facts LiveStats Lib_Str_PushBack Lib_Str_Resize.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HLib.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsGrammar PrsNeeds.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Import RunsLib.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag Require Import
  DiagTac DiagVia DiagViaS1 DiagPins DiagS1 DRep DFacts DsRoom DiagStmts SbOverflow Xsputn PutCstr.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import RunRandom.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Module Ly := S1Layout.
Abbreviation SEGS := Plain.M.loaded_segments.

Definition PC_RET_MEMSET : Z := 0x8ece4.
Definition GLOBAL_GUARD : Z := 0xff0e8.
Definition GLOBAL_LOC : Z := 0xff0e0.

Definition FUELS : nat := 100%nat.
Definition PC_BACKS : Z := 0x69c84.
Definition PC_RETS : Z := 0x69c94.

Section PutString.
Context {AC : AllocCeiling}.
Context {RRND : RunRandom}.
  Variable MI : MallocIface SEGS Ly.L.
  Variable ST : StaticsIface SEGS Ly.L.
  Hypothesis DN : diag_needs MI ST.

  #[local] Notation cfg fx R pc M model := (mkCfg (@mkst fx R (Z_to_bv 64 pc) M (seg_rom SEGS)) model).

  Section Call.
    Context {fx : FPState}.
    Variables (A : AS MI) (s : LibIface.SX ST) (R : bvmap 5 word) (M : mem) (model : Model).
    Variables (sp ret ds err len str : Z) (m : sbuf) (cs : list Z) (B : list (Z * Z)) (K : TSet).
    Variables (m0 : sbuf) (pp0 hm0 fl fill : Z).
    Hypothesis CB : callB MI ST A s R M model sp ret 12288.
    Hypothesis ROC : ro_clear Ly.L M.
    Hypothesis Ha0 : getr R 10%bv = Z_to_bv 64 ds.
    Hypothesis Ha1 : getr R 11%bv = Z_to_bv 64 str.
    Hypothesis DI0 : ds_inv A M ds err len B m0 pp0 hm0 fl fill.
    Hypothesis ABOVE : above_sp MI A sp ds 392.
    Hypothesis STR : str_rep MI A M str m cs.
    Hypothesis SAB : above_sp MI A sp str 24.
    Hypothesis DISJ : forall a, zwin ds (ds + 392) a -> ~ zwin str (str + 24) a.
    Hypothesis OWN : forall b, In b (str_blocks m) -> ~ In b B.
    Hypothesis BUD : len + Zlen cs <= DS_MAXLEN.
    Hypothesis ROOM : ds_room SEGS Ly.L MI A.
    Hypothesis POST : forall A' R' M' model' B' (J : Z -> Prop),
        retB MI ST A' s R R' M' model model' -> getr R' 10%bv = Z_to_bv 64 ds ->
        ds_rep MI A' M' ds err (len + Zlen cs) B' -> blk_xfer B B' (live MI A) (live MI A') -> junk_ok MI A J ->
        eff MI A A' M M' (sp - 12288, sp) (fun a => ds_foot ds B a \/ ds_foot ds B' a \/ J a) ->
        srealizes SEGS (cfg fx R' ret M' model') K.

    Lemma pstr_main : srealizes SEGS (cfg fx R A_PUT_STRING M model) K.
    Proof using AC RRND MI ST DN fx A s R M model sp ret ds err len str m cs B K m0 pp0 hm0 fl fill CB ROC Ha0 Ha1 DI0 ABOVE STR SAB DISJ OWN BUD ROOM POST.
      pose proof CB as CB0. destruct CB0 as [AI MS ROC' SXI SXH [Hra Hret Hretr Hsp Hsp16 Hsphi Hgp Htp] Hceil HROOM Hwin Hown_sx Herr_sx].
      cbn [ly_gp ly_tp Ly.L] in Hgp, Htp. pose proof ac_bounds_lit as Hcv. pose proof (dn_mstack MI ST DN) as HMS.
      destruct ABOVE as (Hds_sp & Hds_hi & Hds_own). destruct SAB as (Hs_sp & Hs_hi & Hs_own).
      pose proof STR as STR0. destruct STR0 as (Hs0 & Hs1 & HDs & Hlen & HM & FC & FN).
      assert (HDstk : mdef M (sp - 12288) 12288).
      { eapply store_ok_mdef_offimg; [exact HROOM | lia | lia | lia | intros x Hx; apply ly_noseg; lia]. }
      set (dat := str_data str m). set (n := Zlen cs).
      assert (Hdat : 0 <= dat /\ dat + n <= 2 ^ 47 /\ (forall a, dat <= a < dat + n -> ~ zwin ds (ds + 392) a /\ sp <= a \/ exists d asz, m = SLong d asz /\ d <= a < d + asz /\ d + asz <= alloc_ceiling)).
      { subst dat n. destruct m as [|d asz]; cbn [str_data str_cap] in *.
        - split; [lia|]. split; [unfold SSO_CAP in Hlen; lia|]. intros a Ha. left. split; [intros Hz; apply (DISJ a Hz); unfold zwin; unfold SSO_CAP in Hlen; lia | lia].
        - destruct HM as (Hd0 & _ & Hdsz & _ & _ & HIn & _). pose proof (live_range _ _ MI A M model d asz AI HIn). split; [lia|]. split; [lia|].
          intros a Ha. right. exists d, asz. split; [reflexivity | lia]. }
      destruct Hdat as (Hd0 & Hd1 & Hsrc).

      set (E := Eseed R (match m with SShort => [Z_to_bv 64 (2 * n)] | SLong d asz => [Z_to_bv 64 (asz + 1); Z_to_bv 64 n; Z_to_bv 64 d] end)).
      assert (HR : regs_ok E sr_id R) by (apply regs_ok_seed).
      assert (HK : know_ok SEGS E M ([KWr (SA (EVar 2) (-16)) (ELit 16); KRange (EVar 2) (2 ^ 40) (2 ^ 47); KRange (EVar 11) (2 ^ 40) (2 ^ 47 - 24);
                                       KDisj (SA (EVar 11) 0) (ELit 24) (SA (EVar 2) (-16)) (ELit 16)]
          ++ match m with SShort => [KWord (SA (EVar 11) 0) (N.to_nat 1) (EVar 32); KRange (EVar 32) 0 44]
                        | SLong _ _ => [KWord (SA (EVar 11) 0) (N.to_nat 8) (EVar 32); KWord (SA (EVar 11) 8) (N.to_nat 8) (EVar 33); KWord (SA (EVar 11) 16) (N.to_nat 8) (EVar 34)] end)).
      { apply Forall_app. split.
        - repeat apply Forall_cons; try apply Forall_nil.
          + eapply kwr_stack; [evs; exact Hsp | reflexivity | lia | lia | eapply stack_room_mono; [exact HROOM | lia | lia | lia]].
          + krv Hsp. + krv Ha1.
          + kdj str 24 sp 16. lia.
        - subst E. destruct m as [|d asz]; cbn [str_data str_cap] in HM, Hlen |- *; repeat apply Forall_cons; try apply Forall_nil.
          + unfold SSO_CAP in Hlen. eapply (kword_var _ _ _ _ str); [eapply fld_cellw; [fld_fix HM | cbn; lia] | cbn; lia | evs; exact Ha1 | lia | lia | cbn; lia | evs; reflexivity ].
          + unfold SSO_CAP in Hlen. eapply krange_var; [evs; reflexivity | lia | lia].
          + destruct HM as (Hd00 & _ & Hdsz & _ & Hmin & _ & _ & Fcap & Fsz & Fdat). unfold SSO_CAP in Hmin. kwv Fcap Ha1.
          + destruct HM as (Hd00 & _ & Hdsz & _ & Hmin & _ & _ & Fcap & Fsz & Fdat). subst n. kwv Fsz Ha1.
          + destruct HM as (Hd00 & _ & Hdsz & _ & Hmin & _ & _ & Fcap & Fsz & Fdat). kwv Fdat Ha1. }
      assert (STEP : forall R1 (M1 : mem),
        getr R1 1%bv = Z_to_bv 64 PC_BACKS -> getr R1 2%bv = Z_to_bv 64 (sp - 16) -> getr R1 10%bv = Z_to_bv 64 ds ->
        getr R1 11%bv = Z_to_bv 64 dat -> getr R1 12%bv = Z_to_bv 64 n -> getr R1 8%bv = Z_to_bv 64 ds ->
        (forall r, In r [3; 4; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr R1 r = getr R r) ->
        M1 = wbytes (wbytes M (Z_to_bv 64 (sp + -8)) (word_to_le_bytes 8 (Z_to_bv 64 ret))) (Z_to_bv 64 (sp + -16)) (word_to_le_bytes 8 (getr R 8%bv)) ->
        srealizes SEGS (cfg fx R1 A_PUT_CSTR M1 model) K).
      2: { subst E. destruct m as [|d asz]; cbn [str_data str_cap] in dat, HM, Hlen.
           - unfold SSO_CAP in Hlen.
             xruns HR HK FUELS [A_PUT_CSTR] (SCR [true; true] [] []) 40%N.
             { repeat apply Forall_cons; try apply Forall_nil; cbn [sc_denot]; evs; cbn [branch_taken]; subst n;
                 rewrite alu_Z by lia; cbn [zar]; rewrite even_land_1 by lia; unfold bv_eqb; rewrite !u64_of_Z by lia; reflexivity. }
             clear HK. rename HR' into HR1. rename R' into R1. wnorm_goal.
             eapply STEP; [ | | | | | | | reflexivity].
             + regval HR1 (1%bv : reg) PC_BACKS V; exact V. + regval HR1 (2%bv : reg) (sp - 16) V; exact V. + regval HR1 (10%bv : reg) ds V; exact V.
             + regval HR1 (11%bv : reg) dat V; exact V.
             + rreg HR1 (12%bv : reg) T. rewrite T. rewrite alu_Z by lia. cbn [zar]. f_equal. rewrite Z.pow_1_r. subst n. rewrite Z.mul_comm, Z.div_mul by lia. reflexivity.
             + regval HR1 (8%bv : reg) ds V; exact V.
             + intros r Hr. cbn in Hr. repeat (destruct Hr as [<-|Hr]; [kept_chain HR1|]). destruct Hr.
           - destruct HM as (Hd00 & _ & Hdsz & Hal8 & Hmin & _ & _ & Fcap & Fsz & Fdat). unfold SSO_CAP in Hmin.
             xruns HR HK FUELS [A_PUT_CSTR] (SCR [false; true] [] []) 40%N.
             { repeat apply Forall_cons; try apply Forall_nil; cbn [sc_denot]; evs; cbn [branch_taken]; rewrite ext_Z_val by lia;
                 change (8 * Z.of_nat 0) with 0; change (2 ^ (8 * Z.of_nat 1)) with 256; rewrite Z.pow_0_r, Z.div_1_r;
                 rewrite alu_Z by (pose proof (Z.mod_pos_bound (asz + 1) 256 ltac:(lia)); lia); cbn [zar];
                 rewrite odd_byte0 by lia; unfold bv_eqb; rewrite !u64_of_Z by lia; reflexivity. }
             clear HK. rename HR' into HR1. rename R' into R1. wnorm_goal.
             eapply STEP; [ | | | | | | | reflexivity].
             + regval HR1 (1%bv : reg) PC_BACKS V; exact V. + regval HR1 (2%bv : reg) (sp - 16) V; exact V. + regval HR1 (10%bv : reg) ds V; exact V.
             + regval HR1 (11%bv : reg) dat V; exact V. + regval HR1 (12%bv : reg) n V; exact V. + regval HR1 (8%bv : reg) ds V; exact V.
             + intros r Hr. cbn in Hr. repeat (destruct Hr as [<-|Hr]; [kept_chain HR1|]). destruct Hr. }
      intros R1 M1 X1 X2 X10 X11 X12 X8 YS EM1.
      assert (ST1 : stores_in (zwin (sp - 16) sp) M M1) by (rewrite EM1; stores_tower).
      assert (WNO : forall a, zwin (sp - 16) sp a -> ~ owned MI A a /\ ~ in_ranges (ly_img Ly.L) a /\ ~ sx_region ST a).
      { intros a Ha. unfold zwin in Ha. pose proof (Hwin a ltac:(unfold zwin; lia)) as [H1 H2]. split; [exact H1|]. split; [apply hi_offimg; lia | exact H2]. }
      assert (AI1 : ainv MI A M1 model) by (eapply stores_in_ainv; [exact AI | exact ST1 | intros a Ha; exact (proj1 (WNO a Ha))]).
      assert (SX1 : sx_inv ST s M1).
      { eapply stores_in_sx; [exact SXI | exact ST1 |]. intros a Ha. pose proof (WNO a Ha) as (_ & Hni & Hns).
        split; [exact Hns | intros Hr; apply Hni; apply ly_relro_img; exact Hr]. }
      assert (ROC1 : ro_clear Ly.L M1).
      { eapply ro_clear_frame; [exact ROC | eapply stores_in_frame_eq; [exact ST1 | intros a Ha; exact Ha] |].
        intros a (Himg & _) Hw. exact (proj1 (proj2 (WNO a Hw)) Himg). }
      assert (HDf : mdef M1 (sp - 16) 16) by (eapply stores_in_mdef; [exact ST1|]; eapply mdef_sub; [exact HDstk | lia | lia]).
      assert (HXS : XS_STK MI = 208 + (16 + MALLOC_STACK MI)) by (unfold XS_STK, OVF_STK, NEW_STACK; lia).
      apply (put_main MI ST DN A s R1 M1 model (sp - 16) PC_BACKS 12272 ds err len dat n B K m0 pp0 hm0 fl fill).
      - constructor.
        + exact AI1. + exact MS. + exact (img_ro_clear_of' ST s M1 ROC1 SX1). + exact SX1. + exact SXH.
        + constructor; [exact X1 | apply bv_eq; vm_compute; reflexivity | unfold PC_BACKS; lia | exact X2 | mlia | lia | rewrite (YS 3%bv) by inl; exact Hgp | rewrite (YS 4%bv) by inl; exact Htp].
        + lia.
        + unfold stack_room. eapply stores_in_store_ok; [exact ST1|].
          replace (Z_to_bv 64 (sp - 16 - 12272)) with (Z_to_bv 64 (sp - 12288)) by (f_equal; lia).
          apply (mdef_store_ok SEGS M (sp - 12288) 12288); [exact HDstk | lia | lia | lia].
        + intros a Ha. split; [apply (hi_unowned MI A M1 model); [exact AI1 | unfold zwin in Ha; lia] | apply (proj2 (Hwin a ltac:(unfold zwin in *; lia)))].
        + exact Hown_sx. + exact Herr_sx.
      - lia.
      - exact ROC1.
      - exact X10. - exact X11. - exact X12.
      - eapply (ds_inv_frame MI A A M M1); [exact DI0 | | intros blk Hb; pose proof (di_B _ _ _ _ _ _ _ _ _ _ _ _ DI0) as EB; rewrite EB in Hb;
            destruct (si_str _ _ _ _ _ _ _ (di_sb _ _ _ _ _ _ _ _ _ _ _ _ DI0)) as (cs0 & SR0 & _); exact (str_blocks_live MI _ _ _ _ _ SR0 blk Hb)].
        eapply stores_in_agree; [exact ST1|]. intros a Ha. unfold ds_foot, DS_SIZE, zwin in *. destruct Ha as [Ha|(q & k & Hin & Hq)]; [lia|].
        pose proof (di_B _ _ _ _ _ _ _ _ _ _ _ _ DI0) as EB. rewrite EB in Hin.
        destruct (si_str _ _ _ _ _ _ _ (di_sb _ _ _ _ _ _ _ _ _ _ _ _ DI0)) as (cs0 & SR0 & _).
        pose proof (str_blocks_live MI _ _ _ _ _ SR0 _ Hin) as HIn0. pose proof (live_range _ _ MI A M model q k AI HIn0). lia.
      - split; [lia | split; [lia | exact Hds_own]].
      - subst n. lia.
      - intros a Ha. destruct (Hsrc a Ha) as [[Hnz Hsa] | (d & asz & Em & Hda & Hdc)].
        + split; [exact Hnz | left; lia].
        + split; [unfold zwin; lia | right; right]. exists d, asz.
          rewrite Em in STR. destruct STR as (_ & _ & _ & _ & (_ & _ & _ & _ & _ & HIn & _) & _).
          split; [exact HIn|]. split; [lia|]. rewrite <- (di_B _ _ _ _ _ _ _ _ _ _ _ _ DI0). apply OWN. rewrite Em. left. reflexivity.
      - exists (str_bytes cs). subst n. unfold Zlen in *. rewrite Nat2Z.id.
        erewrite <- (fld_str_rdn SEGS M dat cs); [ | lia | unfold Zlen in *; lia | exact FC].
        apply rdn_ext; [rewrite u64_of_Z by lia; lia|]. intros x Hx. rewrite u64_of_Z in Hx by lia.
        apply (proj1 ST1). intros Hw. unfold zwin in Hw. destruct (Hsrc (bv_unsigned x) ltac:(lia)) as [[_ Hsa] | (d & asz & _ & Hda & Hdc)]; lia.
      - subst n. exact BUD.
      - exact ROOM.
      -
        intros A' R' M' model' B' J RB H10 DS XF JK EF.
        pose proof RB as RB0. destruct RB as [AI' MS' FS' FDS' SX' KEPT].
        assert (NF : forall a, sp - 16 <= a < sp -> ~ (ds_foot ds B a \/ ds_foot ds B' a \/ J a)).
        { intros a Ha [Hf|[Hf|Hj]].
          - unfold ds_foot, DS_SIZE, zwin in Hf. destruct Hf as [Hz|(q & k & Hin & Hq)]; [lia|].
            rewrite (di_B _ _ _ _ _ _ _ _ _ _ _ _ DI0) in Hin. destruct (si_str _ _ _ _ _ _ _ (di_sb _ _ _ _ _ _ _ _ _ _ _ _ DI0)) as (cs0 & SR0 & _).
            pose proof (live_range _ _ MI A M model q k AI (str_blocks_live MI _ _ _ _ _ SR0 _ Hin)). lia.
          - unfold ds_foot, DS_SIZE, zwin in Hf. destruct Hf as [Hz|(q & k & Hin & Hq)]; [lia|].
            destruct (ds_blocks MI A' M' ds err _ B' DS) as [_ HB]. destruct (HB q k Hin) as [HIn' _].
            pose proof (live_range _ _ MI A' M' model' q k AI' HIn'). lia.
          - destruct (JK a Hj) as (Hlo & _). lia. }
        assert (AGS : agree_on (zwin (sp - 16) sp) M1 M').
        { eapply (agree_hi_via_eff MI A A' M1 M'); [exact EF | exact AI1 | exact AI' | lia | lia | replace (sp - (sp - 16)) with 16 by lia; exact HDf | intros a Ha; apply NF; lia | cbn; lia]. }
        assert (T : forall a (kk : nat) v, sp - 16 <= a -> a + Z.of_nat kk <= sp -> fld SEGS M1 a kk v -> fld SEGS M' a kk v).
        { intros a kk v H1 H2 HF. eapply fld_agree; [lia | lia | exact HF | eapply agree_on_weaken; [exact AGS|]; intros x Hx; unfold zwin in *; lia]. }
        assert (F8' : fld SEGS M' (sp - 16 + 8) 8 ret) by (apply T; [lia | cbn; lia |]; unfold fld; rewrite EM1; peel).
        assert (F0' : fld SEGS M' (sp - 16) 8 (bv_unsigned (getr R 8%bv))).
        { apply T; [lia | cbn; lia |]. unfold fld. rewrite EM1. rewrite Z_to_bv_bv_unsigned. peel. }
        assert (R'2 : getr R' 2%bv = Z_to_bv 64 (sp - 16)) by (rewrite (KEPT 2%bv) by inl; exact X2).
        assert (R'8 : getr R' 8%bv = Z_to_bv 64 ds) by (rewrite (KEPT 8%bv) by inl; exact X8).
        pose proof (u64_range (getr R 8%bv)) as HR8r.
        set (E3 := Eseed R' [Z_to_bv 64 ret; getr R 8%bv]).
        assert (HR3 : regs_ok E3 sr_id R') by (apply regs_ok_seed).
        assert (HK3 : know_ok SEGS E3 M' [KRange (EVar 2) (2 ^ 40) (2 ^ 47); KWord (SA (EVar 2) 8) (N.to_nat 8) (EVar 32); KWord (SA (EVar 2) 0) (N.to_nat 8) (EVar 33)]).
        { repeat apply Forall_cons; try apply Forall_nil; [krv R'2 | kwe F8' R'2 | kwe F0' R'2]. }
        xruns HR3 HK3 FUELS [PC_RETS] (SCR [] [] []) 40%N. { scs_auto. }
        clear HK3. rename HR' into HR4. rename R'0 into R4.
        regval HR4 (1%bv : reg) ret V1. regval HR4 (10%bv : reg) ds V10.
        eapply srz_msteps; [exact (ms_halt _ MS') | exact (ms_lazy _ MS') | apply (ret_at SEGS PC_RETS R4 M' _ (Z_to_bv 64 ret) ltac:(vm_refl_bv) V1 Hret) |].
        apply (POST A' R4 M' model' B' J); [ | exact V10 | exact DS | exact XF | exact JK |].
        + constructor; [exact AI' | exact MS' | exact FS' | exact FDS' | exact SX' |].
          intros r Hr. unfold callee_saved in Hr. cbn in Hr. repeat (destruct Hr as [<-|Hr]; [kept_chain HR4 KEPT YS|]). destruct Hr.
        + assert (E01 : eff MI A A M M1 (sp - 12288, sp) (fun _ => False)).
          { eapply (eff_of_stores MI); [exact ST1|]. intros a Ha. right. unfold W_of, zwin in *. cbn. lia. }
          pose proof (eff_widen MI A A' M1 M' _ (sp - 12288, sp) _ EF ltac:(cbn; lia) ltac:(cbn; lia)) as E12.
          assert (WUN : forall a, W_of (sp - 12288, sp) a -> ~ owned MI A' a).
          { intros a Ha. unfold W_of in Ha. cbn in Ha. apply (hi_unowned MI A' M' model'); [exact AI' | lia]. }
          pose proof (eff_trans _ _ _ _ _ _ _ _ _ _ E01 E12 WUN) as E02. eapply eff_weaken; [exact E02|]. intros a [[]|Ha]. exact Ha.
    Qed.
  End Call.

  Theorem put_string : put_string_stmt SEGS Ly.L MI ST dcS1 (ds_rep MI).
  Proof using AC RRND MI ST DN.
    intros fx A s R M model sp ret ds err len str m cs B K CB ROC Ha0 Ha1 (m0 & pp0 & hm0 & fl & fill & DI) ABOVE STR SAB DISJ OWN BUD ROOM POST.
    cbn [dc_stack dc_put_string dcS1] in *. unfold DS_SIZE in *.
    eapply (pstr_main A s R M model sp ret ds err len str m cs B K m0 pp0 hm0 fl fill CB ROC Ha0 Ha1 DI ABOVE STR SAB DISJ OWN BUD ROOM).
    intros A' R' M' model' B' J RB H10 DS XF JK EF. unfold ds_op_post in POST. cbn [dc_stack dcS1] in POST.
    apply (POST A' R' M' model' B' J RB ltac:(intros _; exact H10) DS XF JK). eapply eff_weaken; [exact EF | intros a Ha; cbn beta in *; tauto].
  Qed.
End PutString.

