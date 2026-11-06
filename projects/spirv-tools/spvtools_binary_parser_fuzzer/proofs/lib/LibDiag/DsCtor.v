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
  DiagTac DiagVia DiagViaS1 DiagPins DiagS1 DRep DFacts DsRoom DiagStmts DsCtorTail.
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

Lemma cellw_of_bytes : forall M a, 0 <= a -> a + 8 <= 2 ^ 64 ->
  (exists bs, rdn SEGS M (Z_to_bv 64 a) 8 = Some bs) -> exists v, cellw SEGS M a 8 v.
Proof.
  intros M a Ha Ha8 (bs & RD). pose proof (rdn_length _ _ _ _ _ RD) as HL.
  exists (lez bs). pose proof (lez_bound_len bs 8 HL) as Hb. split; [cbn; cbn in Hb; lia|].
  change (N.to_nat 8) with 8%nat. rewrite RD. f_equal.
  unfold word_to_le_bytes. rewrite u64_of_Z by (cbn in Hb; lia). rewrite <- HL. symmetry. apply Z_to_le_bytes_lez.
Qed.

Lemma rdn_of_mdef_hi : forall M a (n : nat), mdef M a (Z.of_nat n) -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  exists bs, rdn SEGS M (Z_to_bv 64 a) n = Some bs.
Proof.
  intros M a n. revert a. induction n as [|n IH]; intros a HD Ha Hn; [exists []; reflexivity|].
  destruct (M (Z_to_bv 64 a)) as [b|] eqn:Hb; [|exfalso; apply (HD 0 ltac:(lia)); rewrite Z.add_0_r; exact Hb].
  destruct (IH (a + 1)) as (bs & RD); [intros i Hi; replace (a + 1 + i) with (a + (1 + i)) by lia; apply HD; lia | lia | lia |].
  exists (b :: bs). cbn [rdn]. rewrite Hb. replace (Z_to_bv 64 a + 1)%bv with (Z_to_bv 64 (a + 1)); [rewrite RD; reflexivity|].
  rewrite w_add_1. rewrite u64_of_Z by lia. reflexivity.
Qed.

Section DsCtor.
Context {AC : AllocCeiling}.
Context {RRND : RunRandom}.
  Variable MI : MallocIface SEGS Ly.L.
  Variable ST : StaticsIface SEGS Ly.L.
  Hypothesis DN : diag_needs MI ST.

  #[local] Notation cfg fx R pc M model := (mkCfg (@mkst fx R (Z_to_bv 64 pc) M (seg_rom SEGS)) model).

  Section Call.
    Context {fx : FPState}.
    Variables (A : AS MI) (s : LibIface.SX ST) (R : bvmap 5 word) (M : mem) (model : Model).
    Variables (sp ret ds ppos pcons pstr1 err pstr2 : Z) (K : TSet).
    Variable S : Z.
    Hypothesis CB : callB MI ST A s R M model sp ret S.
    Hypothesis HS : 208 <= S.
    Hypothesis ROC : ro_clear Ly.L M.
    Hypothesis Ha0 : getr R 10%bv = Z_to_bv 64 ds.
    Hypothesis Ha1 : getr R 11%bv = Z_to_bv 64 ppos.
    Hypothesis Ha2 : getr R 12%bv = Z_to_bv 64 pcons.
    Hypothesis Ha3 : getr R 13%bv = Z_to_bv 64 pstr1.
    Hypothesis Ha4 : getr R 14%bv = Z_to_bv 64 (err mod 2 ^ 64).
    Hypothesis Ha5 : getr R 15%bv = Z_to_bv 64 pstr2.
    Hypothesis Herr : - 2 ^ 31 <= err < 0.
    Hypothesis Hds : above_sp MI A sp ds 392 /\ ds mod 8 = 0 /\ mdef M ds 392.
    Hypothesis Hpos : above_sp MI A sp ppos 24 /\ mdef M ppos 24.
    Hypothesis Hs1 : above_sp MI A sp pstr1 24 /\ fld SEGS M pstr1 2 0 /\ mdef M pstr1 24.
    Hypothesis Hs2 : above_sp MI A sp pstr2 24 /\ fld SEGS M pstr2 2 0 /\ mdef M pstr2 24.
    Hypothesis Hcons : obj_ok MI A sp S pcons 48 /\ fld SEGS M (pcons + 32) 8 0.
    Hypothesis Hpc_hi : pcons + 48 <= 2 ^ 47.
    Hypothesis DISJ : forall a, zwin ds (ds + 392) a ->
        ~ zwin ppos (ppos + 24) a /\ ~ zwin pstr1 (pstr1 + 24) a /\ ~ zwin pstr2 (pstr2 + 24) a /\ ~ zwin pcons (pcons + 48) a.
    Hypothesis CONT : forall A' R' M' model' B,
        retB MI ST A' s R R' M' model model' ->
        ds_rep MI A' M' ds err 0 B ->
        blk_xfer [] B (live MI A) (live MI A') ->
        eff MI A A' M M' (sp - S, sp) (ds_foot ds B) ->
        srealizes SEGS (cfg fx R' ret M' model') K.

    Lemma ctor_main : srealizes SEGS (cfg fx R A_DS_CTOR M model) K.
    Proof using AC RRND MI ST DN fx A s R M model sp ret ds ppos pcons pstr1 err pstr2 K S CB HS Ha0 Ha1 Ha2 Ha3 Ha4 Ha5 Herr Hds Hpos Hs1 Hs2 Hcons Hpc_hi DISJ CONT.
      pose proof CB as CB0. destruct CB0 as [AI MS ROC' SXI SXH [Hra Hret Hretr Hsp Hsp16 Hsphi Hgp Htp] Hceil HROOM Hwin Hown_sx Herr_sx].
      cbn [ly_gp ly_tp Ly.L] in Hgp, Htp. pose proof ac_bounds_lit as Hcv. pose proof (dn_mstack MI ST DN) as HMS.
      destruct Hds as ((Hds_sp & Hds_hi & Hds_own) & Hal & HDds). destruct Hpos as ((Hp_sp & Hp_hi & Hp_own) & HDp).
      destruct Hs1 as ((H1_sp & H1_hi & H1_own) & F1z & HD1). destruct Hs2 as ((H2_sp & H2_hi & H2_own) & F2z & HD2).
      destruct Hcons as ([PLc DJc] & Fcf).
      pose proof (dn_statics MI ST DN s M SXI) as PINS.

      set (E := Eseed R []).
      assert (HR : regs_ok E sr_id R) by (apply regs_ok_seed).
      assert (HK : know_ok SEGS E M
        [KWr (SA (EVar 2) (-208)) (ELit 208); KWr (SA (EVar 10) 0) (ELit 392);
         KRange (EVar 2) (2 ^ 40) (2 ^ 47); KRange (EVar 10) (2 ^ 40) (2 ^ 47 - 392);
         KDisj (SA (EVar 10) 0) (ELit 392) (SA (EVar 2) (-208)) (ELit 208);
         KImg 0xe6000 0xee000]).
      { repeat apply Forall_cons; try apply Forall_nil.
        - eapply kwr_stack; [evs; exact Hsp | reflexivity | lia | lia | eapply stack_room_mono; [exact HROOM | lia | lia | lia]].
        - eapply (kwr_of_mdef _ _ _ _ ds 0 392); [evs; exact Ha0 | lia | lia | lia | lia | replace (ds + 0) with ds by lia; exact HDds].
        - krv Hsp. - krv Ha0.
        - kdj ds 392 sp 208. lia.
        - apply kimg_of_clear; [lia | lia |]. intros a Ha. apply (sx_relro ST s M a SXI). exists 0xe6000, 0xee000. split; [left; reflexivity | lia]. }
      xruns HR HK FUEL [A_MEMSET] (SCR [] [] []) 60%N.
      { scs_auto. }
      clear HK. rename HR' into HR1. rename R' into R1. wnorm_goal.
      lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?mm _) _) _ => set (M1 := mm) end.
      regval HR1 (1%bv : reg) PC_RET_MEMSET X1. regval HR1 (2%bv : reg) (sp - 112) X2. regval HR1 (10%bv : reg) (ds + 168) X10.
      regval HR1 (11%bv : reg) 0 X11. regval HR1 (12%bv : reg) 80 X12.
      regval HR1 (8%bv : reg) (ds + 160) X8. regval HR1 (9%bv : reg) ds X9.
      regval HR1 (3%bv : reg) 67584 X3. regval HR1 (4%bv : reg) 1050296 X4.
      regval HR1 (18%bv : reg) (err mod 2 ^ 64) X18. regval HR1 (19%bv : reg) pstr1 X19. regval HR1 (20%bv : reg) pcons X20.
      regval HR1 (21%bv : reg) ppos X21. regval HR1 (22%bv : reg) (ds + 8) X22. regval HR1 (23%bv : reg) (ds + 112) X23.
      regval HR1 (24%bv : reg) 0xea9a8 X24. regval HR1 (25%bv : reg) 0xea9e8 X25.
      assert (ST1 : stores_in (fun a => zwin (sp - 112) sp a \/ zwin ds (ds + 8) a \/ zwin (ds + 112) (ds + 168) a) M M1) by (clear - M1 Hds_sp Hds_hi Hceil HS Hcv Hsphi Hretr HMS; subst M1; stores_tower).
      assert (HDstk : mdef M (sp - S) S).
      { eapply store_ok_mdef_offimg; [exact HROOM | lia | lia | lia | intros x Hx; apply ly_noseg; lia]. }

      destruct (s1_memset M1 (Z_to_bv 64 (ds + 168)) (Z_to_bv 64 0) (Z_to_bv 64 PC_RET_MEMSET) 80 (seg_rom SEGS) R1
                  ltac:(lia) ltac:(rewrite u64_of_Z by lia; lia)
                  ltac:(eapply (mdef_store_ok_off SEGS M1 ds 392 168); [eapply stores_in_mdef; [exact ST1 | exact HDds] | lia | lia | lia | lia])
                  ltac:(apply bv_eq; vm_compute; reflexivity) X10 X11 X12 X1)
        as (R2 & Hms2 & Y10 & AG).
      replace s1_memset_entry with (Z_to_bv 64 A_MEMSET) in Hms2 by (apply bv_eq; vm_compute; reflexivity).
      eapply srz_msteps; [exact (ms_halt _ MS) | exact (ms_lazy _ MS) | exact Hms2 |]. clear Hms2.
      set (M2 := wbytes M1 (Z_to_bv 64 (ds + 168)) (repeat (cbyte (Z_to_bv 64 0)) (Z.to_nat 80))).
      assert (Y : forall r, ~ In r ms_clob -> getr R2 r = getr R1 r) by (intros r Hr; exact (AG r Hr)).
      assert (Y2 : getr R2 2%bv = Z_to_bv 64 (sp - 112)) by (rewrite Y by ninl; exact X2).
      assert (Y8 : getr R2 8%bv = Z_to_bv 64 (ds + 160)) by (rewrite Y by ninl; exact X8).
      assert (Y9 : getr R2 9%bv = Z_to_bv 64 ds) by (rewrite Y by ninl; exact X9).
      assert (ST2 : stores_in (fun a => zwin (sp - 112) sp a \/ zwin ds (ds + 8) a \/ zwin (ds + 112) (ds + 248) a) M M2).
      { subst M2. eapply stores_in_wbytes_more; [eapply stores_in_weaken; [exact ST1 | intros a Ha; unfold zwin in *; lia] | lia | rewrite repeat_length; lia |].
        intros x Hx. rewrite repeat_length in Hx. unfold zwin. lia. }
      assert (PINS2 : pins D_DIAG M2).
      { eapply (pins_agree_low D_DIAG M M2 0x7fff7f800000 PINS); [vm_compute; reflexivity | lia |].
        intros a Ha. apply (proj1 ST2). rewrite u64_of_Z by lia. unfold zwin. lia. }

      assert (Y10' : getr R2 10%bv = Z_to_bv 64 (ds + 168)) by exact Y10.
      set (E2 := Eseed R2 [Z_to_bv 64 pstr2]).
      assert (Y22 : getr R2 22%bv = Z_to_bv 64 (ds + 8)) by (rewrite Y by ninl; exact X22).
      assert (Y3 : getr R2 3%bv = Z_to_bv 64 67584) by (rewrite Y by ninl; exact X3).
      assert (Y4 : getr R2 4%bv = Z_to_bv 64 1050296) by (rewrite Y by ninl; exact X4).
      assert (Y18 : getr R2 18%bv = Z_to_bv 64 (err mod 2 ^ 64)) by (rewrite Y by ninl; exact X18).
      assert (Y19 : getr R2 19%bv = Z_to_bv 64 pstr1) by (rewrite Y by ninl; exact X19).
      assert (Y20 : getr R2 20%bv = Z_to_bv 64 pcons) by (rewrite Y by ninl; exact X20).
      assert (Y21 : getr R2 21%bv = Z_to_bv 64 ppos) by (rewrite Y by ninl; exact X21).
      assert (Y24 : getr R2 24%bv = Z_to_bv 64 0xea9a8) by (rewrite Y by ninl; exact X24).
      assert (Y25 : getr R2 25%bv = Z_to_bv 64 0xea9e8) by (rewrite Y by ninl; exact X25).
      assert (Y23 : getr R2 23%bv = Z_to_bv 64 (ds + 112)) by (rewrite Y by ninl; exact X23).
      assert (HR2 : regs_ok E2 (srs sr_id [(8%bv : reg, EAlu ALU_ADD (EVar 9) (ELit 160)); (10%bv : reg, EAlu ALU_ADD (EVar 9) (ELit 168));
                                           (22%bv : reg, EAlu ALU_ADD (EVar 9) (ELit 8)); (23%bv : reg, EAlu ALU_ADD (EVar 9) (ELit 112))]) R2).
      { apply regs_ok_srs; [apply regs_ok_seed|]. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
          (split; [intros E0; discriminate E0 | evs; regsub]); rewrite alu_Z by lia; cbn [zar]; rewrite Z.mod_small by lia; reflexivity. }
      assert (SL8 : fld SEGS M2 (sp - 112 + 8) 8 0x68bc8) by (clear - M1 M2 Hds_sp Hds_hi Hceil HS Hcv Hsphi Hretr HMS; unfold fld; subst M2 M1; peel).
      assert (SL0 : fld SEGS M2 (sp - 112) 8 pstr2) by (clear - M1 M2 Hds_sp Hds_hi Hceil HS Hcv Hsphi Hretr HMS; unfold fld; subst M2 M1; peel).
      assert (HK2 : know_ok SEGS E2 M2
        [KWord (SA (EVar 2) 8) (N.to_nat 8) (ELit 0x68bc8); KWord (SA (EVar 2) 0) (N.to_nat 8) (EVar 32);
         KWr (SA (EVar 2) (-96)) (ELit 208); KWr (SA (EVar 9) 0) (ELit 392);
         KRange (EVar 2) (2 ^ 40) (2 ^ 47); KRange (EVar 9) (2 ^ 40) (2 ^ 47 - 392);
         KDisj (SA (EVar 9) 0) (ELit 392) (SA (EVar 2) (-96)) (ELit 208);
         KImg 0xe6000 0xee000;
         KWord (SA (ELit 0) GLOBAL_GUARD) (N.to_nat 1) (ELit 1);
         KWord (SA (ELit 0) GLOBAL_LOC) (N.to_nat 8) (ELit LOC_IMP)]).
      { repeat apply Forall_cons; try apply Forall_nil.
        - kwe SL8 Y2.
        - kwe SL0 Y2.
        - eapply (kwr_of_mdef _ _ _ _ (sp - 112) (-96) 208); [evs; exact Y2 | lia | lia | lia | lia |].
          eapply stores_in_mdef; [exact ST2|]. eapply mdef_sub; [exact HDstk | lia | lia].
        - eapply (kwr_of_mdef _ _ _ _ ds 0 392); [evs; exact Y9 | lia | lia | lia | lia | replace (ds + 0) with ds by lia]. eapply stores_in_mdef; [exact ST2 | exact HDds].
        - krv Y2. - krv Y9.
        - kdj ds 392 (sp - 112) 208. lia.
        - apply kimg_of_clear; [lia | lia |]. intros a Ha. rewrite (proj1 ST2 (Z_to_bv 64 a)) by (rewrite u64_of_Z by lia; unfold zwin; lia).
          apply (sx_relro ST s M a SXI). exists 0xe6000, 0xee000. split; [left; reflexivity | lia].
        - unfold GLOBAL_GUARD. kabs PINS2.
        - unfold GLOBAL_LOC. kabs PINS2. }
      xruns HR2 HK2 FUEL [A_STR_RESIZE] (SCR [] [] []) 60%N.
      { scs_auto. }
      clear HK2. rename HR' into HR3. rename R' into R3. wnorm_goal.
      lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?mm _) _) _ => set (M3 := mm) end.
      regval HR3 (1%bv : reg) PC_RET_RESIZE Z1. regval HR3 (2%bv : reg) (sp - 128) Z2. regval HR3 (10%bv : reg) (ds + 72) Z10.
      regval HR3 (11%bv : reg) 22 Z11. regval HR3 (12%bv : reg) 0 Z12.
      regval HR3 (8%bv : reg) (ds + 8) Z8. regval HR3 (9%bv : reg) (ds + 73) Z9. regval HR3 (18%bv : reg) 0 Z18.
      regval HR3 (3%bv : reg) 67584 Z3. regval HR3 (4%bv : reg) 1050296 Z4.
      regval HR3 (19%bv : reg) pstr1 Z19. regval HR3 (20%bv : reg) pcons Z20. regval HR3 (21%bv : reg) ppos Z21.
      assert (ST3 : stores_in (fun a => zwin (sp - 128) sp a \/ zwin ds (ds + 264) a) M M3) by (clear - M1 M2 M3 Hds_sp Hds_hi Hceil HS Hcv Hsphi Hretr HMS; subst M3 M2 M1; stores_tower).
      assert (HDd3 : mdef M3 ds 392) by (eapply stores_in_mdef; [exact ST3 | exact HDds]).
      assert (Fhdr : fld SEGS M3 (ds + 72) 8 0) by (clear - M1 M2 M3 Hds_sp Hds_hi Hceil HS Hcv Hsphi Hretr HMS; unfold fld; subst M3; peel).
      assert (STR3 : str_rep MI A M3 (ds + 72) SShort []).
      { unfold str_rep. cbn [str_cap str_data]. replace (Zlen (@nil Z)) with 0 by reflexivity.
        split; [lia|]. split; [lia|]. split; [eapply mdef_sub; [exact HDd3 | lia | lia]|]. split; [unfold SSO_CAP; lia|].
        split; [exact (fld8_byte0' M3 (ds + 72) 0 Fhdr)|]. split; [intros i Hi; lia|].
        rewrite Z.add_0_r. apply fld8_zero_b1; [lia | lia | exact Fhdr]. }

      pose proof (str_resize_8b820_spec MI) as RS. unfold str_resize_stmt in RS. cbn [sc_resize sc_resize_stack c8b3ec] in RS. lazy zeta in RS.
      destruct (RS fx A M3 R3 (sp - 128) PC_RET_RESIZE (ds + 72) 22 0 SShort [] STR3 ltac:(cbn [str_cap]; unfold SSO_CAP; lia)
                  ltac:(cbn [str_data str_cap]; unfold SSO_CAP; eapply mdef_sub; [exact HDd3 | lia | lia])
                  ltac:(cbn [str_data str_cap]; unfold SSO_CAP; intros a Ha; unfold zwin in *; lia)
                  ltac:(unfold stack_room; eapply stores_in_store_ok; [exact ST3|];
                        replace (Z_to_bv 64 (sp - 128 - 80)) with (Z_to_bv 64 (sp - S + (S - 208))) by (f_equal; lia);
                        apply (mdef_store_ok_off SEGS M (sp - S) S); [exact HDstk | lia | lia | lia | lia])
                  ltac:(lia) ltac:(lia) ltac:(apply bv_eq; vm_compute; reflexivity) Z1 Z2 Z10 Z11 Z12)
        as (R4 & M4 & MS4 & KP4 & STR4 & FR4 & DM4). clear RS.
      eapply srz_msteps; [exact (ms_halt _ MS) | exact (ms_lazy _ MS) | exact MS4 |]. clear MS4.
      cbn [str_data str_cap] in FR4. unfold SSO_CAP in FR4.
      assert (ST4 : stores_in (fun a => zwin (sp - 208) sp a \/ zwin ds (ds + 264) a) M M4).
      { eapply stores_in_trans; [eapply stores_in_weaken; [exact ST3 | intros a Ha; unfold zwin in *; lia]|].
        split; [|exact DM4]. intros a Ha. apply FR4. unfold zwin in *. lia. }
      assert (AG34 : forall lo hi, (hi <= ds + 72 \/ ds + 96 <= lo) -> (hi <= sp - 208 \/ sp - 128 <= lo) -> 0 <= lo -> hi <= 2 ^ 64 ->
                    agree_on (zwin lo hi) M3 M4).
      { intros lo hi H1 H2 H3 H4 a Ha. apply FR4. rewrite u64_of_Z by (unfold zwin in Ha; lia). unfold zwin in *. lia. }

      assert (Hpc : 0 <= pcons /\ (pcons + 48 <= sp - S \/ sp <= pcons)).
      { destruct PLc as [Hhi|(q & k & HIn & Hq & Hk)].
        - split; [lia|]. destruct (Z.lt_ge_cases pcons sp); [left|right; lia].
          destruct (Z.lt_ge_cases (pcons + 48) (sp - S + 1)); [lia|]. exfalso.
          destruct (Z.lt_ge_cases pcons (sp - S)).
          + apply (DJc (sp - S)); unfold zwin; lia.
          + apply (DJc pcons); unfold zwin; lia.
        - pose proof (live_range _ _ MI A M model q k AI HIn). lia. }

      assert (TA : forall a (k : nat) v, (forall x, a <= x < a + Z.of_nat k -> ~ (sp - 208 <= x < sp) /\ ~ (ds <= x < ds + 264)) -> 0 <= a -> a + Z.of_nat k < 2 ^ 64 ->
                  fld SEGS M a k v -> fld SEGS M4 a k v).
      { intros a k v Hx Ha Hk HF. eapply fld_agree; [lia | lia | exact HF |]. eapply stores_in_agree; [exact ST4|]. intros x Hx0. unfold zwin in *.
        destruct (Hx x Hx0). lia. }
      assert (OBJ : forall o, (o = ppos \/ o = pstr1 \/ o = pstr2) -> forall off, 0 <= off <= 16 ->
                   exists v, cellw SEGS M4 (o + off) 8 v).
      { intros o Ho off Hoff.
        assert (Hob : sp <= o /\ o + 24 <= 2 ^ 47 /\ mdef M o 24 /\ forall x, ds <= x < ds + 392 -> ~ (o <= x < o + 24)).
        { destruct Ho as [->|[->| ->]]; (split; [assumption|]; split; [assumption|]; split; [assumption|]);
            intros x Hx; pose proof (DISJ x ltac:(unfold zwin; lia)) as (D1 & D2 & D3 & D4); unfold zwin in *; tauto. }
        destruct Hob as (Ho1 & Ho2 & Ho3 & Ho4).
        destruct (cellw_of_bytes M (o + off) ltac:(lia) ltac:(lia)) as (v & [Rv Cv]).
        { apply (rdn_of_mdef_hi M (o + off) 8); [intros i Hi; replace (o + off + i) with (o + (off + i)) by lia; apply Ho3; lia | lia | cbn; lia]. }
        exists v. split; [exact Rv|]. apply TA; [intros x Hx; split; [lia | intros Hd; exact (Ho4 x ltac:(lia) ltac:(cbn in Hx; lia))] | lia | cbn; lia | exact Cv]. }
      destruct (OBJ ppos ltac:(left; reflexivity) 0 ltac:(lia)) as (vp0 & Cp0). rewrite Z.add_0_r in Cp0.
      destruct (OBJ ppos ltac:(left; reflexivity) 8 ltac:(lia)) as (vp1 & Cp1).
      destruct (OBJ ppos ltac:(left; reflexivity) 16 ltac:(lia)) as (vp2 & Cp2).
      destruct (OBJ pstr1 ltac:(right; left; reflexivity) 0 ltac:(lia)) as (v10 & C10). rewrite Z.add_0_r in C10.
      destruct (OBJ pstr1 ltac:(right; left; reflexivity) 8 ltac:(lia)) as (v11 & C11).
      destruct (OBJ pstr1 ltac:(right; left; reflexivity) 16 ltac:(lia)) as (v12 & C12).
      destruct (OBJ pstr2 ltac:(right; right; reflexivity) 0 ltac:(lia)) as (v20 & C20). rewrite Z.add_0_r in C20.
      destruct (OBJ pstr2 ltac:(right; right; reflexivity) 8 ltac:(lia)) as (v21 & C21).
      destruct (OBJ pstr2 ltac:(right; right; reflexivity) 16 ltac:(lia)) as (v22 & C22).

      assert (T34 : forall a (k : nat) v, (a + Z.of_nat k <= ds + 72 \/ ds + 96 <= a) -> (a + Z.of_nat k <= sp - 208 \/ sp - 128 <= a) -> 0 <= a -> a + Z.of_nat k < 2 ^ 64 ->
                   fld SEGS M3 a k v -> fld SEGS M4 a k v).
      { intros a k v H1 H2 H3 H4 HF. eapply fld_agree; [lia | lia | exact HF | apply AG34; lia]. }

      set (W13 := fun a => zwin (sp - 128) (sp - 96) a \/ zwin ds (ds + 120) a \/ zwin (ds + 160) (ds + 264) a).
      assert (ST13 : stores_in W13 M1 M3) by (clear - M1 M2 M3 W13 Hds_sp Hds_hi Hceil HS Hcv Hsphi Hretr HMS; subst M3 M2 W13; stores_tower).
      assert (T13 : forall a (k : nat) v, (forall x, a <= x < a + Z.of_nat k -> ~ W13 x) -> 0 <= a -> a + Z.of_nat k < 2 ^ 64 -> fld SEGS M1 a k v -> fld SEGS M3 a k v).
      { intros a k v Hx Ha Hk HF. eapply fld_agree; [lia | lia | exact HF |]. eapply stores_in_agree; [exact ST13|]. intros x Hx0. split; [unfold zwin in Hx0; lia | apply Hx; unfold zwin in Hx0; lia]. }
      assert (SL1 : slots SEGS M1 sp (SVC R ret)) by (clear - M1 Hds_sp Hds_hi Hceil HS Hcv Hsphi Hretr HMS; unfold SVC; subst M1; slots_tower).
      assert (SL3 : slots SEGS M3 sp (SVC R ret)).
      { eapply slots_agree; [exact SL1 | cbn; lia | lia | cbn [length SVC Z.of_nat Pos.of_succ_nat Pos.succ Pos.mul Z.mul]].
        eapply stores_in_agree; [exact ST13|]. intros x Hx. subst W13. unfold zwin in *. cbn beta. lia. }
      apply (ctor_tail MI ST DN A s R M model sp ret ds ppos pcons pstr1 err pstr2 K S CB HS Herr
               (conj (conj Hds_sp (conj Hds_hi Hds_own)) (conj Hal HDds)) (conj (conj Hp_sp (conj Hp_hi Hp_own)) HDp)
               (conj (conj H1_sp (conj H1_hi H1_own)) (conj F1z HD1)) (conj (conj H2_sp (conj H2_hi H2_own)) (conj F2z HD2))
               (conj (conj PLc DJc) Fcf) Hpc_hi DISJ CONT R4 M4 vp0 vp1 vp2 v10 v11 v12 v20 v21 v22).
      constructor.
      - exact ST4.
      - rewrite (KP4 2%bv) by inl. exact Z2. - rewrite (KP4 3%bv) by inl. exact Z3. - rewrite (KP4 4%bv) by inl. exact Z4.
      - rewrite (KP4 8%bv) by inl. exact Z8. - rewrite (KP4 9%bv) by inl. exact Z9. - rewrite (KP4 18%bv) by inl. exact Z18.
      - rewrite (KP4 19%bv) by inl. exact Z19. - rewrite (KP4 20%bv) by inl. exact Z20. - rewrite (KP4 21%bv) by inl. exact Z21.
      - intros r Hr. cbn in Hr. repeat (destruct Hr as [<-|Hr]; [kept_chain KP4 HR3 Y HR1|]). destruct Hr.
      - apply T34; [lia | lia | lia | cbn; lia |]. clear - M1 M2 M3 Hds_sp Hds_hi Hceil HS Hcv Hsphi Hretr HMS. unfold fld. subst M3. peel.
      - apply T34; [lia | lia | lia | cbn; lia |]. clear - M1 M2 M3 Hds_sp Hds_hi Hceil HS Hcv Hsphi Hretr HMS. unfold fld. subst M3. peel.
      - apply T34; [lia | lia | lia | cbn; lia |]. clear - M1 M2 M3 Hds_sp Hds_hi Hceil HS Hcv Hsphi Hretr HMS. unfold fld. subst M3. peel.
      - apply T34; [lia | lia | lia | cbn; lia |]. clear - M1 M2 M3 Hds_sp Hds_hi Hceil HS Hcv Hsphi Hretr HMS. unfold fld. subst M3. peel.
      - eapply slots_agree; [exact SL3 | cbn; lia | lia | cbn [length SVC Z.of_nat Pos.of_succ_nat Pos.succ Pos.mul Z.mul]; apply AG34; lia].
      - eapply stores_in_mdef; [exact ST4 | exact HDds].
      - apply T34; [cbn; lia | lia | lia | cbn; lia |]. clear - M1 M2 M3 Hds_sp Hds_hi Hceil HS Hcv Hsphi Hretr HMS. unfold fld, VT_OS. subst M3. peel.
      - apply T34; [cbn; lia | lia | lia | cbn; lia |]. clear - M1 M2 M3 Hds_sp Hds_hi Hceil HS Hcv Hsphi Hretr HMS. unfold fld, VT_SB. subst M3. peel.
      - apply T34; [cbn; lia | lia | lia | cbn; lia |]. clear - M1 M2 M3 Hds_sp Hds_hi Hceil HS Hcv Hsphi Hretr HMS. unfold fld, LOC_IMP. subst M3. peel.
      - apply T34; [cbn; lia | lia | lia | cbn; lia |]. clear - M1 M2 M3 Hds_sp Hds_hi Hceil HS Hcv Hsphi Hretr HMS. unfold fld. subst M3. peel.
      - apply T34; [cbn; lia | lia | lia | cbn; lia |]. clear - M1 M2 M3 Hds_sp Hds_hi Hceil HS Hcv Hsphi Hretr HMS. unfold fld. subst M3. peel.
      - apply T34; [cbn; lia | lia | lia | cbn; lia |]. clear - M1 M2 M3 Hds_sp Hds_hi Hceil HS Hcv Hsphi Hretr HMS. unfold fld. subst M3. peel.
      - replace (repeat 0 22) with (sresize_cs [] 22 0) by reflexivity. exact STR4.
      - apply T34; [cbn; lia | lia | lia | cbn; lia |]. clear - M1 M2 M3 Hds_sp Hds_hi Hceil HS Hcv Hsphi Hretr HMS. unfold fld. subst M3. peel.
      - apply T34; [cbn; lia | lia | lia | cbn; lia |]. clear - M1 M2 M3 Hds_sp Hds_hi Hceil HS Hcv Hsphi Hretr HMS. unfold fld. subst M3. peel.
      - apply T34; [cbn; lia | lia | lia | cbn; lia |]. clear - M1 M2 M3 Hds_sp Hds_hi Hceil HS Hcv Hsphi Hretr HMS. unfold fld, VT_IOS. subst M3. peel.
      - apply T34; [cbn; lia | lia | lia | cbn; lia |]. apply T13; [intros x Hx; subst W13; unfold zwin; cbn in Hx; lia | lia | cbn; lia|].
        clear - M1 M2 M3 Hds_sp Hds_hi Hceil HS Hcv Hsphi Hretr HMS. unfold fld, DS_FL0. subst M1. peel.
      - apply T34; [cbn; lia | lia | lia | cbn; lia |]. apply T13; [intros x Hx; subst W13; unfold zwin; cbn in Hx; lia | lia | cbn; lia|]. clear - M1 M2 M3 Hds_sp Hds_hi Hceil HS Hcv Hsphi Hretr HMS. unfold fld. subst M1. peel.
      - apply T34; [cbn; lia | lia | lia | cbn; lia |]. apply T13; [intros x Hx; subst W13; unfold zwin; cbn in Hx; lia | lia | cbn; lia|]. clear - M1 M2 M3 Hds_sp Hds_hi Hceil HS Hcv Hsphi Hretr HMS. unfold fld. subst M1. peel.
      - apply T34; [cbn; lia | lia | lia | cbn; lia |]. apply T13; [intros x Hx; subst W13; unfold zwin; cbn in Hx; lia | lia | cbn; lia|].
        clear - M1 M2 M3 Hds_sp Hds_hi Hceil HS Hcv Hsphi Hretr HMS. unfold fld. subst M1. peel.
      - apply T34; [cbn; lia | lia | lia | cbn; lia |]. apply T13; [intros x Hx; subst W13; unfold zwin; cbn in Hx; lia | lia | cbn; lia|].
        clear - M1 M2 M3 Hds_sp Hds_hi Hceil HS Hcv Hsphi Hretr HMS. unfold fld. subst M1. peel.
      - apply T34; [cbn; lia | lia | lia | cbn; lia |]. apply T13; [intros x Hx; subst W13; unfold zwin; cbn in Hx; lia | lia | cbn; lia|]. clear - M1 M2 M3 Hds_sp Hds_hi Hceil HS Hcv Hsphi Hretr HMS. unfold fld. subst M1. peel.
      - apply T34; [cbn; lia | lia | lia | cbn; lia |]. clear - M1 M2 M3 Hds_sp Hds_hi Hceil HS Hcv Hsphi Hretr HMS. unfold fld, LOC_IMP. subst M3. peel.
      - intros i Hi. apply T34; [cbn; lia | lia | lia | cbn; lia |]. clear - M1 M2 M3 Hds_sp Hds_hi Hceil HS Hcv Hsphi Hretr HMS Hi. unfold fld. subst M3 M2. peel.
        replace (ds + 168 + 8 * i) with (ds + 168 + (8 * i)) by lia. apply fld8_zero_of_repeat; cbn [Z.of_nat Z.to_nat Pos.to_nat]; lia.
      - apply T34; [cbn; lia | lia | lia | cbn; lia |]. clear - M1 M2 M3 Hds_sp Hds_hi Hceil HS Hcv Hsphi Hretr HMS. unfold fld. subst M3. peel.
      - apply T34; [cbn; lia | lia | lia | cbn; lia |].
        pose proof (fld4_of_bytes M3 (ds + 256) 255 255 255 255 (2 ^ 32 - 1) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as FB.
        apply FB; [ | | | | vm_compute; reflexivity]; clear - M1 M2 M3 Hds_sp Hds_hi Hceil HS Hcv Hsphi Hretr HMS;
          unfold fld; subst M3; peel;
          lazymatch goal with |- rdn _ (wbytes _ (Z_to_bv 64 ?b) _) (Z_to_bv 64 ?a) _ = _ => replace (Z_to_bv 64 a) with (Z_to_bv 64 b) by (f_equal; lia) end;
          rewrite (w2lb_mod 1 18446744073709551615), (w2lb_mod 1 255) by lia;
          apply ContLib.rdn_wbytes_hit1; rewrite u64_of_Z by lia; lia.
      - exact Cp0. - exact Cp1. - exact Cp2.
      - apply TA; [intros x Hx; cbn in Hx; split; [lia | intros Hd; exact (proj2 (proj2 (proj2 (DISJ x ltac:(unfold zwin; lia)))) ltac:(unfold zwin; lia))] | lia | cbn; lia | exact Fcf].
      - apply TA; [intros x Hx; cbn in Hx; split; [lia | intros Hd; exact (proj1 (proj2 (DISJ x ltac:(unfold zwin; lia))) ltac:(unfold zwin; lia))] | lia | cbn; lia | exact F1z].
      - exact C10. - exact C11. - exact C12.
      - apply TA; [intros x Hx; cbn in Hx; split; [lia | intros Hd; exact (proj1 (proj2 (proj2 (DISJ x ltac:(unfold zwin; lia)))) ltac:(unfold zwin; lia))] | lia | cbn; lia | exact F2z].
      - exact C20. - exact C21. - exact C22.
    Qed.
  End Call.

  Theorem ds_ctor : ds_ctor_stmt SEGS Ly.L MI ST dcS1 (ds_rep MI).
  Proof using AC RRND MI ST DN.
    intros fx A s R M model sp ret ds ppos pcons pstr1 err pstr2 K CB ROC Ha0 Ha1 Ha2 Ha3 Ha4 Ha5 Herr ABOVE Hal HD Hp HDp H1a F1 HD1 H2a F2 HD2 OBJ Hpc F32 DISJ ROOM CONT.
    cbn [dc_stack dc_ctor dcS1] in *. unfold DS_SIZE in *.
    exact (ctor_main A s R M model sp ret ds ppos pcons pstr1 err pstr2 K 12288 CB ltac:(lia) Ha0 Ha1 Ha2 Ha3 Ha4 Ha5 Herr
             (conj ABOVE (conj Hal HD)) (conj Hp HDp) (conj H1a (conj F1 HD1)) (conj H2a (conj F2 HD2)) (conj OBJ F32) Hpc DISJ CONT).
  Qed.
End DsCtor.
