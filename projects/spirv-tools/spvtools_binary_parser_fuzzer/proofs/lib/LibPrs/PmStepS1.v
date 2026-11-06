(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require list.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac WalkTac StartupTac SumWalkTac StoreOk MemSplit Hoare ShapeAlg
  SRealizes RefMemcpyLib RefReadLib FPSteps LibIface LibBudget LibEff MmapSim LibMaskBits
  ZStores SymExec3 SymExec3Sound SymRun3 S1Layout.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContLib StrLib LiveStats ContStmts S1Facts.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts HCommon HLib HConstsS1.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsNeeds PrsInv PrsStmts PmBase PmHyps PmCoreS1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Abbreviation SEGS := Plain.M.loaded_segments.

Module Ly := S1Layout.

Section PM.
Context {AC : AllocCeiling}.
  Context {MI : MallocIface SEGS Ly.L} {ST : StaticsIface SEGS Ly.L}.
  Context {G : grammar} {idesc : Z -> Z -> Prop} {odesc edesc : Z -> Z -> Z -> Prop}
          {generates_type is_ext_inst is_nonsemantic : Z -> bool}
          {ds_rep : AS MI -> mem -> Z -> Z -> Z -> list (Z * Z) -> Prop}.
  Variable CL : pm_callees SEGS Ly.L MI ST G tcS1 dcS1 nfcS1 HConstsS1.hc ccS1 kcS1
                  idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep.

  #[local] Notation PMX := (PmBase.PMX MI ST).
  #[local] Notation cfg fx R pc M model := (mkCfg (@mkst fx R (Z_to_bv 64 pc) M (seg_rom SEGS)) model).

  #[local] Notation pm_exit := (PmCoreS1.pm_exit MI ST).
  #[local] Notation POSTK := (PmCoreS1.POSTK MI ST).
  #[local] Notation pmx_throughS := (pmx_through SEGS Ly.L MI ST ly_img_low ly_rw_img ly_relro_img ly_errno_img ly_rw_not_relro ly_errno_rw).
  #[local] Notation pmx_dsS := (pmx_ds SEGS Ly.L MI ST ly_img_low ly_rw_img ly_relro_img ly_errno_img ly_rw_not_relro ly_errno_rw).
  Let HCL := cl_classes _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL.
  #[local] Notation pmx_roomS := (pmx_room SEGS Ly.L MI ST (proj1 HCL) (proj1 (proj2 HCL)) (proj2 (proj2 HCL)) (cl_RB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL)).
  #[local] Notation pmx_room3S := (pmx_room3 SEGS Ly.L MI ST (proj1 HCL) (proj1 (proj2 HCL)) (proj2 (proj2 HCL)) (cl_RB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL)).

  Record PMS (w : pmw MI ST) (c0 : parserC) (K : TSet) : Prop := MKPMS {
    ps_L0   : Permutation (live MI (w_A0 w)) (w_L0 w ++ state_blocks (pc_state c0));
    ps_budS : forall cls, 4 <= cls -> count_class_f (size_class MI) (BIG MI) (w_L0 w) cls + PM_SMALL_SLACK <= CAP_SMALL;
    ps_budN : forall cls, 0 <= cls < 4 -> count_class_f (size_class MI) (BIG MI) (w_L0 w) cls + PM_NODES (w_n w) + PM_SMALL_SLACK <= CAP_NODE;
    ps_budB : big_bytes_f (round_big MI) (BIG MI) (w_L0 w) + PM_BIG (w_n w) <= LIB_BIGCAP;
    ps_diag : 0 <= w_diag w < 2 ^ 64;
    ps_post : POSTK w c0 K;
    ps_ret  : ret_ok (Z_to_bv 64 (w_ret w));
    ps_R0ra : getr (w_R0 w) 1%bv = Z_to_bv 64 (w_ret w);
    ps_R0sp : getr (w_R0 w) 2%bv = Z_to_bv 64 (w_sp0 w);
    ps_gp   : getr (w_R0 w) 3%bv = Z_to_bv 64 (ly_gp Ly.L);
    ps_tp   : getr (w_R0 w) 4%bv = Z_to_bv 64 (ly_tp Ly.L);
    ps_cls  : size_class MI 24 <= 2 /\ (size_class MI 32 <= 2 /\ size_class MI 24 <> size_class MI 32) /\ 4096 <= BIG MI
  }.
  Ltac postrun := evs; rewrite ?v_addi_Z by lia; rewrite ?Z.add_0_r, ?Z.add_opp_r.

  Lemma pmx_ds_room : forall (w : pmw MI ST) c0 K A M model c,
    PMS w c0 K -> PMX w A M model c -> pm_bud (w_n w) c -> ds_room SEGS Ly.L MI A.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K A M model c PS X B. split.
    { pose proof (x_caps X) as (_ & _ & HN). unfold DS_MAXBLK, LIB_NMAX in *. lia. }
    intros n Hn. unfold DS_MAXBLK in Hn.
    eapply pmx_roomS; [exact X | exact B | exact (ps_budS _ _ _ PS) | exact (ps_budN _ _ _ PS) | exact (ps_budB _ _ _ PS) | lia].
  Qed.

  Lemma pm_tail_68410 : forall (w : pmw MI ST) c0 K (fx : FPState) A M model c R (err len : Z) (B : list (Z * Z)),
    PMS w c0 K -> PMX w A M model c -> c_tr c = B -> pm_bud (w_n w) c ->
    ds_rep A M (w_sp w + 272) err len B -> - 2 ^ 31 <= err < 0 ->
    frm_zero (@fp_csr fx) ->
    getr R 2%bv = Z_to_bv 64 (w_sp w) -> getr R 3%bv = Z_to_bv 64 (ly_gp Ly.L) -> getr R 4%bv = Z_to_bv 64 (ly_tp Ly.L) ->
    srealizes SEGS (cfg fx R 0x684b4 M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx A M model c R err len B PS X Htr B_ DS Herr FZ Hsp Hgp Htp.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & Gc2 & Gap & Gn & Gw). unfold w_sp0, PM_FRAME in *.
    pose proof (cl_ds_laws _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL) as DL.
    pose proof (dl_err _ _ _ _ _ _ DL _ _ _ _ _ _ DS) as Herrc. pose proof (dl_blocks _ _ _ _ _ _ DL _ _ _ _ _ _ DS) as [HBlen HBin].
    pose proof (dl_def _ _ _ _ _ _ DL _ _ _ _ _ _ DS) as (Hdsdef & _ & _ & _).
    unfold CRep.fld in Herrc.
    assert (Cerr : cell4 SEGS M (w_sp w + 272 + 360) (err mod 2 ^ 32)).
    { split; [pose proof (Z.mod_pos_bound err (2 ^ 32)); cbn; lia | exact Herrc]. }
    pose (E := Eseed R [Z_to_bv 64 (w_sp w); sxw (err mod 2 ^ 32)]).
    assert (HR : regs_ok E (srs sr_id [(2%bv, EVar 32)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros XX; discriminate XX); evs; assumption. }
    assert (HK : know_ok SEGS E M [KRange (EVar 32) (2 ^ 24) (2 ^ 47)]).
    { repeat apply Forall_cons; try apply Forall_nil. eapply krange_var; [evs; reflexivity | lia | lia]. }
    xruns HR HK 100%nat STOPS (SCR [] [EVar 33] []) 50%N.
    { split_scs. sc_rd_sx Cerr. }
    rreg HR' (10%bv) G10. rreg HR' (1%bv) G1. rreg HR' (2%bv) G2. rreg HR' (3%bv) G3. rreg HR' (4%bv) G4.
    eapply (cl_ds_dtor _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL fx A (w_s w) R' M model (w_sp w) 0x684c0 (w_sp w + 272) err len B K).
    - eapply pmx_callB; [exact X | | cbn [dc_stack dcS1]; unfold PM_FRAME; lia]. constructor.
      + exact G1. + unfold ret_ok. apply bv_eq. vm_compute. reflexivity. + lia. + exact G2. + exact Gsp16. + lia. + rewrite G3; exact Hgp. + rewrite G4; exact Htp.
    - exact (x_roc X).
    - rewrite G10, w_add by lia. reflexivity.
    - exact DS.
    - eapply (pmx_above_sp_frame SEGS Ly.L MI ST ly_img_low ly_rw_img); [exact X | lia | unfold DS_SIZE, w_sp0, PM_FRAME; lia].
    -
      intros A' R2 M' model' RB XFER Hdef' EFF.
      destruct RB as [AI' MS' FS' FDS' SX' KEPT].
      assert (X' : PMX w A' M' model' (set_tr c [])).
      { eapply (pmx_dsS w A M model c A' M' model' (dc_stack dcS1) (w_sp w + 272) B [] [] (fun _ => False) (fun _ => False));
          [exact X | rewrite Htr, app_nil_r; reflexivity | exact AI' | exact MS' | exact FS' | exact FDS'
          | eapply eff_weaken; [exact EFF | intros a Ha; left; exact Ha] | cbn [dc_stack dcS1]; unfold PM_FRAME; lia | lia | unfold DS_SIZE, w_sp0, PM_FRAME; lia
          | intros a [] | intros a [] | exact Hdef' | exact XFER | exact HBlen | rewrite Zlength_nil; lia]. }
      rreg HR' (26%bv) G26.
      eapply (pm_exit w c0 K fx A' M' model' (set_tr c []) R2 (getr R2 26%bv)); try (exact X'); try reflexivity.
      + destruct B_ as (_ & _ & _ & _ & Bv1 & Bv2 & Bv3 & _). cbn [c_v1 set_tr]. unfold OPND_SZ in Bv1. lia.
      + destruct B_ as (_ & _ & _ & _ & Bv1 & Bv2 & Bv3 & _). cbn [c_v2 set_tr]. lia.
      + destruct B_ as (_ & _ & _ & _ & Bv1 & Bv2 & Bv3 & _). cbn [c_v3 set_tr]. lia.
      + exact (ps_diag _ _ _ PS).
      + intros b Hb. eapply (pm_bud_sizes SEGS Ly.L MI ST w A' M' model' (set_tr c [])); [exact X' | | exact Hb].
        destruct B_ as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9). repeat (split; [assumption|]). cbn [set_tr c_tr]. rewrite Zlength_nil. split; [lia|]. intros b' [].
      + intros cls. pose proof (x_geo X') as GEO'. destruct GEO' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Gn' & _).
        eapply (cnt_c_blocks SEGS Ly.L MI (proj1 (ps_cls _ _ _ PS)) (proj1 (proj2 (ps_cls _ _ _ PS))) (proj2 (proj2 (ps_cls _ _ _ PS)))); [| lia].
        destruct B_ as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9). repeat (split; [assumption|]). cbn [set_tr c_tr]. rewrite Zlength_nil. split; [lia|]. intros b' [].
      + exact (ps_L0 _ _ _ PS).
      + exact FZ.
      + exact (ps_post _ _ _ PS).
      + rewrite (KEPT 2%bv) by (first [solve [clear; cbv; tauto] | cbv; tauto]). rewrite G2. reflexivity.
      + rewrite (KEPT 3%bv) by (first [solve [clear; cbv; tauto] | cbv; tauto]). rewrite G3, (ps_gp _ _ _ PS). exact Hgp.
      + rewrite (KEPT 4%bv) by (first [solve [clear; cbv; tauto] | cbv; tauto]). rewrite G4, (ps_tp _ _ _ PS). exact Htp.
      + exact (ps_ret _ _ _ PS).
      + exact (ps_R0ra _ _ _ PS).
      + exact (ps_R0sp _ _ _ PS).
  Qed.

  Definition ro_byte (a : Z) : option Z :=
    match rdn SEGS (fun _ => None) (Z_to_bv 64 a) 1 with Some [b] => Some (bv_unsigned b) | _ => None end.
  Definition zseq (lo n : Z) : list Z := map (fun i => lo + Z.of_nat i) (seq 0 (Z.to_nat n)).
  Definition ro_cstr_chk (p n : Z) : bool :=
    (0x10008 <=? p) && (0 <=? n) && (p + n + 16 <=? 0xe6000) &&
    forallb (fun i => match ro_byte (p + i) with Some c => 0 <? c | None => false end) (zseq 0 n) &&
    (match ro_byte (p + n) with Some c => c =? 0 | None => false end) &&
    forallb (fun a => match ro_byte a with Some _ => true | None => false end)
            (zseq (p - p mod 8) (n + 1 + p mod 8 + (8 - (p + n + 1) mod 8) mod 8)).

  Lemma in_zseq : forall lo n a, 0 <= n -> lo <= a < lo + n -> In a (zseq lo n).
  Proof using.
    intros lo n a Hn Ha. unfold zseq. apply in_map_iff. exists (Z.to_nat (a - lo)). split; [lia|]. apply in_seq. lia.
  Qed.
  Lemma ro_byte_range : forall a c, ro_byte a = Some c -> 0 <= c < 256.
  Proof using.
    intros a c. unfold ro_byte. destruct (rdn _ _ _ _) as [[|b [|]]|]; intros E; try discriminate E.
    injection E as <-. pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. cbn in Hb. lia.
  Qed.
  Lemma ro_rdn1 : forall M (a : Z) (k : nat), ro_clear Ly.L M -> 0x10000 <= a -> a + Z.of_nat k <= 0xe6000 ->
    rdn SEGS M (Z_to_bv 64 a) k = rdn SEGS (fun _ => None) (Z_to_bv 64 a) k.
  Proof using.
    intros M a k ROC H1 H2. symmetry. apply rdn_agree_win; [lia|lia|]. intros x Hx. unfold zwin in Hx.
    symmetry. apply ROC. rewrite u64_of_Z by lia. unfold ro_addr. cbn [ly_img ly_rw ly_relro Ly.L]. rewrite !in_ranges_1. lia.
  Qed.
  Lemma ro_byte_fld : forall M a c, ro_clear Ly.L M -> 0x10000 <= a -> a + 1 <= 0xe6000 -> ro_byte a = Some c -> fld SEGS M a 1 c.
  Proof using.
    intros M a c ROC H1 H2. unfold ro_byte, CRep.fld. rewrite (ro_rdn1 M a 1 ROC H1 ltac:(cbn; lia)).
    destruct (rdn _ _ _ _) as [[|b [|]]|]; intros E; try discriminate E. injection E as <-.
    rewrite N_to_le_bytes_1_small. do 2 f_equal. apply bv_eq. pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. cbn in Hb.
    rewrite (u64_of_Z (bv_unsigned b)) by lia. rewrite Z_to_bv_unsigned. unfold bv_wrap. symmetry. apply Z.mod_small. exact (bv_unsigned_in_range 8 b).
  Qed.
  Lemma ro_cstr_of_chk : forall p n, ro_cstr_chk p n = true -> ro_cstr SEGS Ly.L p n.
  Proof using.
    intros p n H. unfold ro_cstr_chk in H. apply andb_prop in H. destruct H as [H H6]. apply andb_prop in H. destruct H as [H H5].
    apply andb_prop in H. destruct H as [H H4]. apply andb_prop in H. destruct H as [H H3]. apply andb_prop in H. destruct H as [H1 H2].
    apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3.
    pose proof (Z.mod_pos_bound p 8 ltac:(lia)) as Hm8. pose proof (Z.mod_pos_bound (p + n + 1) 8 ltac:(lia)) as Hm8'.
    pose proof (Z.mod_pos_bound (8 - (p + n + 1) mod 8) 8 ltac:(lia)) as Hm8''.
    split; [lia|]. split; [lia|]. split; [lia|]. intros M ROC. split; [|split].
    - intros i Hi. pose proof (proj1 (forallb_forall _ _) H4 i (in_zseq 0 n i ltac:(lia) ltac:(lia))) as Hc. cbn beta in Hc.
      destruct (ro_byte (p + i)) as [c|] eqn:E; [|discriminate Hc]. exists c. pose proof (ro_byte_range _ _ E). apply Z.ltb_lt in Hc.
      split; [lia|]. apply (ro_byte_fld M (p + i) c ROC); [lia|lia|exact E].
    - destruct (ro_byte (p + n)) as [c|] eqn:E; [|discriminate H5]. apply Z.eqb_eq in H5. subst c.
      apply (ro_byte_fld M (p + n) 0 ROC); [lia|lia|exact E].
    - intros a Ha. pose proof (proj1 (forallb_forall _ _) H6 a (in_zseq (p - p mod 8) (n + 1 + p mod 8 + (8 - (p + n + 1) mod 8) mod 8) a ltac:(lia) ltac:(lia))) as Hc. cbn beta in Hc.
      destruct (ro_byte a) as [c|] eqn:E; [|discriminate Hc]. exists c. pose proof (ro_byte_range _ _ E).
      split; [lia|]. apply (ro_byte_fld M a c ROC); [lia|lia|exact E].
  Qed.

  Definition cregs (w : pmw MI ST) (R : bvmap 5 word) (ret : Z) : Prop :=
    getr R 1%bv = Z_to_bv 64 ret /\ ret_ok (Z_to_bv 64 ret) /\ 0 <= ret < 2 ^ 64 /\
    getr R 2%bv = Z_to_bv 64 (w_sp w) /\ getr R 3%bv = Z_to_bv 64 (ly_gp Ly.L) /\ getr R 4%bv = Z_to_bv 64 (ly_tp Ly.L).

  Lemma pmx_cregs_callB : forall (w : pmw MI ST) A M model c R ret S,
    PMX w A M model c -> cregs w R ret -> 0 <= S <= w_STK w - PM_FRAME -> callB MI ST A (w_s w) R M model (w_sp w) ret S.
  Proof using AC MI ST.
    intros w A M model c R ret S X (C1 & C2 & C3 & C4 & C5 & C6) HS. pose proof (x_geo X) as GEO.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & _). unfold w_sp0, PM_FRAME in *.
    eapply pmx_callB; [exact X | | exact HS]. constructor; try assumption. lia.
  Qed.

  Lemma cregs_kept : forall (w : pmw MI ST) R R' ret ret',
    cregs w R ret -> kept R R' -> getr R' 1%bv = Z_to_bv 64 ret' -> ret_ok (Z_to_bv 64 ret') -> 0 <= ret' < 2 ^ 64 -> cregs w R' ret'.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w R R' ret ret' (C1 & C2 & C3 & C4 & C5 & C6) K H1 H2 H3.
    split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
    rewrite (K 2%bv) by (first [solve [clear; cbv; tauto] | cbv; tauto]). rewrite (K 3%bv) by (first [solve [clear; cbv; tauto] | cbv; tauto]). rewrite (K 4%bv) by (first [solve [clear; cbv; tauto] | cbv; tauto]). tauto.
  Qed.

  Definition frame_but (w : pmw MI ST) (lo hi : Z) (a : Z) : Prop := w_sp w <= a < w_sp0 w /\ ~ (lo <= a < hi).

  Lemma live_below_sp : forall (w : pmw MI ST) A M model c q k a,
    PMX w A M model c -> In (q, k) (live MI A) -> q <= a < q + k -> a < w_sp w.
  Proof using AC MI ST.
    intros w A M model c q k a X Hin Ha. pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & _). unfold w_sp0, PM_FRAME in *.
    pose proof (ai_live_block MI A M model q k (x_ai X) Hin) as (_ & _ & _ & Hhi & _). lia.
  Qed.

  Lemma pm_ds_step : forall (w : pmw MI ST) c0 K A M model c A' R R' M' model' B B' rest (J Xf : Z -> Prop),
    PMS w c0 K -> PMX w A M model c -> c_tr c = B ++ rest -> pm_bud (w_n w) c -> Zlength rest <= 1 ->
    Zlength B <= 1 -> (forall q k, In (q, k) B -> In (q, k) (live MI A)) ->
    retB MI ST A' (w_s w) R R' M' model model' ->
    Zlength B' <= 1 -> (forall q k, In (q, k) B' -> In (q, k) (live MI A') /\ 0 < k <= DS_MAXBLK) ->
    mdef M' (w_sp w + 272) DS_SIZE ->
    blk_xfer B B' (live MI A) (live MI A') -> junk_ok MI A J ->
    eff MI A A' M M' (w_sp w - dc_stack dcS1, w_sp w) (fun a => ds_foot (w_sp w + 272) B a \/ ds_foot (w_sp w + 272) B' a \/ J a \/ Xf a) ->
    (forall a, Xf a -> w_sp w + 272 + DS_SIZE <= a < w_sp0 w - 104 /\ M' (Z_to_bv 64 a) <> None) ->
    PMX w A' M' model' (set_tr c (B' ++ rest)) /\ pm_bud (w_n w) (set_tr c (B' ++ rest))
    /\ CRep.agree_on (fun a => frame_but w (w_sp w + 272) (w_sp w + 272 + DS_SIZE) a /\ ~ Xf a) M M'.
  Proof using AC MI ST.
    intros w c0 K A M model c A' R R' M' model' B B' rest J Xf PS X Htr BUD Hrest HB HBl RB HB' HB'l Hdef XFER HJ EF HXf.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & _).
    destruct RB as [AI' MS' FS' FDS' SX' KEPT].
    assert (X' : PMX w A' M' model' (set_tr c (B' ++ rest))).
    { eapply (pmx_dsS w A M model c A' M' model' (dc_stack dcS1) (w_sp w + 272) B B' rest J Xf);
        [exact X | exact Htr | exact AI' | exact MS' | exact FS' | exact FDS' | exact EF
        | cbn [dc_stack dcS1]; unfold PM_FRAME; lia | lia | unfold DS_SIZE, w_sp0, PM_FRAME; lia | exact HJ
        | intros a Ha; destruct (HXf a Ha); unfold w_sp0, PM_FRAME, DS_SIZE in *; split; [lia|assumption]
        | exact Hdef | exact XFER | exact HB | exact HB']. }
    split; [exact X'|]. split.
    - destruct BUD as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9). repeat (split; [assumption|]). cbn [set_tr c_tr].
      rewrite Htr in B8, B9. unfold Zlength in *. rewrite length_app in *. rewrite Nat2Z.inj_add in *. split; [lia|].
      intros b Hb. apply in_app_iff in Hb. destruct Hb as [Hb|Hb].
      + destruct b as [q k]. destruct (HB'l q k Hb). unfold DS_MAXBLK in *. cbn. lia.
      + apply B9. apply in_app_iff. right. exact Hb.
    - eapply (pmx_frame_keep SEGS Ly.L MI ST ly_img_low ly_rw_img ly_errno_img);
        [exact X | exact EF | cbn [dc_stack dcS1]; lia |].
      intros a [[Hw Hno] HnX]. split; [exact Hw|]. unfold ds_foot, zwin, DS_SIZE in *.
      intros [[Ho|(q & k & Hq & Ha)]|[[Ho|(q & k & Hq & Ha)]|[Hj|Hx]]]; [lia | | lia | | | exact (HnX Hx)].
      + pose proof (live_below_sp w A M model c q k a X (HBl q k Hq) Ha). lia.
      + pose proof (live_below_sp w A' M' model' _ q k a X' (proj1 (HB'l q k Hq)) Ha). lia.
      + pose proof (proj1 (HJ a Hj)). unfold w_sp0, PM_FRAME in *. lia.
  Qed.

  Lemma pmx_ds_room1 : forall (w : pmw MI ST) c0 K A M model c,
    PMS w c0 K -> PMX w A M model c -> pm_bud (w_n w) c -> Zlength (c_tr c) <= 1 -> ds_room1 SEGS Ly.L MI A.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K A M model c PS X B Hlen. split.
    { pose proof (x_caps X) as (_ & _ & HN). unfold DS_MAXBLK, LIB_NMAX in *. lia. }
    intros q n1 n2 H1 H2. unfold DS_MAXBLK in H1, H2.
    change (roomL MI A ((q, n1) :: live MI A) n2) with (roomL MI A ((0, n1) :: live MI A) n2).
    eapply pmx_room3S; [exact X | exact B | exact (ps_budS _ _ _ PS) | exact (ps_budN _ _ _ PS) | exact (ps_budB _ _ _ PS) | exact Hlen | lia | lia].
  Qed.

  #[local] Notation DL := (cl_ds_laws _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).

  Lemma pm_put_cstr : forall (w : pmw MI ST) c0 K (fx : FPState) A M model c R (err len p n m ret : Z) (B rest : list (Z * Z)),
    PMS w c0 K -> PMX w A M model c -> c_tr c = B ++ rest -> pm_bud (w_n w) c -> Zlength rest <= 1 ->
    ds_rep A M (w_sp w + 272) err len B ->
    cregs w R ret ->
    getr R 10%bv = Z_to_bv 64 (w_sp w + 272) -> getr R 11%bv = Z_to_bv 64 p -> getr R 12%bv = Z_to_bv 64 m ->
    ro_cstr SEGS Ly.L p n -> 0 <= m <= n -> len + m <= DS_MAXLEN ->
    (forall A' R' M' model' B',
        PMX w A' M' model' (set_tr c (B' ++ rest)) -> pm_bud (w_n w) (set_tr c (B' ++ rest)) ->
        kept R R' -> getr R' 10%bv = Z_to_bv 64 (w_sp w + 272) ->
        ds_rep A' M' (w_sp w + 272) err (len + m) B' ->
        CRep.agree_on (frame_but w (w_sp w + 272) (w_sp w + 272 + DS_SIZE)) M M' ->
        srealizes SEGS (cfg fx R' ret M' model') K) ->
    srealizes SEGS (cfg fx R (dc_put_cstr dcS1) M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx A M model c R err len p n m ret B rest PS X Htr BUD Hrest DS CR Ha0 Ha1 Ha2 RO Hm Hlen CONT.
    pose proof (x_geo X) as GEO. destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & _).
    pose proof (dl_blocks _ _ _ _ _ _ DL _ _ _ _ _ _ DS) as [HBlen HBin].
    eapply (cl_put_cstr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL fx A (w_s w) R M model (w_sp w) ret (w_sp w + 272) err len p n m B K).
    - eapply pmx_cregs_callB; [exact X | exact CR | cbn [dc_stack dcS1]; unfold PM_FRAME; lia].
    - exact (x_roc X).
    - exact Ha0. - exact Ha1. - exact Ha2. - exact DS.
    - eapply (pmx_above_sp_frame SEGS Ly.L MI ST ly_img_low ly_rw_img); [exact X | lia | unfold DS_SIZE, w_sp0, PM_FRAME; lia].
    - exact RO. - exact Hm. - exact Hlen.
    - eapply pmx_ds_room; [exact PS | exact X | exact BUD].
    - intros A' R' M' model' B' J RB Hres DS' XFER HJ EF.
      pose proof (dl_blocks _ _ _ _ _ _ DL _ _ _ _ _ _ DS') as [HB'len HB'in].
      pose proof (dl_def _ _ _ _ _ _ DL _ _ _ _ _ _ DS') as (Hdef' & _).
      destruct (pm_ds_step w c0 K A M model c A' R R' M' model' B B' rest J (fun _ => False) PS X Htr BUD Hrest HBlen
                 ltac:(intros q k Hq; exact (proj1 (HBin q k Hq))) RB HB'len HB'in Hdef' XFER HJ EF ltac:(intros a []))
        as (X' & BUD' & AG).
      eapply CONT; [exact X' | exact BUD' | exact (rb_kept _ _ _ _ _ _ _ _ _ _ _ RB) | exact (Hres eq_refl) | exact DS' |].
      eapply agree_on_weaken; [exact AG|]. intros a Ha. split; [exact Ha | intros []].
  Qed.

  Lemma pm_put_num : forall (pc lo hi : Z) (enc : Z -> Z),
    put_num_stmt SEGS Ly.L MI ST dcS1 ds_rep pc lo hi enc ->
    forall (w : pmw MI ST) c0 K (fx : FPState) A M model c R (err len x ret : Z) (B rest : list (Z * Z)),
    PMS w c0 K -> PMX w A M model c -> c_tr c = B ++ rest -> pm_bud (w_n w) c -> Zlength rest <= 1 ->
    ds_rep A M (w_sp w + 272) err len B ->
    cregs w R ret ->
    getr R 10%bv = Z_to_bv 64 (w_sp w + 272) -> getr R 11%bv = Z_to_bv 64 (enc x) -> lo <= x < hi -> len + 24 <= DS_MAXLEN ->
    (forall A' R' M' model' B',
        PMX w A' M' model' (set_tr c (B' ++ rest)) -> pm_bud (w_n w) (set_tr c (B' ++ rest)) ->
        kept R R' -> getr R' 10%bv = Z_to_bv 64 (w_sp w + 272) ->
        ds_rep A' M' (w_sp w + 272) err (len + 24) B' ->
        CRep.agree_on (frame_but w (w_sp w + 272) (w_sp w + 272 + DS_SIZE)) M M' ->
        srealizes SEGS (cfg fx R' ret M' model') K) ->
    srealizes SEGS (cfg fx R pc M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros pc lo hi enc STMT w c0 K fx A M model c R err len x ret B rest PS X Htr BUD Hrest DS CR Ha0 Ha1 Hx Hlen CONT.
    pose proof (x_geo X) as GEO. destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & _).
    pose proof (dl_blocks _ _ _ _ _ _ DL _ _ _ _ _ _ DS) as [HBlen HBin].
    eapply (STMT fx A (w_s w) R M model (w_sp w) ret (w_sp w + 272) err len x B K).
    - eapply pmx_cregs_callB; [exact X | exact CR | cbn [dc_stack dcS1]; unfold PM_FRAME; lia].
    - exact (x_roc X).
    - exact Ha0. - exact Ha1. - exact Hx. - exact DS.
    - eapply (pmx_above_sp_frame SEGS Ly.L MI ST ly_img_low ly_rw_img); [exact X | lia | unfold DS_SIZE, w_sp0, PM_FRAME; lia].
    - exact Hlen.
    - eapply pmx_ds_room; [exact PS | exact X | exact BUD].
    - intros A' R' M' model' B' J RB Hres DS' XFER HJ EF.
      pose proof (dl_blocks _ _ _ _ _ _ DL _ _ _ _ _ _ DS') as [HB'len HB'in].
      pose proof (dl_def _ _ _ _ _ _ DL _ _ _ _ _ _ DS') as (Hdef' & _).
      destruct (pm_ds_step w c0 K A M model c A' R R' M' model' B B' rest J (fun _ => False) PS X Htr BUD Hrest HBlen
                 ltac:(intros q k Hq; exact (proj1 (HBin q k Hq))) RB HB'len HB'in Hdef' XFER HJ EF ltac:(intros a []))
        as (X' & BUD' & AG).
      eapply CONT; [exact X' | exact BUD' | exact (rb_kept _ _ _ _ _ _ _ _ _ _ _ RB) | exact (Hres eq_refl) | exact DS' |].
      eapply agree_on_weaken; [exact AG|]. intros a Ha. split; [exact Ha | intros []].
  Qed.
  Definition pm_put_u16 := pm_put_num _ _ _ _ (cl_put_u16 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).
  Definition pm_put_u32 := pm_put_num _ _ _ _ (cl_put_u32 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).
  Definition pm_put_u64 := pm_put_num _ _ _ _ (cl_put_u64 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).
  Definition pm_put_int := pm_put_num _ _ _ _ (cl_put_int _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).

  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  Lemma mod16_8 : forall x d, x mod 16 = 0 -> d mod 8 = 0 -> (x + d) mod 8 = 0.
  Proof using. intros; lia. Qed.
  Lemma mod16_4 : forall x d, x mod 16 = 0 -> d mod 4 = 0 -> (x + d) mod 4 = 0.
  Proof using. intros; lia. Qed.
  Lemma mod16_2 : forall x d, x mod 16 = 0 -> d mod 2 = 0 -> (x + d) mod 2 = 0.
  Proof using. intros; lia. Qed.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

  Definition ftemp (w : pmw MI ST) (t n : Z) : Prop :=
    w_sp w <= t /\ t + n <= w_sp0 w - 104 /\ (t + n <= w_sp w + 272 \/ w_sp w + 272 + DS_SIZE <= t).

  Lemma pm_ctor : forall (w : pmw MI ST) c0 K (fx : FPState) A M model c R (err ppos pstr1 pstr2 ret : Z) (rest : list (Z * Z)),
    PMS w c0 K -> PMX w A M model c -> c_tr c = rest -> pm_bud (w_n w) c -> Zlength rest <= 1 ->
    cregs w R ret ->
    getr R 10%bv = Z_to_bv 64 (w_sp w + 272) -> getr R 11%bv = Z_to_bv 64 ppos -> getr R 12%bv = Z_to_bv 64 (w_cons w) ->
    getr R 13%bv = Z_to_bv 64 pstr1 -> getr R 14%bv = Z_to_bv 64 (err mod 2 ^ 64) -> getr R 15%bv = Z_to_bv 64 pstr2 ->
    - 2 ^ 31 <= err < 0 ->
    ftemp w ppos 24 -> ftemp w pstr1 24 -> ftemp w pstr2 24 ->
    fld SEGS M pstr1 2 0 -> fld SEGS M pstr2 2 0 ->
    (forall A' R' M' model' B',
        PMX w A' M' model' (set_tr c (B' ++ rest)) -> pm_bud (w_n w) (set_tr c (B' ++ rest)) ->
        kept R R' -> ds_rep A' M' (w_sp w + 272) err 0 B' ->
        CRep.agree_on (frame_but w (w_sp w + 272) (w_sp w + 272 + DS_SIZE)) M M' ->
        srealizes SEGS (cfg fx R' ret M' model') K) ->
    srealizes SEGS (cfg fx R (dc_ctor dcS1) M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx A M model c R err ppos pstr1 pstr2 ret rest PS X Htr BUD Hrest CR Ha0 Ha1 Ha2 Ha3 Ha4 Ha5 Herr T1 T2 T3 F1 F2 CONT.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & Gc2 & Gap & Gn & Gw).
    unfold ftemp, w_sp0, PM_FRAME, DS_SIZE in T1, T2, T3.
    assert (WD : forall t n, w_sp w <= t -> t + n <= w_sp w + 880 -> mdef M t n).
    { intros t n Ht Hn i Hi. pose proof (x_wdef X (t + i - (w_sp w + 880 - w_STK w)) ltac:(unfold w_sp0, PM_FRAME; lia)) as D.
      unfold w_sp0, PM_FRAME in D. replace (w_sp w + 880 - w_STK w + (t + i - (w_sp w + 880 - w_STK w))) with (t + i) in D by lia. exact D. }
    eapply (cl_ds_ctor _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL fx A (w_s w) R M model (w_sp w) ret (w_sp w + 272) ppos (w_cons w) pstr1 err pstr2 K).
    - eapply pmx_cregs_callB; [exact X | exact CR | cbn [dc_stack dcS1]; unfold PM_FRAME; lia].
    - exact (x_roc X).
    - exact Ha0. - exact Ha1. - exact Ha2. - exact Ha3. - exact Ha4. - exact Ha5. - exact Herr.
    - eapply (pmx_above_sp_frame SEGS Ly.L MI ST ly_img_low ly_rw_img); [exact X | lia | unfold DS_SIZE, w_sp0, PM_FRAME; lia].
    - apply mod16_8; [exact Gsp16 | reflexivity].
    - apply WD; unfold DS_SIZE; lia.
    - eapply (pmx_above_sp_frame SEGS Ly.L MI ST ly_img_low ly_rw_img); [exact X | lia | unfold w_sp0, PM_FRAME; lia].
    - apply WD; lia.
    - eapply (pmx_above_sp_frame SEGS Ly.L MI ST ly_img_low ly_rw_img); [exact X | lia | unfold w_sp0, PM_FRAME; lia].
    - exact F1.
    - apply WD; lia.
    - eapply (pmx_above_sp_frame SEGS Ly.L MI ST ly_img_low ly_rw_img); [exact X | lia | unfold w_sp0, PM_FRAME; lia].
    - exact F2.
    - apply WD; lia.
    - split; [left; lia | intros a Ha; cbn [dc_stack dcS1] in Ha; unfold zwin, w_sp0, PM_FRAME in *; lia].
    - lia.
    - exact (x_consf X).
    - intros a Ha. unfold zwin, DS_SIZE in *. unfold w_sp0, PM_FRAME in Gc1. repeat split; lia.
    - eapply pmx_ds_room; [exact PS | exact X | exact BUD].
    - intros A' R' M' model' B' RB DS' XFER EF.
      pose proof (dl_blocks _ _ _ _ _ _ DL _ _ _ _ _ _ DS') as [HB'len HB'in].
      pose proof (dl_def _ _ _ _ _ _ DL _ _ _ _ _ _ DS') as (Hdef' & _).
      destruct (pm_ds_step w c0 K A M model c A' R R' M' model' [] B' rest (fun _ => False) (fun _ => False) PS X Htr BUD Hrest
                 ltac:(rewrite Zlength_nil; lia) ltac:(intros q k [])
                 RB HB'len HB'in Hdef' XFER ltac:(intros a [])
                 ltac:(eapply eff_weaken; [exact EF | intros a Ha; right; left; exact Ha]) ltac:(intros a []))
        as (X' & BUD' & AG).
      eapply CONT; [exact X' | exact BUD' | exact (rb_kept _ _ _ _ _ _ _ _ _ _ _ RB) | exact DS' |].
      eapply agree_on_weaken; [exact AG|]. intros a Ha. split; [exact Ha | intros []].
  Qed.

  Lemma pm_pdiag : forall (with_err : bool) (pc : Z),
    pdiag_stmt SEGS Ly.L MI ST dcS1 ds_rep pc with_err ->
    forall (w : pmw MI ST) c0 K (fx : FPState) A M model c R (err ret : Z) (rest : list (Z * Z)),
    PMS w c0 K -> PMX w A M model c -> c_tr c = rest -> pm_bud (w_n w) c -> Zlength rest <= 1 ->
    cregs w R ret ->
    getr R 10%bv = Z_to_bv 64 (w_sp w + 272) -> getr R 11%bv = Z_to_bv 64 (w_cons w) -> getr R 12%bv = Z_to_bv 64 (c_icount c) ->
    (if with_err then getr R 13%bv = Z_to_bv 64 (err mod 2 ^ 64) /\ - 2 ^ 31 <= err < 0 else err = - 4) ->
    (forall A' R' M' model' B',
        PMX w A' M' model' (set_tr c (B' ++ rest)) -> pm_bud (w_n w) (set_tr c (B' ++ rest)) ->
        kept R R' -> ds_rep A' M' (w_sp w + 272) err 0 B' ->
        CRep.agree_on (frame_but w (w_sp w + 272) (w_sp w + 272 + DS_SIZE)) M M' ->
        srealizes SEGS (cfg fx R' ret M' model') K) ->
    srealizes SEGS (cfg fx R pc M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros with_err pc STMT w c0 K fx A M model c R err ret rest PS X Htr BUD Hrest CR Ha0 Ha1 Ha2 Herr CONT.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & Gc2 & Gap & Gn & Gw).
    pose proof (x_scal X) as (S1 & S2 & _).
    assert (WD : forall t n, w_sp w <= t -> t + n <= w_sp w + 880 -> mdef M t n).
    { intros t n Ht Hn i Hi. pose proof (x_wdef X (t + i - (w_sp w + 880 - w_STK w)) ltac:(unfold w_sp0, PM_FRAME; lia)) as D.
      unfold w_sp0, PM_FRAME in D. replace (w_sp w + 880 - w_STK w + (t + i - (w_sp w + 880 - w_STK w))) with (t + i) in D by lia. exact D. }
    eapply (STMT fx A (w_s w) R M model (w_sp w) ret (w_sp w + 272) (w_cons w) (c_icount c) err K).
    - eapply pmx_cregs_callB; [exact X | exact CR | cbn [dc_stack dcS1]; unfold PM_FRAME; lia].
    - exact (x_roc X).
    - exact Ha0. - exact Ha1. - exact Ha2.
    - lia.
    - exact Herr.
    - eapply (pmx_above_sp_frame SEGS Ly.L MI ST ly_img_low ly_rw_img); [exact X | lia | unfold DS_SIZE, w_sp0, PM_FRAME; lia].
    - apply mod16_8; [exact Gsp16 | reflexivity].
    - apply WD; unfold DS_SIZE; lia.
    - split; [left; lia | intros a Ha; cbn [dc_stack dcS1] in Ha; unfold zwin, w_sp0, PM_FRAME in *; lia].
    - lia.
    - exact (x_consf X).
    - intros a Ha. unfold zwin, DS_SIZE in *. unfold w_sp0, PM_FRAME in Gc1. lia.
    - eapply pmx_ds_room; [exact PS | exact X | exact BUD].
    - intros A' R' M' model' B' RB DS' XFER EF.
      pose proof (dl_blocks _ _ _ _ _ _ DL _ _ _ _ _ _ DS') as [HB'len HB'in].
      pose proof (dl_def _ _ _ _ _ _ DL _ _ _ _ _ _ DS') as (Hdef' & _).
      destruct (pm_ds_step w c0 K A M model c A' R R' M' model' [] B' rest (fun _ => False) (fun _ => False) PS X Htr BUD Hrest
                 ltac:(rewrite Zlength_nil; lia) ltac:(intros q k [])
                 RB HB'len HB'in Hdef' XFER ltac:(intros a [])
                 ltac:(eapply eff_weaken; [exact EF | intros a Ha; right; left; exact Ha]) ltac:(intros a []))
        as (X' & BUD' & AG).
      eapply CONT; [exact X' | exact BUD' | exact (rb_kept _ _ _ _ _ _ _ _ _ _ _ RB) | exact DS' |].
      eapply agree_on_weaken; [exact AG|]. intros a Ha. split; [exact Ha | intros []].
  Qed.
  Definition pm_pdiag0 := pm_pdiag false _ (cl_pdiag0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).
  Definition pm_pdiagE := pm_pdiag true _ (cl_pdiagE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).

  Lemma pm_dtor : forall (w : pmw MI ST) c0 K (fx : FPState) A M model c R (err len ret : Z) (B rest : list (Z * Z)),
    PMS w c0 K -> PMX w A M model c -> c_tr c = B ++ rest -> pm_bud (w_n w) c -> Zlength rest <= 1 ->
    ds_rep A M (w_sp w + 272) err len B ->
    cregs w R ret -> getr R 10%bv = Z_to_bv 64 (w_sp w + 272) ->
    (forall A' R' M' model',
        PMX w A' M' model' (set_tr c rest) -> pm_bud (w_n w) (set_tr c rest) ->
        kept R R' ->
        CRep.agree_on (frame_but w (w_sp w + 272) (w_sp w + 272 + DS_SIZE)) M M' ->
        srealizes SEGS (cfg fx R' ret M' model') K) ->
    srealizes SEGS (cfg fx R (dc_dtor dcS1) M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx A M model c R err len ret B rest PS X Htr BUD Hrest DS CR Ha0 CONT.
    pose proof (x_geo X) as GEO. destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & _).
    pose proof (dl_blocks _ _ _ _ _ _ DL _ _ _ _ _ _ DS) as [HBlen HBin].
    eapply (cl_ds_dtor _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL fx A (w_s w) R M model (w_sp w) ret (w_sp w + 272) err len B K).
    - eapply pmx_cregs_callB; [exact X | exact CR | cbn [dc_stack dcS1]; unfold PM_FRAME; lia].
    - exact (x_roc X).
    - exact Ha0. - exact DS.
    - eapply (pmx_above_sp_frame SEGS Ly.L MI ST ly_img_low ly_rw_img); [exact X | lia | unfold DS_SIZE, w_sp0, PM_FRAME; lia].
    - intros A' R' M' model' RB XFER Hdef' EF.
      destruct (pm_ds_step w c0 K A M model c A' R R' M' model' B [] rest (fun _ => False) (fun _ => False) PS X Htr BUD Hrest HBlen
                 ltac:(intros q k Hq; exact (proj1 (HBin q k Hq))) RB ltac:(rewrite Zlength_nil; lia) ltac:(intros q k [])
                 Hdef' XFER ltac:(intros a []) ltac:(eapply eff_weaken; [exact EF | intros a Ha; left; exact Ha]) ltac:(intros a []))
        as (X' & BUD' & AG).
      eapply CONT; [exact X' | exact BUD' | exact (rb_kept _ _ _ _ _ _ _ _ _ _ _ RB) |].
      eapply agree_on_weaken; [exact AG|]. intros a Ha. split; [exact Ha | intros []].
  Qed.

  Lemma set_tr_id : forall c, set_tr c (c_tr c) = c.
  Proof using. intros c. destruct c. reflexivity. Qed.

  Lemma pm_exhausted : forall (w : pmw MI ST) c0 K (fx : FPState) A M model c R (inst_offset opcode type ret : Z),
    PMS w c0 K -> PMX w A M model c -> pm_bud (w_n w) c -> Zlength (c_tr c) <= 1 ->
    cregs w R ret ->
    getr R 10%bv = Z_to_bv 64 (w_p w) -> getr R 11%bv = Z_to_bv 64 inst_offset ->
    getr R 12%bv = Z_to_bv 64 opcode -> getr R 13%bv = Z_to_bv 64 type ->
    0 <= inst_offset < 2 ^ 63 -> 0 <= opcode < 2 ^ 16 -> 0 <= type < 2 ^ 32 ->
    (forall A' R' M' model',
        PMX w A' M' model' c -> kept R R' -> getr R' 10%bv = Z_to_bv 64 (2 ^ 64 - 4) ->
        CRep.agree_on (fun a => w_sp w <= a < w_sp0 w) M M' ->
        srealizes SEGS (cfg fx R' ret M' model') K) ->
    srealizes SEGS (cfg fx R (dc_exhausted dcS1) M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w c0 K fx A M model c R inst_offset opcode type ret PS X BUD Hlen CR Ha0 Ha1 Ha2 Ha3 Hio Hop Hty CONT.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & Gc2 & Gap & Gn & Gw).
    pose proof (x_scal X) as (S1 & S2 & _).
    eapply (cl_exhausted _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL fx A (w_s w) R M model (w_sp w) ret (w_p w) (w_cons w) (w_n w) (c_widx c) (c_icount c) inst_offset opcode type K).
    - eapply pmx_cregs_callB; [exact X | exact CR | cbn [dc_stack dcS1]; unfold PM_FRAME; lia].
    - exact (x_roc X).
    - exact Ha0. - exact Ha1. - exact Ha2. - exact Ha3. - exact Hio. - exact Hop. - exact Hty.
    - left. lia.
    - unfold PARSER_SIZE in *. lia.
    - intros a Ha. unfold zwin, PARSER_SIZE in *. unfold w_sp0, PM_FRAME in Gpp. cbn [dc_stack dcS1]. lia.
    - exact (x_cons X). - exact (x_n X). - exact (x_widx X). - exact (x_icount X).
    - lia. - lia. - lia.
    - split; [left; lia | intros a Ha; cbn [dc_stack dcS1] in Ha; unfold zwin, w_sp0, PM_FRAME in *; lia].
    - lia.
    - exact (x_consf X).
    - eapply pmx_ds_room1; [exact PS | exact X | exact BUD | exact Hlen].
    - intros A' R' M' model' J RB Hres HL HJ EF.
      destruct RB as [AI' MS' FS' FDS' SX' KEPT].
      assert (X' : PMX w A' M' model' (set_tr c (c_tr c))).
      { eapply (pmx_throughS w A M model c A' M' model' (dc_stack dcS1) (fun a => J a) (c_tr c));
          [exact X | exact AI' | exact MS' | exact FS' | exact FDS' | exact EF
          | cbn [dc_stack dcS1]; unfold PM_FRAME; lia
          | intros a Hj HP; exact (junk_not_fprot SEGS Ly.L MI ST w A M model c J a X HJ Hj HP)
          | intros a Hj; left; right; exact (junk_junkL SEGS Ly.L MI ST w A M model c J a X HJ Hj)
          | intros a Hj Hz; exfalso; pose proof (proj1 (HJ a Hj)); unfold zwin, w_sp0, PM_FRAME in *; lia
          | intros b Hb; apply (Permutation_in b (Permutation_sym HL)); eapply cblk_live; [exact X | exact Hb]
          | rewrite <- c_blocks_split; exact (Permutation_trans HL (x_live X))]. }
      rewrite set_tr_id in X'.
      eapply CONT; [exact X' | exact KEPT | exact Hres |].
      eapply (pmx_frame_keep SEGS Ly.L MI ST ly_img_low ly_rw_img ly_errno_img); [exact X | exact EF | cbn [dc_stack dcS1]; lia |].
      intros a Ha. split; [exact Ha|]. intros Hj. pose proof (proj1 (HJ a Hj)). unfold zwin, w_sp0, PM_FRAME in *. lia.
  Qed.

  Lemma kwr_mdef : forall E M (n : N) (b off k : Z),
    ev E n = Z_to_bv 64 b -> mdef M (b + off) k -> 0 <= b < 2 ^ 64 -> 0 <= b + off -> b + off + k < 2 ^ 64 -> 0 <= k ->
    kentry_ok SEGS E M (KWr (SA (EVar n) off) (ELit k)).
  Proof using.
    intros E M n b off k Hn HD Hb Hbo Hbk Hk. cbn [kentry_ok].
    unfold flat, estart, elenZ. cbn [a_base a_off edenot]. rewrite Hn, !u64_of_Z by lia.
    split; [lia|]. intros d m Hd Hdm.
    replace (b + off + d) with ((b + off) + d) by lia. apply (mdef_store_ok_off SEGS M (b + off) k d m HD); lia.
  Qed.

  Lemma pmx_kwr : forall (w : pmw MI ST) A M model c E (n : N),
    PMX w A M model c -> ev E n = Z_to_bv 64 (w_sp w) -> kentry_ok SEGS E M (KWr (SA (EVar n) 0) (ELit 776)).
  Proof using AC MI ST.
    intros w A M model c E n X Hn. pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & _). unfold w_sp0, PM_FRAME in *.
    eapply kwr_mdef; [exact Hn | | lia | lia | lia | lia].
    intros i Hi. pose proof (x_wdef X (w_sp w + 0 + i - (w_sp w + 880 - w_STK w)) ltac:(unfold w_sp0, PM_FRAME; lia)) as D.
    unfold w_sp0, PM_FRAME in D. replace (w_sp w + 880 - w_STK w + (w_sp w + 0 + i - (w_sp w + 880 - w_STK w))) with (w_sp w + 0 + i) in D by lia. exact D.
  Qed.

  Lemma fld_cellw : forall M a (w : N) v, fld SEGS M a (N.to_nat w) v -> 0 <= v < 2 ^ (8 * Z.of_N w) -> cellw SEGS M a w v.
  Proof using. intros M a w v H Hv. split; [exact Hv | exact H]. Qed.

  Ltac w2blen := rewrite ?length_N_to_le_bytes.
  Lemma rdn_wbytes_prefix : forall m (a : word) bs k,
    bv_unsigned a + Z.of_nat (length bs) <= 2 ^ 64 -> (k <= length bs)%nat ->
    rdn SEGS (wbytes m a bs) a k = Some (firstn k bs).
  Proof using. intros m a bs k H Hk. eapply rdn_firstn; [apply rdn_wbytes_self; exact H | exact Hk]. Qed.

  Ltac rdback := unfold CRep.fld; repeat (rewrite rdn_wbytes_out_Z by (w2blen; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia));
                 first [ apply rdn_wbytes_self; w2blen; rewrite u64_of_Z by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia
                       |
                         rewrite rdn_wbytes_prefix; [ reflexivity | w2blen; rewrite u64_of_Z by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | w2blen; lia ]
                       | idtac ].

  Ltac stin := repeat (first [ apply stores_in_refl
                             | eapply stores_in_wbytes_more; [ | lia | w2blen; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia
                                                              | w2blen; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unfold zwin; intros; lia ] ]).

  Ltac pm_seed R w c extra :=
    pose (E := Eseed R (Z_to_bv 64 (w_sp w) :: Z_to_bv 64 (w_p w) :: Z_to_bv 64 (w_words w) :: Z_to_bv 64 (w_n w) ::
                        Z_to_bv 64 (w_cons w) :: Z_to_bv 64 (c_icount c) :: Z_to_bv 64 (c_widx c) :: extra)).
  Ltac seedHR_ HR E l R :=
    assert (HR : regs_ok E (srs sr_id l) R)
      by (apply regs_ok_srs; [apply regs_ok_seed|]; repeat constructor; cbn [fst snd]; try (intros XX; discriminate XX); evs;
          first [assumption | reflexivity | rewrite w_add by lia; assumption]).
  Tactic Notation "seedHR" ident(HR) constr(E) uconstr(l) constr(R) :=
    let l' := constr:(l : list (reg * expr)) in seedHR_ HR E l' R.

  Definition pm_kn : list kentry :=
    [KWord (SA (EVar 33) 48) (N.to_nat 8) (EVar 34); KWord (SA (EVar 33) 56) (N.to_nat 8) (EVar 35);
     KWord (SA (EVar 33) 8) (N.to_nat 8) (EVar 36); KWord (SA (EVar 33) 80) (N.to_nat 8) (EVar 37);
     KWord (SA (EVar 33) 72) (N.to_nat 8) (EVar 38);
     KWr (SA (EVar 32) 0) (ELit 776); KWr (SA (EVar 33) 72) (ELit 22); KWr (SA (EVar 33) 216) (ELit 72);
     KRange (EVar 32) (2 ^ 24) (2 ^ 47 - 880); KRange (EVar 33) (2 ^ 24) (2 ^ 47 - 288);
     KRange (EVar 35) 0 (2 ^ 24); KRange (EVar 37) 0 (2 ^ 24); KRange (EVar 38) 0 (2 ^ 24);
     KDisj (SA (EVar 32) 0) (ELit 880) (SA (EVar 33) 0) (ELit 288)].

  Lemma pmx_know : forall (w : pmw MI ST) A M model c E,
    PMX w A M model c ->
    ev E 32 = Z_to_bv 64 (w_sp w) -> ev E 33 = Z_to_bv 64 (w_p w) -> ev E 34 = Z_to_bv 64 (w_words w) ->
    ev E 35 = Z_to_bv 64 (w_n w) -> ev E 36 = Z_to_bv 64 (w_cons w) -> ev E 37 = Z_to_bv 64 (c_icount c) ->
    ev E 38 = Z_to_bv 64 (c_widx c) ->
    know_ok SEGS E M pm_kn.
  Proof using AC MI ST.
    intros w A M model c E X E32 E33 E34 E35 E36 E37 E38.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & Gc2 & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    pose proof (x_scal X) as (Sc1 & Sc2 & _).
    assert (Hwr : 0 <= w_words w < 2 ^ 64) by (destruct (Z.eq_dec (w_words w) 0); [lia | destruct (Gw ltac:(assumption)); lia]).
    pose proof (fld_cellw M _ 8 _ (x_words X) ltac:(lia)) as Cw.
    pose proof (fld_cellw M _ 8 _ (x_n X) ltac:(lia)) as Cn.
    pose proof (fld_cellw M _ 8 _ (x_cons X) ltac:(lia)) as Cc.
    pose proof (fld_cellw M _ 8 _ (x_icount X) ltac:(lia)) as Ci.
    pose proof (fld_cellw M _ 8 _ (x_widx X) ltac:(lia)) as Cx. unfold O_WORDS, O_N, O_ICOUNT, O_WIDX in *.
    unfold pm_kn. repeat apply Forall_cons; try apply Forall_nil.
    - eapply kword_var; [exact Cw | cbn; lia | exact E33 | lia | lia | cbn; lia | cbn [edenot]; exact E34].
    - eapply kword_var; [exact Cn | cbn; lia | exact E33 | lia | lia | cbn; lia | cbn [edenot]; exact E35].
    - eapply kword_var; [exact Cc | cbn; lia | exact E33 | lia | lia | cbn; lia | cbn [edenot]; exact E36].
    - eapply kword_var; [exact Ci | cbn; lia | exact E33 | lia | lia | cbn; lia | cbn [edenot]; exact E37].
    - eapply kword_var; [exact Cx | cbn; lia | exact E33 | lia | lia | cbn; lia | cbn [edenot]; exact E38].
    - eapply pmx_kwr; [exact X | exact E32].
    - eapply kwr_mdef; [exact E33 | eapply mdef_sub; [exact (x_pdef X) | unfold O_WIDX; lia | unfold PARSER_SIZE; lia] | lia | lia | lia | lia].
    - eapply kwr_mdef; [exact E33 | eapply mdef_sub; [exact (x_pdef X) | lia | unfold PARSER_SIZE; lia] | lia | lia | lia | lia].
    - eapply krange_var; [exact E32 | lia | lia].
    - eapply krange_var; [exact E33 | lia | lia].
    - eapply krange_var; [exact E35 | lia | lia].
    - eapply krange_var; [exact E37 | lia | lia].
    - eapply krange_var; [exact E38 | lia | lia].
    - eapply kdisj_vars; [exact E32 | exact E33 | lia | lia | lia | lia | lia].
  Qed.
  Ltac seedHK HK w A M model c E X :=
    assert (HK : know_ok SEGS E M pm_kn) by (apply (pmx_know w A M model c E X); evs; reflexivity).

  Lemma know_more : forall E M l1 l2, know_ok SEGS E M l2 -> Forall (kentry_ok SEGS E M) l1 -> know_ok SEGS E M (l1 ++ l2).
  Proof using. intros E M l1 l2 H2 H1. unfold know_ok. apply Forall_app. split; assumption. Qed.

  Ltac name_run HRn Rn :=
    lazymatch goal with H : regs_ok _ _ ?Rx |- srealizes _ (mkCfg (mkst ?Rx _ _ _) _) _ => rename H into HRn; rename Rx into Rn end;
    try lazymatch goal with H : log_flat _ _ |- _ => clear H end.

  Ltac cregs_tac G1 G2 G3 G4 :=
    split; [exact G1|]; split; [apply bv_eq; vm_compute; reflexivity|]; split; [lia|]; split; [exact G2|]; split; [exact G3 | exact G4].

  Ltac fixregs := try replace (Z_to_bv 5 (Z.of_N 3)) with (3%bv : reg) in * by (apply bv_eq; reflexivity);
                  try replace (Z_to_bv 5 (Z.of_N 4)) with (4%bv : reg) in * by (apply bv_eq; reflexivity);
                  try replace (Z_to_bv 5 (Z.of_N 8)) with (8%bv : reg) in * by (apply bv_eq; reflexivity);
                  try replace (Z_to_bv 5 (Z.of_N 9)) with (9%bv : reg) in * by (apply bv_eq; reflexivity).

  Lemma in_reg_list : forall (r : bv 5) (l : list (bv 5)),
    existsb (fun x => Z.eqb (bv_unsigned x) (bv_unsigned r)) l = true -> In r l.
  Proof using.
    intros r l; induction l as [|x l IH]; cbn; [discriminate|]. intros H. apply Bool.orb_true_iff in H.
    destruct H as [H|H]; [left; apply bv_eq; apply Z.eqb_eq; exact H | right; apply IH; exact H].
  Qed.

  Ltac keptQ KEPT G Q :=
    lazymatch type of G with getr _ ?r = _ => pose proof G as Q; rewrite <- (KEPT r) in Q by (clear; apply in_reg_list; reflexivity) end.

  Definition hdr_consts (w : pmw MI ST) : list (Z * Z) :=
    [(16, 0xffff); (24, w_p w + 152); (32, w_p w + 176); (40, 0x1010101); (48, 0xf0f0f0f); (56, 0x33333333);
     (64, 0x55555555); (72, 0x3fffc); (80, w_p w + 96); (88, 0xffffffffcccccccd); (96, 0x12973); (104, 0x121a9);
     (112, 0x11599); (120, 0x10758); (128, 0x140bc); (136, w_p w + 216)].
  Definition loop_mem (w : pmw MI ST) (M : mem) : Prop :=
    Forall (fun oc => fld SEGS M (w_sp w + fst oc) 8 (snd oc)) (hdr_consts w).
  Definition loop_regs (w : pmw MI ST) (R : bvmap 5 word) : Prop :=
    getr R 2%bv = Z_to_bv 64 (w_sp w) /\ getr R 3%bv = Z_to_bv 64 (ly_gp Ly.L) /\ getr R 4%bv = Z_to_bv 64 (ly_tp Ly.L) /\
    getr R 8%bv = Z_to_bv 64 (w_p w) /\ getr R 9%bv = Z_to_bv 64 (w_p w + 240) /\
    getr R 18%bv = Z_to_bv 64 (w_sp w + 220) /\ getr R 19%bv = Z_to_bv 64 (w_sp w + 234) /\ getr R 20%bv = Z_to_bv 64 (w_p w + 264) /\
    getr R 21%bv = Z_to_bv 64 (w_sp w + 218) /\ getr R 22%bv = Z_to_bv 64 (w_sp w + 200) /\ getr R 24%bv = Z_to_bv 64 1.

  Lemma pm_leafA : forall pc PRE POST, leafA SEGS Ly.L pc PRE POST ->
    forall (w : pmw MI ST) A M model c (fx : FPState) R (ret : Z) K,
    PMX w A M model c -> PRE R M -> getr R 1%bv = Z_to_bv 64 ret -> ret_ok (Z_to_bv 64 ret) ->
    (forall R', kept R R' -> POST R R' -> srealizes SEGS (cfg fx R' ret M model) K) ->
    srealizes SEGS (cfg fx R pc M model) K.
  Proof using AC MI ST.
    intros pc PRE POST STMT w A M model c fx R ret K X HP Hra Hret CONT.
    destruct (STMT fx R M (Z_to_bv 64 ret) (x_roc X) HP Hra Hret) as (R' & MSx & KP & PO).
    pose proof (x_ms X) as MS.
    eapply srz_msteps; [exact (ms_halt _ MS) | exact (ms_lazy _ MS) | exact MSx |]. exact (CONT R' KP PO).
  Qed.
  Definition pm_fixword := pm_leafA _ _ _ (cl_fixword _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).
  Definition pm_is_host_endian := pm_leafA _ _ _ (cl_is_host_endian _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL).

  Lemma fld_keep : forall (W : Z -> Prop) M M' a k v,
    stores_in W M M' -> fld SEGS M a k v -> 0 <= a -> a + Z.of_nat k < 2 ^ 64 ->
    (forall x, a <= x < a + Z.of_nat k -> ~ W x) -> fld SEGS M' a k v.
  Proof using.
    intros W M M' a k v SI F Ha Hk HW. eapply fld_agree; [exact Ha | exact Hk | exact F |].
    eapply stores_in_agree; [exact SI|]. intros x Hx. unfold zwin in Hx. split; [lia | apply HW; exact Hx].
  Qed.

  Lemma stores_in_of_frame_eq : forall (W : Z -> Prop) M M',
    frame_eq W M M' -> (forall a : word, M a <> None -> M' a <> None) -> stores_in W M M'.
  Proof using. intros W M M' FE D. split; [exact FE | exact D]. Qed.

  Lemma Z_to_bv64_add_mod : forall z, Z_to_bv 64 (z + 2 ^ 64) = Z_to_bv 64 z.
  Proof using.
    intros z. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 64) with (2 ^ 64). replace (z + 2 ^ 64) with (z + 1 * 2 ^ 64) by lia. apply Z.mod_add. lia.
  Qed.

  Lemma pm_binend : forall (w : pmw MI ST) A M model c (fx : FPState) R (ret : Z) K,
    PMX w A M model c -> w_words w <> 0 -> 1 <= w_n w ->
    fld SEGS M (w_sp w + 144) 8 (w_words w) -> fld SEGS M (w_sp w + 152) 8 (w_n w) ->
    getr R 10%bv = Z_to_bv 64 (w_sp w + 144) -> getr R 11%bv = Z_to_bv 64 (w_p w + 88) -> getr R 2%bv = Z_to_bv 64 (w_sp w) ->
    getr R 1%bv = Z_to_bv 64 ret -> ret_ok (Z_to_bv 64 ret) ->
    (forall R' M' (r e : Z), kept R R' -> getr R' 10%bv = Z_to_bv 64 r -> 0 <= r < 2 ^ 64 -> 0 <= e < 2 ^ 32 -> (r = 0 -> 0 <= e < 2) ->
        PMX w A M' model (set_scal c (c_widx c) (c_icount c) e (c_reqconv c)) ->
        CRep.agree_on (fun a => w_sp w <= a < w_sp0 w) M M' ->
        srealizes SEGS (cfg fx R' ret M' model) K) ->
    srealizes SEGS (cfg fx R (tc_binary_endianness tcS1) M model) K.
  Proof using AC MI ST G idesc odesc edesc generates_type is_ext_inst is_nonsemantic ds_rep CL.
    intros w A M model c fx R ret K X Hw Hn F144 F152 Ha0 Ha1 Hsp Hra Hret CONT.
    pose proof (x_geo X) as GEO. pose proof ac_bounds_lit as Hcv. pose proof (x_ms X) as MS.
    destruct GEO as (Gsp16 & Gceil & Gsphi & Gstk & Gpp & Gphi & Gp16 & Gc1 & Gc2 & Gap & Gn & Gw). unfold w_sp0, PM_FRAME, PARSER_SIZE in *.
    destruct (Gw Hw) as (W1 & W2 & W3 & W4 & W5). pose proof (x_scal X) as (S1 & S2 & S3 & S4).
    assert (WD : forall t n, w_sp w + 880 - w_STK w <= t -> t + n <= w_sp w + 880 -> mdef M t n).
    { intros t n Ht Hn' i Hi. pose proof (x_wdef X (t + i - (w_sp w + 880 - w_STK w)) ltac:(unfold w_sp0, PM_FRAME; lia)) as D.
      unfold w_sp0, PM_FRAME in D. replace (w_sp w + 880 - w_STK w + (t + i - (w_sp w + 880 - w_STK w))) with (t + i) in D by lia. exact D. }
    destruct (cl_binary_endianness _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CL fx R M (w_sp w + 144) (w_p w + 88) (w_words w) (w_n w) (w_sp w) (Z_to_bv 64 ret)
                (x_roc X) Ha0 Ha1 Hsp F144 ltac:(replace (w_sp w + 144 + 8) with (w_sp w + 152) by lia; exact F152) Hn W1 W3
                ltac:(eapply mdef_sub; [exact (x_wbuf X Hw) | lia | lia]) ltac:(lia) ltac:(lia)
                ltac:(eapply mdef_sub; [exact (x_pdef X) | lia | unfold PARSER_SIZE; lia]) ltac:(lia) ltac:(lia)
                ltac:(apply mod16_8; [exact Gsp16 | reflexivity]) W2 ltac:(apply mod16_4; [exact Gp16 | reflexivity])
                ltac:(intros a Ha; cbn [tc_lookup_stack tcS1] in Ha; unfold zwin in *; lia)
                ltac:(unfold stack_room; cbn [tc_lookup_stack tcS1]; apply (mdef_store_ok SEGS M _ 64); [apply WD; lia | lia | lia | lia])
                ltac:(cbn [tc_lookup_stack tcS1]; lia) ltac:(lia) Hra Hret)
      as (R' & M' & r & e & MSx & KP & Hr & Rr & Re & Fe & He2 & FE & DK).
    cbn [tc_lookup_stack tcS1] in FE.
    pose proof (stores_in_of_frame_eq _ M M' FE DK) as SI.
    eapply srz_msteps; [exact (ms_halt _ MS) | exact (ms_lazy _ MS) | exact MSx |].
    assert (Hr' : exists r', Z_to_bv 64 r = Z_to_bv 64 r' /\ 0 <= r' < 2 ^ 64 /\ (r' = 0 -> r = 0)).
    { destruct (Z.lt_ge_cases r 0); [exists (r + 2 ^ 64); rewrite Z_to_bv64_add_mod; split; [reflexivity | lia] | exists r; split; [reflexivity | lia]]. }
    destruct Hr' as (r' & Er & Rr' & Er0). rewrite Er in Hr.
    eapply (CONT R' M' r' e KP Hr Rr' Re ltac:(intros H0; apply He2, Er0, H0)).
    - eapply (pmx_stores SEGS Ly.L MI ST ly_img_low ly_rw_img ly_relro_img); [exact X | exact SI | | | | | | lia | lia | lia | exact S4].
      + intros a [Ha|Ha]; unfold zwin, scal_win, w_sp0, PM_FRAME, O_WIDX, O_FLAGS in *; [right; lia | left; lia].
      + eapply fld_keep; [exact SI | exact (x_widx X) | unfold O_WIDX; lia | unfold O_WIDX; cbn; lia | unfold O_WIDX, zwin; cbn; intros; lia].
      + eapply fld_keep; [exact SI | exact (x_icount X) | unfold O_ICOUNT; lia | unfold O_ICOUNT; cbn; lia | unfold O_ICOUNT, zwin; cbn; intros; lia].
      + unfold O_ENDIAN. exact Fe.
      + eapply fld_keep; [exact SI | exact (x_flags X) | unfold O_FLAGS; lia | unfold O_FLAGS; cbn; lia | unfold O_FLAGS, zwin; cbn; intros; lia].
    - eapply stores_in_agree; [exact SI|]. intros a Ha. unfold zwin. split; [lia | lia].
  Qed.

  Lemma ext_val_sx4 : forall v, 0 <= v < 2 ^ 32 -> ext_val true 0 4 (Z_to_bv 64 v) = Z_to_bv 64 (PrsNeeds.sx32 v).
  Proof using.
    intros v Hv. unfold ext_val, ext_Z. rewrite u64_of_Z by lia.
    change (2 ^ (8 * Z.of_nat 0)) with 1. rewrite Z.div_1_r. change (8 * Z.of_nat 4) with 32. rewrite Z.mod_small by lia.
    change (8 * N.of_nat 4)%N with 32%N. rewrite bv_swrap32_cases by lia. unfold PrsNeeds.sx32.
    destruct (Z.ltb_spec v (2 ^ 31)); destruct (Z.ltb_spec v 2147483648); try lia; [reflexivity|].
    rewrite <- (Z_to_bv64_add_mod (v - 2 ^ 32)). f_equal. lia.
  Qed.
  Lemma sxw_sx32 : forall v, 0 <= v < 2 ^ 32 -> sxw v = Z_to_bv 64 (PrsNeeds.sx32 v).
  Proof using.
    intros v Hv. unfold sxw. rewrite bv_swrap32_cases by lia. unfold PrsNeeds.sx32.
    destruct (Z.ltb_spec v (2 ^ 31)); destruct (Z.ltb_spec v 2147483648); try lia; [reflexivity|].
    rewrite <- (Z_to_bv64_add_mod (v - 2 ^ 32)). f_equal. lia.
  Qed.

  Lemma mdef_cell4 : forall M a, mdef M a 4 -> 0 <= a -> a + 4 < 2 ^ 64 -> exists v, cell4 SEGS M a v.
  Proof using.
    intros M a HD Ha Ha4. destruct (mdef_rdn SEGS M a 4 0 4 HD Ha Ha4 ltac:(lia) ltac:(cbn; lia)) as (bs & Hbs & Hlen).
    rewrite Z.add_0_r in Hbs. exists (bytes_le_to_Z bs).
    pose proof (bytes_le_to_Z_bound bs) as Hb. rewrite Hlen in Hb. pose proof (bytes_le_to_Z_nonneg bs) as Hb0. cbn in Hb.
    split; [cbn; lia|]. change (N.to_nat 4) with 4%nat. rewrite Hbs. f_equal.
    rewrite <- (sw_bytes_LWv bs Hlen) at 1. unfold LWv, v_lw. rewrite u64_of_Z by lia.
    change 32%N with (8 * 4)%N. apply (word_to_le_bytes_swrap 4). cbn; lia.
  Qed.

  Lemma zbv_add_nat : forall a (k : nat), 0 <= a -> a + Z.of_nat k < 2 ^ 64 ->
  (Z_to_bv 64 a + nat_to_word k)%bv = Z_to_bv 64 (a + Z.of_nat k).
Proof using.
  intros a k Ha Hk. apply bv_eq. unfold nat_to_word. rewrite bv_add_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
  rewrite (Z.mod_small a), (Z.mod_small (Z.of_nat k)), Z.mod_small by lia. reflexivity.
Qed.
  Lemma flags_store : forall M p f b,
  CRep.fld SEGS M (p + 92) 2 f -> (f = 0 \/ f = 1) -> (b = 0 \/ b = 1) -> 0 <= p -> p + 94 < 2 ^ 64 ->
  CRep.fld SEGS (wbytes M (Z_to_bv 64 (p + 92)) (word_to_le_bytes 1 (Z_to_bv 64 b))) (p + 92) 2 b.
Proof using.
  intros M p f b F Hf Hb Hp Hp'. unfold CRep.fld in *.
  pose proof (rdn_skipn SEGS M 2 _ _ 1 F ltac:(lia)) as F1. rewrite zbv_add_nat in F1 by lia. cbn [Nat.sub] in F1.
  change 2%nat with (1 + 1)%nat.
  rewrite (rdn_app SEGS _ 1 1 _ (word_to_le_bytes 1 (Z_to_bv 64 b)) (skipn 1 (word_to_le_bytes 2 (Z_to_bv 64 f)))).
  - f_equal. destruct Hf as [-> | ->]; destruct Hb as [-> | ->]; reflexivity.
  - apply rdn_wbytes_self. rewrite length_N_to_le_bytes, u64_of_Z by lia. cbn. lia.
  - rewrite zbv_add_nat by lia. rewrite rdn_wbytes_out_Z by (rewrite length_N_to_le_bytes; cbn; lia). exact F1.
Qed.

  Lemma w_xor1 : forall r, (r = 0 \/ r = 1) -> alu64 ALU_XOR (Z_to_bv 64 r) (Z_to_bv 64 1) = Z_to_bv 64 (1 - r).
  Proof using. intros r [-> | ->]; apply bv_eq; vm_compute; reflexivity. Qed.
  Lemma land_range : forall a b, 0 <= a -> 0 <= b -> 0 <= Z.land a b <= a.
  Proof using. intros a b Ha Hb. split; [apply Z.land_nonneg; lia | apply land_le_l; lia]. Qed.

  Lemma ver_br1 : forall r, 0 <= r < 2 ^ 64 ->
  branch_taken BC_EQ (alu64 ALU_AND (Z_to_bv 64 r) (Z_to_bv 64 18446744073692774655)) (Z_to_bv 64 0)
  = (Z.land r 18446744073692774655 =? 0).
  Proof using.
  intros r Hr. pose proof (land_range r 18446744073692774655 ltac:(lia) ltac:(lia)).
  rewrite w_and by lia. rewrite br_eq by lia. reflexivity.
  Qed.

  Lemma ver_br2 : forall r, 0 <= r < 2 ^ 32 ->
  branch_taken BC_LTU (Z_to_bv 64 18446744073709550078)
     (sext 64 (alu32 ALU_ADD (low32 (Z_to_bv 64 r)) (low32 (Z_to_bv 64 18446744073709484543))))
  = ((65536 <=? r) && (r <=? 67072)).
  Proof using.
  intros r Hr. rewrite w_addw. unfold v_addw. rewrite !u64_of_Z by lia.
  replace (r + 18446744073709484543) with ((r - 67073) + (2 ^ 32) * 2 ^ 32) by lia. rewrite swrap32_shift.
  destruct (Z.lt_ge_cases r 67073) as [Hlt|Hge].
  - rewrite <- (swrap32_shift (r - 67073) 1). replace (r - 67073 + 1 * 2 ^ 32) with (r + 4294900223) by lia.
    rewrite bv_swrap32_cases by lia. destruct (Z.ltb_spec (r + 4294900223) (2 ^ 31)); [lia|].
    rewrite <- (Z_to_bv64_add_mod (r + 4294900223 - 2 ^ 32)). rewrite br_ltu by lia.
    destruct (Z.leb_spec 65536 r); destruct (Z.leb_spec r 67072); cbn [andb]; first [apply Z.ltb_lt; lia | apply Z.ltb_ge; lia].
  - rewrite bv_swrap32_cases by lia. destruct (Z.ltb_spec (r - 67073) (2 ^ 31)).
    + rewrite br_ltu by lia.
      destruct (Z.leb_spec 65536 r); destruct (Z.leb_spec r 67072); cbn [andb]; first [apply Z.ltb_lt; lia | apply Z.ltb_ge; lia].
    + rewrite <- (Z_to_bv64_add_mod (r - 67073 - 2 ^ 32)). rewrite br_ltu by lia.
      destruct (Z.leb_spec 65536 r); destruct (Z.leb_spec r 67072); cbn [andb]; first [apply Z.ltb_lt; lia | apply Z.ltb_ge; lia].
  Qed.

  Lemma land_sx32_hi : forall r, 2 ^ 31 <= r < 2 ^ 32 -> Z.land (PrsNeeds.sx32 r) 18446744073692774655 <> 0.
  Proof using.
    intros r Hr. unfold PrsNeeds.sx32. destruct (Z.ltb_spec r (2 ^ 31)); [lia|]. intros H0.
    assert (T : Z.testbit (Z.land (r + 2 ^ 64 - 2 ^ 32) 18446744073692774655) 63 = true).
    { rewrite Z.land_spec. apply andb_true_intro. split; [| reflexivity].
      apply Z.testbit_true; [lia|]. replace ((r + 2 ^ 64 - 2 ^ 32) / 2 ^ 63) with 1; [reflexivity|].
      apply (Z.div_unique _ _ _ (r + 2 ^ 64 - 2 ^ 32 - 2 ^ 63)); [left; lia | lia]. }
    rewrite H0 in T. cbn in T. discriminate T.
  Qed.
  Lemma sx32_range : forall r, 0 <= r < 2 ^ 32 -> 0 <= PrsNeeds.sx32 r < 2 ^ 64.
  Proof using. intros r Hr. unfold PrsNeeds.sx32. destruct (Z.ltb_spec r (2 ^ 31)); lia. Qed.

  Lemma sx32_small : forall x, 0 <= x < 2 ^ 31 -> PrsNeeds.sx32 x = x.
  Proof using. intros x Hx. unfold PrsNeeds.sx32. destruct (Z.ltb_spec x (2 ^ 31)); lia. Qed.
End PM.

Ltac postrun := evs; rewrite ?v_addi_Z by lia; rewrite ?Z.add_0_r, ?Z.add_opp_r.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Ltac w2blen := rewrite ?length_N_to_le_bytes.
Ltac rdback := unfold CRep.fld; repeat (rewrite rdn_wbytes_out_Z by (w2blen; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia));
               first [ apply rdn_wbytes_self; w2blen; rewrite u64_of_Z by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia
                     |
                       rewrite rdn_wbytes_prefix; [ reflexivity | w2blen; rewrite u64_of_Z by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | w2blen; lia ]
                     | idtac ].
Ltac stin := repeat (first [ apply stores_in_refl
                           | eapply stores_in_wbytes_more; [ | lia | w2blen; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia
                                                            | w2blen; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unfold zwin; intros; lia ] ]).
Ltac pm_seed R w c extra :=
  pose (E := Eseed R (Z_to_bv 64 (w_sp w) :: Z_to_bv 64 (w_p w) :: Z_to_bv 64 (w_words w) :: Z_to_bv 64 (w_n w) ::
                      Z_to_bv 64 (w_cons w) :: Z_to_bv 64 (c_icount c) :: Z_to_bv 64 (c_widx c) :: extra)).
Ltac seedHR_ HR E l R :=
  assert (HR : regs_ok E (srs sr_id l) R)
    by (apply regs_ok_srs; [apply regs_ok_seed|]; repeat constructor; cbn [fst snd]; try (intros XX; discriminate XX); evs;
        first [assumption | reflexivity | rewrite w_add by lia; assumption]).
Tactic Notation "seedHR" ident(HR) constr(E) uconstr(l) constr(R) :=
  let l' := constr:(l : list (reg * expr)) in seedHR_ HR E l' R.
Ltac seedHK HK w A M model c E X :=
  assert (HK : know_ok SEGS E M pm_kn) by (apply (pmx_know w A M model c E X); evs; reflexivity).
Ltac name_run HRn Rn :=
  lazymatch goal with H : regs_ok _ _ ?Rx |- srealizes _ (mkCfg (mkst ?Rx _ _ _) _) _ => rename H into HRn; rename Rx into Rn end;
  try lazymatch goal with H : log_flat _ _ |- _ => clear H end.
Ltac cregs_tac G1 G2 G3 G4 :=
  split; [exact G1|]; split; [apply bv_eq; vm_compute; reflexivity|]; split; [lia|]; split; [exact G2|]; split; [exact G3 | exact G4].
Ltac fixregs := try replace (Z_to_bv 5 (Z.of_N 3)) with (3%bv : reg) in * by (apply bv_eq; reflexivity);
                try replace (Z_to_bv 5 (Z.of_N 4)) with (4%bv : reg) in * by (apply bv_eq; reflexivity);
                try replace (Z_to_bv 5 (Z.of_N 8)) with (8%bv : reg) in * by (apply bv_eq; reflexivity);
                try replace (Z_to_bv 5 (Z.of_N 9)) with (9%bv : reg) in * by (apply bv_eq; reflexivity).
Ltac keptQ KEPT G Q :=
  lazymatch type of G with getr _ ?r = _ => pose proof G as Q; rewrite <- (KEPT r) in Q by (clear; apply in_reg_list; reflexivity) end.
