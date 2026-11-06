(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec ShapeAlg SpinAlg CatExec AgentLib AxSymExec3K AxSymExec3SoundK AsanPlanCoreK AsanPlanK AsanPlanSoundK AsanInitK
  Pm5DefsK Pm5PlanImagesK Pm5StartupK HandoffBridgeK HandoffBInvK HandoffRolesK Pm5HandoffK Pm5HSK_0 Pm5HSK_1 Pm5MainTableK Pm5HandoffInstK Pm5DrvEntryK Pm5StartupFinalK.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import SymExec2 SymExec2Sound SymRun SymDrive HeapIface HeapIfaceA PmHeapIfaceA HeapIfaceANull IcptIfaceA PmIcptIfaceA Pm5IcptLayout PmIcptDrvA LibIface PmLibIfaceA
  ArtRuns ArtBridge Pm5ArtInv Pm5ArtFsInv Pm5ArtHandoffK Pm5ArtHandoffInstK Pm5StkShK As0DrvKitA Pm5DrvEntry Pm5DrvEntryInst Pm5Drv_defs Pm5DrvLib Pm5DrvRead Pm5DrvStdio Pm5DrvLibL
  Pm5DrvC Pm5DrvD PmLibIfaceAW Pm5DrvLibLW Pm5MainPhaseA HeapIfaceN Pm5ArtIfaceInstN.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import ShapeLaws Spec BigintSpec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

#[local] Existing Instance PropExec.fx0.

(* [comment removed for export] *)
Definition phi_okD (PHI : list byte -> Prop) (path : list byte) (fs : Fs.Fs) : Prop :=
  (length path < 4096)%nat -> path <> [] -> path <> dot_path ->
  forall data, fs_lookup fs path = Some data -> Z.of_nat (length data) < 67108864 -> (6 <= length data)%nat -> 6 + CFGA data <= Z.of_nat (length data) ->
  PHI (payloadA data).

(* [comment removed for export] *)
Definition lib_ok_stmtW (scfg : SpuriousCfg) (L : asan_layout) (LX : asan_layout_x) (C : asan_statics_cells) (IL : icpt_layout) (ILX : icpt_layout_x) (Lay : lib_layoutA)
    (LSt : asan_run -> lib_statics) (PHI : list byte -> Prop) : Prop :=
  forall ar HI, pm_asan_iface_ok L LX ar C scfg HI -> pm_aicpt_ok L ar IL ILX scfg HI (aannotate_spec L ar scfg HI (iclx_annotate ILX) 4096) -> afree_null_spec L ar scfg HI ->
    Pm5ArtIfaceInstN.pm_instN L ar IL scfg HI ->
    lla_L Lay = L /\ lib_iface_okDW Lay ar scfg HI (LSt ar) PHI.
(* [comment removed for export] *)
Definition instN_ok_stmt (scfg : SpuriousCfg) (L : asan_layout) (IL : icpt_layout) (BUDGET : Z) : Prop :=
  forall MAPS0 RESV0 NOACC0 BASE rn,
    bridge_static ASEGS0 MAPS0 RESV0 NOACC0 (art_RES rn) (rn_HI rn) BUDGET Pm5ArtInv.LENMAX Pm5ArtInv.KMAX ->        (* [comment removed for export] *)
    art_run_ok rn -> rn_tp rn = 0x6a1890 -> rn_key rn = 0 -> rn_tsd rn = 0x6c2d48 -> rn_loff rn = 0x10 ->
    Pm5ArtIfaceInstN.pm_instN L (rn_ar rn) IL scfg (HIA BUDGET MAPS0 RESV0 NOACC0 BASE rn).

(* [comment removed for export] *)
Definition drv_main_stmtW (scfg : SpuriousCfg) (L : asan_layout) (C : asan_statics_cells) (IL : icpt_layout) (Lay : lib_layoutA) (LSt : asan_run -> lib_statics) (B0 : Z) (PHI : list byte -> Prop) : Prop :=   (* [comment removed for export] *)
  sc_alloc scfg = false -> sc_fs scfg = true -> drv_consts_stmt L C IL ->
  forall (sp : word) (a0s path : list byte) (envp : list (list byte)) (fs : Fs.Fs),
    valid_sp sp -> valid_argv [a0s; path] -> valid_envp envp -> valid_fs fs -> phi_okD PHI path fs ->
  forall (ar : asan_run) (HI : asan_iface) (p0 p1 can tid : word) (A0 : list (Z * Z)) (cr0 : credit)
         (R : bvmap 5 word) (M0 : word -> option byte) (model : Model),
    asan_iface_ok L ar C scfg HI -> afree_null_spec L ar scfg HI -> aicpt_ok L ar IL scfg HI -> lib_iface_okDW Lay ar scfg HI (LSt ar) PHI -> drv_layoutA L ar IL sp ->
    SX2S.regs_ok (env_mainA sp p0 p1 can tid R) sr_mainA R ->
    SX2S.know_ok ASEGS (env_mainA sp p0 p1 can tid R) (mrestrict (ahid A0 model) M0) kn_mainA ->
    auxv_atA sp p0 M0 ->                                                     (* [comment removed for export] *)
    dinv ar HI sp M0 [] [] cr0 A0 M0 model ->
    defined M0 (bv_unsigned sp) (ar_stack_top ar - bv_unsigned sp) ->
    m_fds model = APSK.fds_std -> m_fs model = fs ->
    rdn ASEGS (mrestrict (ahid A0 model) M0) p1 (length path + 1) = Some (path ++ [Z_to_bv 8 0]) ->
    bv_unsigned sp <= bv_unsigned p1 /\ bv_unsigned p1 + Z.of_nat (length path) + 1 + 16 <= 2 ^ 47 ->
    cr0 = (8192, B0) ->
    (* [comment removed for export] *)
    defined M0 (bv_unsigned p1) (Z.of_nat (length path) + 1 + 16) ->
    shadow_allowed A0 (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) ->
    srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0xb0980) M0 (seg_rom ASEGS)) model) (spec [a0s; path] fs).

Section MainPhaseW.
  Variable scfg : SpuriousCfg.
  Hypothesis Halloc : sc_alloc scfg = false.
  Hypothesis Hfs : sc_fs scfg = true.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variable L : asan_layout.
  Variable C : asan_statics_cells.
  Variable IL : icpt_layout.
  Variable LX : asan_layout_x.
  Variable ILX : icpt_layout_x.
  Variable Lay : lib_layoutA.
  Variable LSt : asan_run -> lib_statics.
  Variable BUDGET : Z.
  Hypothesis BUD_ge : 2 ^ 34 <= BUDGET.
  Hypothesis BUD_hi : BUDGET <= 2 ^ 39 - 2 ^ 35.

  Hypothesis INST_OK : inst_ok_stmt scfg L C BUDGET.
  Hypothesis INSTN_OK : instN_ok_stmt scfg L IL BUDGET.   (* [comment removed for export] *)
  Hypothesis FREE_NULL : free_null_stmt scfg L BUDGET.
  Hypothesis H4E : h4e_stmt BUDGET.
  Hypothesis ICPT_OK : icpt_ok_stmt scfg L IL ILX BUDGET.
  Hypothesis SFREE_OK : sfree_ok_stmt scfg L LX BUDGET.
  Variable PHI : list byte -> Prop.
  Hypothesis LIB_OK : lib_ok_stmtW scfg L LX C IL ILX Lay LSt PHI.
  Hypothesis DLA_OK : dla_ok_stmt scfg L C IL.
  Hypothesis DRV_CONSTS : drv_consts_stmt L C IL.
  Hypothesis DRV_MAIN : drv_main_stmtW scfg L C IL Lay LSt BUDGET PHI.
  Hypothesis USAGE : usage_stmt scfg.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variable sp brk0 mbase : word. Variable rdraw : EntryDraw. Variables argv envp : list (list byte). Variable fs : Fs.Fs.
  Variable stdin : InputStream. Variables uid gid hw : word. Variable groups : list word. Variable net : NetQueue.
  Variables nofile sigmask : word. Variable abrt : bool.
  (* [comment removed for export] *)
  Variable ifs : Fs.Fs. Variable urnd : InputStream. Variable tmp0 : Fs.Fs.
  Hypothesis Hsp : valid_sp sp. Hypothesis Hbrk : valid_brk ASEGS0 brk0.
  Hypothesis Hva : valid_argv argv. Hypothesis Hve : valid_envp envp. Hypothesis Hfit : entry_stack_fits sp argv envp.
  Hypothesis Huid : valid_id uid. Hypothesis Hhw : valid_hwcap hw. Hypothesis Hvfs : valid_fs fs.
  Hypothesis Hseed : fs_seed_tmp ifs tmp0 = fs.
  (* [comment removed for export] *)
  Hypothesis PHIOK : forall a0s path, argv = [a0s; path] -> phi_okD PHI path fs.
  #[local] Notation SINV := (SINV0 APH0 sp rdraw brk0 argv envp uid hw).
  #[local] Notation argH := (argH0 APH0 sp rdraw argv envp uid hw).
  #[local] Notation CSOK := (APSK.cs_ok ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs).
  #[local] Notation usp := (bv_unsigned sp).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma mp_bud : 0 <= BUDGET /\ 0 <= Pm5ArtInv.KMAX /\ 0 <= Pm5ArtInv.LENMAX < 2 ^ 62.
  Proof. unfold Pm5ArtInv.KMAX, Pm5ArtInv.LENMAX. lia. Qed.
  Lemma mp_gap : AsanCeil.bottomup_floor + Pm5ArtInv.LENMAX + (17729665388544 + BUDGET) + (21 + Pm5ArtInv.KMAX) * (Pm5ArtInv.LENMAX + 4095) <= AsanCeil.alloc_ceiling.
  Proof. unfold Pm5ArtInv.KMAX, Pm5ArtInv.LENMAX, AsanCeil.bottomup_floor, AsanCeil.alloc_ceiling. lia. Qed.
  Lemma mp_gap_h : forall h, (h < 2)%nat ->
    AsanCeil.bottomup_floor + Pm5ArtInv.LENMAX + (APK.a_totsz (HSA h) + BUDGET)
    + (Z.of_nat (length (segments_reserved ASEGS0) + length (APK.a_maps (HSA h))) + Pm5ArtInv.KMAX) * (Pm5ArtInv.LENMAX + 4095) <= AsanCeil.alloc_ceiling.
  Proof.
    intros h Hh. destruct (HSA_numbers h Hh) as (N1 & N2 & N3 & N4). rewrite N4, asan0_res_eq. cbn [length Nat.add]. change (Z.of_nat 21) with 21.
    unfold Pm5ArtInv.KMAX, Pm5ArtInv.LENMAX, AsanCeil.bottomup_floor, AsanCeil.alloc_ceiling. lia.
  Qed.

  Lemma HSA_pc : forall h, (h < 2)%nat -> APK.pc (HSA h) = 0xb0980.
  Proof. intros [|[|h]] H; [reflexivity | reflexivity | lia]. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem as0_main_phase : APSK.holes_stmt ASEGS0 scfg ASAN0 AsanInitK.LIMIT HS_as0 SINV argH (HOLES (fun fs' => spec argv fs')) fs.
  Proof.
    intros h ch Hh E R FULL model HC.
    assert (Hh2 : (h < 2)%nat) by (destruct h as [|[|h]]; [lia | lia | discriminate Hh]).
    rewrite (HSA_some h Hh2) in Hh. injection Hh as <-.
    assert (EFS : m_fs model = fs).
    { exact (proj2 (ent_model sp brk0 rdraw argv envp uid hw fs (HSA h) (drv_chk_HSA h Hh2) E R FULL model HC)). }
    unfold HOLES. rewrite EFS.
    destruct (Nat.eq_dec (length argv) 2) as [Hargc|Hargc]; [|exact (USAGE sp brk0 rdraw argv envp uid hw fs Hsp Hva Hve Hfit Hvfs h Hh2 E R FULL model HC Hargc)].
    destruct argv as [|a0s [|path [|x l]]] eqn:Hargv; try discriminate Hargc. clear Hargc.
    (* [comment removed for export] *)
    set (cs := HSA h). set (rn := as0_rn E cs). set (ar := as0_ar E cs).
    set (MAPS0 := vm_maps (m_vmmaps model)). set (RESV0 := segments_reserved ASEGS0). set (NOACC0 := vm_noaccess (m_vmmaps model)).
    pose proof (as0_art_handoff_h sp brk0 rdraw [a0s; path] envp uid hw fs Hsp Hva Hve Hfit BUDGET BUD_ge BUD_hi h Hh2 E R FULL model HC) as HT.
    pose proof (as0_handoff_static sp brk0 rdraw [a0s; path] envp uid hw fs BUDGET Pm5ArtInv.LENMAX Pm5ArtInv.KMAX mp_bud mp_gap h Hh2 E R FULL model HC) as BS.
    rewrite (as0_RES_art h Hh2 E) in BS. fold cs rn in BS.
    pose proof (sp0_val sp brk0 rdraw [a0s; path] envp uid hw fs Hsp Hva Hve Hfit BUDGET Pm5ArtInv.LENMAX Pm5ArtInv.KMAX (HSA h) (drv_chk_HSA h Hh2) (mp_gap_h h Hh2)
                  E R FULL model HC) as SPV.
    pose proof HT as (REP & _ & _ & _ & CLI & _). destruct REP as (ROK & _).
    assert (HIok : asan_iface_ok L ar C scfg (HIA BUDGET MAPS0 RESV0 NOACC0 (as0_BASEx cs E) rn)).
    { apply (INST_OK MAPS0 RESV0 NOACC0 (as0_BASEx cs E) rn); [exact BS | exact ROK | reflexivity | reflexivity | reflexivity | reflexivity]. }
    assert (FNok : afree_null_spec L ar scfg (HIA BUDGET MAPS0 RESV0 NOACC0 (as0_BASEx cs E) rn)).
    { apply (FREE_NULL MAPS0 RESV0 NOACC0 (as0_BASEx cs E) rn); [exact BS | exact ROK | reflexivity | reflexivity | reflexivity | reflexivity]. }
    assert (INok : Pm5ArtIfaceInstN.pm_instN L ar IL scfg (HIA BUDGET MAPS0 RESV0 NOACC0 (as0_BASEx cs E) rn)).
    { apply (INSTN_OK MAPS0 RESV0 NOACC0 (as0_BASEx cs E) rn); [exact BS | exact ROK | reflexivity | reflexivity | reflexivity | reflexivity]. }
    set (HI := HIA BUDGET MAPS0 RESV0 NOACC0 (as0_BASEx cs E) rn) in *.
    pose proof (H4E _ _ _ _ _ _ _ _ _ _ _ _ HT) as RI. fold HI in RI.
    assert (SPT : ar_sptop ar = usp) by exact SPV.
    assert (ICokX : pm_aicpt_ok L ar IL ILX scfg HI (aannotate_spec L ar scfg HI (iclx_annotate ILX) 4096)).
    { apply (ICPT_OK MAPS0 RESV0 NOACC0 (as0_BASEx cs E) rn); [exact BS | exact ROK | reflexivity | reflexivity | reflexivity | reflexivity]. }
    assert (ICok : aicpt_ok L ar IL scfg HI) by exact (aicpt_of_pm L ar IL scfg HI ILX _ ICokX).
    assert (SFok : astack_free_spec L ar scfg HI (hlx_stack_free LX 5) (hlx_sfree_pat LX) 5).
    { apply (SFREE_OK MAPS0 RESV0 NOACC0 (as0_BASEx cs E) rn); [exact BS | exact ROK | reflexivity | reflexivity | reflexivity | reflexivity]. }
    destruct (LIB_OK ar HI (PAIOK _ _ _ _ _ _ HIok SFok) ICokX FNok INok) as (LayL & LIok). pose proof (DLA_OK ar HI sp HIok SPT) as DL.
    (* [comment removed for export] *)
    pose proof (as0_EXTRA_wf cs E) as XWF.
    assert (XBL : 16515072 + 2461542400 + A_bytes (as0_EXTRA cs E) + BUDGET <= AsanInitK.LIMIT).
    { unfold as0_EXTRA. cbn [A_bytes fst snd]. unfold AsanInitK.LIMIT, target_alloc_limit. lia. }
    destruct (as0_main_entry sp brk0 rdraw a0s path envp uid hw fs Hsp Hva Hve Hfit BUDGET Pm5ArtInv.LENMAX Pm5ArtInv.KMAX mp_bud (as0_EXTRA cs E) XWF XBL mp_gap
                h Hh2 E R FULL model HC) as (can & tid & HR & HK & LZ & FDS & _ & STR).
    destruct (as0_main_auxv sp brk0 rdraw a0s path envp uid hw fs Hsp Hva Hve Hfit BUDGET Pm5ArtInv.LENMAX Pm5ArtInv.KMAX mp_bud (as0_EXTRA cs E) XBL mp_gap
                h Hh2 E R FULL model HC) as (uidz & rnd & hwz & AUXW & AUXU & AUXH & AUXR1 & AUXR2).
    destruct LZ as (_ & _ & _ & MI & HALT).
    destruct CLI as (_ & _ & _ & _ & S1 & S2 & S3 & S4 & S5 & _).
    cbn [as0_rn rn_ar as0_ar ar_stack_top ar_stack_bottom ar_sptop] in S1, S2, S3, S4, S5.
    assert (SDEF : defined FULL usp (ar_stack_top ar - usp)).
    { apply (as0_main_stack_defined sp brk0 rdraw a0s path envp uid hw fs Hsp Hva Hve Hfit BUDGET Pm5ArtInv.LENMAX Pm5ArtInv.KMAX mp_bud (as0_EXTRA cs E) XBL mp_gap
               h Hh2 E R FULL model HC); unfold ar, cs; cbn [as0_ar ar_stack_top]; rewrite SPV in *.
      - rewrite S5. rewrite <- Z.add_mod_idemp_l by lia. rewrite S3. reflexivity.
      - lia. }
    assert (DI : dinv ar HI sp FULL [] [] (8192, BUDGET) (as0_A0x cs E) FULL model).
    { apply DINV; [exact RI | exact MI | exact HALT | reflexivity | | |].
      intros x Hx. apply (as0_stksh_main sp brk0 rdraw [a0s; path] envp uid hw fs Hsp Hva Hve Hfit h Hh2 E R FULL model HC).   (* [comment removed for export] *) unfold STKTOP, ar, cs in Hx. cbn [as0_ar ar_sptop ar_stack_top] in Hx. rewrite SPV in Hx. exact Hx.
      intros x Hx. apply (as0_stksh_main_hi sp brk0 rdraw [a0s; path] envp uid hw fs Hsp Hva Hve Hfit h Hh2 E R FULL model HC). unfold ahl_ceil, ar, cs in Hx. cbn [as0_ar ar_sptop] in Hx. rewrite SPV in Hx. exact Hx.
      intros b []. }
    destruct (STR 1%nat ltac:(lia)) as (STR1 & PV1 & PH1). cbn [nth] in STR1, PH1. unfold total_arg_bytes_nat in PV1. cbn [firstn fold_right] in PV1.
    assert (HB : 0 <= Z.of_nat (length envp) <= 256 /\ 0 <= Z.of_nat (length a0s) <= 131071).
    { pose proof Hve as [Hle _]. pose proof Hva as (_ & _ & Hfa & _). inversion Hfa as [|x l Hx _]; subst. lia. }
    assert (SR : 0x7fff80000000 <= usp <= 2 ^ 47) by (destruct Hsp as (H1 & H2 & H3); unfold sp_window_lo, sp_window_hi in H1, H2; lia).
    assert (PE : Z_to_bv 64 (usp + 8 * Z.of_nat (length envp) + Z.of_nat (length a0s) + 201) = cat_argv_ptr sp [a0s; path] envp 1).
    { apply bv_eq. rewrite PV1, Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia. lia. }
    unfold APSK.cfg_of, cs. rewrite (HSA_pc h Hh2). fold cs.
    destruct (STR 0%nat ltac:(lia)) as (_ & PV0 & PH0). cbn [nth] in PH0. unfold total_arg_bytes_nat in PV0. cbn [firstn fold_right] in PV0.
    assert (SA16 : usp mod 16 = 0) by (destruct Hsp as (_ & _ & H3); exact H3).
    assert (UP0 : bv_unsigned (Z_to_bv 64 (usp + 8 * Z.of_nat (length envp) + 200)) = usp + 8 * Z.of_nat (length envp) + 200) by (rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with (2 ^ 64); apply Z.mod_small; lia).
    refine (DRV_MAIN Halloc Hfs DRV_CONSTS sp a0s path envp fs Hsp Hva Hve Hvfs (PHIOK a0s path eq_refl) ar HI _ _ can tid (as0_A0x cs E) (8192, BUDGET) R FULL model HIok FNok ICok LIok DL HR HK _ DI SDEF FDS EFS _ _ eq_refl _ _).
    - exists uidz, rnd, hwz. rewrite UP0.
      split; [intros j Hj; replace (usp + 8 * Z.of_nat (length envp) + 200 - 160 + 8 * Z.of_nat j) with (usp + 8 * Z.of_nat (length envp) + 40 + 8 * Z.of_nat j) by ring; exact (AUXW j Hj)|].
      repeat split; try lia.
      pose proof (Z.div_mod usp 16 ltac:(lia)) as DM. rewrite SA16 in DM.
      replace (usp + 8 * Z.of_nat (length envp) + 200) with ((2 * (usp / 16) + Z.of_nat (length envp) + 25) * 8) by lia. apply Z.mod_mul. lia.
    - rewrite PE. exact STR1.
    - rewrite PE, PV1. rewrite PV1 in PH1. lia.
    - rewrite PE. intros i Hi.
      exact (as0_main_str_defined sp brk0 rdraw a0s path envp uid hw fs Hsp Hva Hve Hfit BUDGET Pm5ArtInv.LENMAX Pm5ArtInv.KMAX mp_bud (as0_EXTRA cs E) XBL mp_gap h Hh2 E R FULL model HC 1%nat ltac:(lia) i Hi).
    - pose proof HT as (_ & _ & _ & _ & CLI' & _). destruct CLI' as (_ & _ & SAH & _). exact SAH.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem as0_realizes_spec_run :
    srealizes ASEGS0 scfg (init_config ASEGS0 AsanUbsan.M.init_pc APH0 sp brk0 mbase rdraw AsanInitK.LIMIT
                                 (AsanInitK.inp argv envp ifs stdin uid gid hw groups net nofile sigmask abrt urnd tmp0))
              (spec argv fs).
  Proof.
    apply (as0_startup_closed scfg Halloc sp brk0 mbase rdraw argv envp fs stdin uid gid hw groups net nofile sigmask abrt ifs urnd tmp0
             Hsp Hbrk Hva Hve Hfit Huid Hhw Hseed (fun fs' => spec argv fs')).
    - intros fs'. apply spec_has_nil.
    - exact as0_main_phase.
  Qed.
End MainPhaseW.
