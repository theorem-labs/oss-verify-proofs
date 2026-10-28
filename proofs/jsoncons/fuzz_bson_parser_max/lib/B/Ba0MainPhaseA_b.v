(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import AsanAcct.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec ShapeAlg SpinAlg CatExec AgentLib AxSymExec3K AxSymExec3SoundK AsanPlanCoreK AsanPlanK AsanPlanSoundK AsanInitK.
  From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0DefsK_b Ba0PlanImagesK_b Ba0StartupK_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HandoffBridgeK HandoffBInvK HandoffRolesK. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0HandoffK_b Ba0HSK_0_b Ba0HSK_1_b Ba0MainTableK_b Ba0HandoffInstK_b Ba0DrvEntryK_b Ba0StartupFinalK_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import SymExec2 SymExec2Sound SymRun SymDrive HeapIface HeapIfaceA HeapIfaceABx HeapIfaceANull. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import LibIface LibIfaceAB
  ArtRuns ArtBridge. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatInv_b BatFsInv_b Ba0ArtHandoffK_b Ba0ArtHandoffInstK_b Ba0StkShK_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import As0DrvKitA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0DrvEntry_b Ba0DrvEntryInst_b Ba0Drv_defs_b Ba0DrvLib_b Ba0DrvRead_b Ba0DrvStdio_b Ba0ExitCells_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ShapeLaws Spec BigintSpec.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import HeapIfaceABxI_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import StrictOfB. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import StrictOfBI_b.      (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnAImgGap_b.      (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Import ListNotations.
Open Scope Z_scope.

#[local] Existing Instance PropExec.fx0.

(* [comment removed for export] *)
Lemma spec_has_nil : forall argv fs, spec argv fs [].
Proof.
  intros argv fs. unfold spec.
  assert (D : forall m f, t_die m f []) by (intros; unfold t_die; apply ShapeAlg.t_emit_has_nil).
  destruct argv as [|a0 [|p [|x l]]]; try apply D.
  destruct (4096 <=? length p)%nat; [apply D|]. destruct (list_byte_eqb p []); [apply D|].
  destruct (list_byte_eqb p dot_path); [apply ShapeLaws.t_alt2_has_nil_l; apply D|].
  destruct (fs_lookup fs p); [apply ShapeLaws.t_alt2_has_nil_l; apply D | apply D].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition HIR (BUDGET : Z) (MAPS0 RESV0 NOACC0 : list (word * word)) (BASE : Z) (rn : art_run) : asan_iface :=
  art_iface art_fsg MAPS0 RESV0 NOACC0 BASE BUDGET art_fsinv rn.
Definition HIA (BUDGET : Z) (MAPS0 RESV0 NOACC0 : list (word * word)) (BASE : Z) (rn : art_run) : asan_iface :=
  HAJ.strict_of (HIR BUDGET MAPS0 RESV0 NOACC0 BASE rn).

(* [comment removed for export] *)
Definition inst_ok_stmt (scfg : SpuriousCfg) (L : asan_layout) (C : asan_statics_cells) (BUDGET : Z) : Prop :=
  forall MAPS0 RESV0 NOACC0 BASE rn,
    bridge_static ASEGS0 MAPS0 RESV0 NOACC0 (art_RES rn) (rn_HI rn) BUDGET BatInv_b.LENMAX BatInv_b.KMAX ->        (* [comment removed for export] *)
    art_run_ok rn -> rn_tp rn = 0x673d00 -> rn_key rn = 0 -> rn_tsd rn = 0x6951b8 -> rn_loff rn = 0x10 ->
    hl_img_hi L <= BIGSHADOW_LO /\ HAJ.asan_iface_okR L (rn_ar rn) C scfg (HIR BUDGET MAPS0 RESV0 NOACC0 BASE rn)
    /\ rt_flag_in_fs L (rn_ar rn) (HIR BUDGET MAPS0 RESV0 NOACC0 BASE rn).      (* [comment removed for export] *)
(* [comment removed for export] *)
Definition free_null_stmt (scfg : SpuriousCfg) (L : asan_layout) (BUDGET : Z) : Prop :=
  forall MAPS0 RESV0 NOACC0 BASE rn,
    bridge_static ASEGS0 MAPS0 RESV0 NOACC0 (art_RES rn) (rn_HI rn) BUDGET BatInv_b.LENMAX BatInv_b.KMAX ->
    art_run_ok rn -> rn_tp rn = 0x673d00 -> rn_key rn = 0 -> rn_tsd rn = 0x6951b8 -> rn_loff rn = 0x10 ->
    afree_null_spec L (rn_ar rn) scfg (HIR BUDGET MAPS0 RESV0 NOACC0 BASE rn).
(* [comment removed for export] *)
Definition h4e_stmt (BUDGET : Z) : Prop :=
  forall MAPS0 RESV0 NOACC0 BASE rn gfs0 k0 K0 B0 A0 M V,
    art_handoff_target art_fsg MAPS0 RESV0 NOACC0 BASE BUDGET art_fsinv rn gfs0 k0 K0 B0 A0 M V ->
    ri_inv (HIR BUDGET MAPS0 RESV0 NOACC0 BASE rn) [] [] [] (K0, B0) A0 M V.
(* [comment removed for export] *)
Definition icpt_ok_stmt (scfg : SpuriousCfg) (L : asan_layout) (IL : icpt_layout) (BUDGET : Z) : Prop :=
  forall MAPS0 RESV0 NOACC0 BASE rn,
    bridge_static ASEGS0 MAPS0 RESV0 NOACC0 (art_RES rn) (rn_HI rn) BUDGET BatInv_b.LENMAX BatInv_b.KMAX ->
    art_run_ok rn -> rn_tp rn = 0x673d00 -> rn_key rn = 0 -> rn_tsd rn = 0x6951b8 -> rn_loff rn = 0x10 ->
    aicpt_ok L (rn_ar rn) IL scfg (HIR BUDGET MAPS0 RESV0 NOACC0 BASE rn).
(* [comment removed for export] *)
Definition ext_ok_stmt (scfg : SpuriousCfg) (L : asan_layout) (EX : HAJ.ext_consts) (BUDGET : Z) : Prop :=
  forall MAPS0 RESV0 NOACC0 BASE rn,
    bridge_static ASEGS0 MAPS0 RESV0 NOACC0 (art_RES rn) (rn_HI rn) BUDGET BatInv_b.LENMAX BatInv_b.KMAX ->
    art_run_ok rn -> rn_tp rn = 0x673d00 -> rn_key rn = 0 -> rn_tsd rn = 0x6951b8 -> rn_loff rn = 0x10 ->
    HAJ.asan_ext_ok L (rn_ar rn) scfg (HIR BUDGET MAPS0 RESV0 NOACC0 BASE rn) EX.
(* [comment removed for export] *)
Definition gap_ok_stmt (BUDGET : Z) : Prop :=
  forall MAPS0 RESV0 NOACC0 BASE rn,
    bridge_static ASEGS0 MAPS0 RESV0 NOACC0 (art_RES rn) (rn_HI rn) BUDGET BatInv_b.LENMAX BatInv_b.KMAX ->
    art_run_ok rn -> rn_tp rn = 0x673d00 -> rn_key rn = 0 -> rn_tsd rn = 0x6951b8 -> rn_loff rn = 0x10 ->
    PMAGAP.rt_img_gap (HIR BUDGET MAPS0 RESV0 NOACC0 BASE rn).
(* [comment removed for export] *)
Definition lib_ext_okG (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (IL : icpt_layout) (scfg : SpuriousCfg) (HI : asan_iface) (EX : HAJ.ext_consts) : Prop :=
  exists HIR, HI = HAJ.strict_of HIR /\ HAJ.asan_iface_okR L ar C scfg HIR /\ aicpt_ok L ar IL scfg HIR /\ HAJ.asan_ext_ok L ar scfg HIR EX /\ PMAGAP.rt_img_gap HIR.
(* [comment removed for export] *)
Definition lib_ok_stmt (scfg : SpuriousCfg) (L : asan_layout) (C : asan_statics_cells) (IL : icpt_layout) (EX : HAJ.ext_consts) (Lay : lib_layoutA) (LSt : asan_run -> lib_statics) : Prop :=
  forall ar HI, asan_iface_okB L ar C scfg HI -> aicpt_ok L ar IL scfg HI ->
    lib_ext_okG L ar C IL scfg HI EX ->      (* [comment removed for export] *)
    lla_L Lay = L /\ lib_iface_okA Lay ar scfg HI (LSt ar).
(* [comment removed for export] *)
Definition dla_ok_stmt (scfg : SpuriousCfg) (L : asan_layout) (C : asan_statics_cells) (IL : icpt_layout) : Prop :=
  forall ar HI (sp0 : word), asan_iface_okB L ar C scfg HI -> ar_sptop ar = bv_unsigned sp0 -> drv_layoutA L ar IL sp0.
(* [comment removed for export] *)
Definition drv_consts_stmt (L : asan_layout) (C : asan_statics_cells) (IL : icpt_layout) : Prop :=
  as0_icpt_layout IL /\ incl RD_CELLS (asc_cells C) /\ 0 <= hl_k_per_malloc L /\ 0 <= hl_b_lin L /\ 0 <= hl_b_overhead L
  /\ incl PR_CELLS (asc_cells C)       (* [comment removed for export] *)
  /\ incl EX_CELLS (asc_cells C)       (* [comment removed for export] *)
  /\ incl DG_CELLS (asc_cells C) /\ incl DGS_CELLS (asc_cells C)       (* [comment removed for export] *)
  /\ incl [(1313048, 1, 1); (1282848, 8, 1182976); (1309752, 8, 2147450880)] (asc_cells C).      (* [comment removed for export] *)
(* [comment removed for export] *)
Definition drv_main_stmt (scfg : SpuriousCfg) (L : asan_layout) (C : asan_statics_cells) (IL : icpt_layout) (Lay : lib_layoutA) (LSt : asan_run -> lib_statics) : Prop :=
  sc_alloc scfg = false -> sc_fs scfg = true -> drv_consts_stmt L C IL ->
  forall (sp : word) (a0s path : list byte) (envp : list (list byte)) (fs : Fs.Fs),
    valid_sp sp -> valid_argv [a0s; path] -> valid_envp envp -> valid_fs fs ->
  forall (ar : asan_run) (HI : asan_iface) (p0 p1 can tid : word) (A0 : list (Z * Z)) (cr0 : credit)
         (R : bvmap 5 word) (M0 : word -> option byte) (model : Model),
    asan_iface_okB L ar C scfg HI -> afree_null_spec L ar scfg HI -> aicpt_ok L ar IL scfg HI -> lib_iface_okA Lay ar scfg HI (LSt ar) ->
    (forall g M, ls_ok (LSt ar) g M -> exists ax : axv, atexit_cellsA M ax) ->      (* [comment removed for export] *)
    drv_layoutA L ar IL sp ->
    SX2S.regs_ok (env_mainA sp p0 p1 can tid R) sr_mainA R ->
    SX2S.know_ok ASEGS (env_mainA sp p0 p1 can tid R) (mrestrict (ahid A0 model) M0) kn_mainA ->
    auxv_atA sp p0 M0 ->                                                     (* [comment removed for export] *)
    dinv ar HI sp M0 [] [] cr0 A0 M0 model ->
    defined M0 (bv_unsigned sp) (ar_stack_top ar - bv_unsigned sp) ->
    m_fds model = APSK.fds_std -> m_fs model = fs ->
    rdn ASEGS (mrestrict (ahid A0 model) M0) p1 (length path + 1) = Some (path ++ [Z_to_bv 8 0]) ->
    bv_unsigned sp <= bv_unsigned p1 /\ bv_unsigned p1 + Z.of_nat (length path) + 1 + 16 <= 2 ^ 47 ->
    cr0 = (8192, 2 ^ 34) ->
    (* [comment removed for export] *)
    defined M0 (bv_unsigned p1) (Z.of_nat (length path) + 1 + 16) ->
    shadow_allowed A0 (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) ->
    srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0xa7b04) M0 (seg_rom ASEGS)) model) (spec [a0s; path] fs).
(* [comment removed for export] *)
Definition usage_stmt (scfg : SpuriousCfg) : Prop :=
  forall sp brk0 rdraw argv envp uid hw fs, valid_sp sp -> valid_argv argv -> valid_envp envp -> entry_stack_fits sp argv envp -> valid_fs fs ->
  forall h, (h < 2)%nat -> forall E R FULL model,
    APSK.cs_ok ASEGS0 ASAN0 AsanInitK.LIMIT (SINV0 APH0 sp rdraw brk0 argv envp uid hw) (argH0 APH0 sp rdraw argv envp uid hw) fs E (HSA h) R FULL model ->
    length argv <> 2%nat ->
    srealizes ASEGS0 scfg (APSK.cfg_of ASEGS0 R (APCK.pc (HSA h)) FULL model) (spec argv fs).

(* [comment removed for export] *)
Lemma role_ks_0 : role HS_0 I_KSPACE = M_KSPACE /\ role HS_0 I_PARR = M_PTRARR.   Proof. vm_compute. split; reflexivity. Qed.
Lemma role_ks_1 : role HS_1 I_KSPACE = M_KSPACE /\ role HS_1 I_PARR = M_PTRARR.   Proof. vm_compute. split; reflexivity. Qed.
Lemma as0_RES_art : forall h, (h < 2)%nat -> forall E, as0_RES E = art_RES (as0_rn E (HSA h)).
Proof.
  intros h Hh E. unfold as0_RES, HandoffBInvK.RES_of, RESm0, art_RES. cbn [map as0_rn rn_kbase rn_parr]. unfold HandoffBInvK.resZ, rbase.
  assert (R : role (HSA h) I_KSPACE = M_KSPACE /\ role (HSA h) I_PARR = M_PTRARR) by (destruct h as [|[|h]]; [exact role_ks_0 | exact role_ks_1 | lia]).
  destruct R as (-> & ->). cbn [APK.am_base APK.am_len M_KSPACE M_PTRARR]. rewrite !Ba0ArtHandoffK_b.uE_lit by lia. reflexivity.
Qed.

Section MainPhase.
  Variable scfg : SpuriousCfg.
  Hypothesis Halloc : sc_alloc scfg = false.
  Hypothesis Hfs : sc_fs scfg = true.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variable L : asan_layout.
  Variable C : asan_statics_cells.
  Variable IL : icpt_layout.
  Variable Lay : lib_layoutA.
  Variable LSt : asan_run -> lib_statics.
  Variable EXc : HAJ.ext_consts.      (* [comment removed for export] *)
  Variable BUDGET : Z.
  Hypothesis BUD_ge : 2 ^ 34 <= BUDGET.
  Hypothesis BUD_hi : BUDGET <= 2 ^ 39 - 2 ^ 35.

  Hypothesis INST_OK : inst_ok_stmt scfg L C BUDGET.
  Hypothesis FREE_NULL : free_null_stmt scfg L BUDGET.
  Hypothesis H4E : h4e_stmt BUDGET.
  Hypothesis ICPT_OK : icpt_ok_stmt scfg L IL BUDGET.
  Hypothesis EXT_OK : ext_ok_stmt scfg L EXc BUDGET.
  Hypothesis GAP_OK : gap_ok_stmt BUDGET.
  Hypothesis LIB_OK : lib_ok_stmt scfg L C IL EXc Lay LSt.
  Hypothesis DLA_OK : dla_ok_stmt scfg L C IL.
  Hypothesis DRV_CONSTS : drv_consts_stmt L C IL.
  Hypothesis DRV_MAIN : drv_main_stmt scfg L C IL Lay LSt.
  Hypothesis USAGE : usage_stmt scfg.
  (* [comment removed for export] *)
  Hypothesis LSXFA : forall ar g M, ls_ok (LSt ar) g M -> exists ax : axv, atexit_cellsA M ax.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variable sp brk0 mbase : word. Variable rdraw : EntryDraw. Variables argv envp : list (list byte). Variable fs : Fs.Fs.
  Variable stdin : InputStream. Variables uid gid hw : word. Variable groups : list word. Variable net : NetQueue.
  Variables nofile sigmask : word. Variable abrt : bool. Variable ur : InputStream.  (* [comment removed for export] *)
  Hypothesis Hsp : valid_sp sp. Hypothesis Hbrk : valid_brk ASEGS0 brk0.
  Hypothesis Hva : valid_argv argv. Hypothesis Hve : valid_envp envp. Hypothesis Hfit : entry_stack_fits sp argv envp.
  Hypothesis Huid : valid_id uid. Hypothesis Hhw : valid_hwcap hw. Hypothesis Hvfs : valid_fs fs.
  #[local] Notation SINV := (SINV0 APH0 sp rdraw brk0 argv envp uid hw).
  #[local] Notation argH := (argH0 APH0 sp rdraw argv envp uid hw).
  #[local] Notation CSOK := (APSK.cs_ok ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs).
  #[local] Notation usp := (bv_unsigned sp).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="BUD_ge"] Lemma mp_bud : 0 <= BUDGET /\ 0 <= BatInv_b.KMAX /\ 0 <= BatInv_b.LENMAX < 2 ^ 62.
  Proof. unfold BatInv_b.KMAX, BatInv_b.LENMAX. lia. Qed.
  #[using="BUD_hi"] Lemma mp_gap : AsanCeil.bottomup_floor + BatInv_b.LENMAX + (17729665200128 + BUDGET) + (21 + BatInv_b.KMAX) * (BatInv_b.LENMAX + 4095) <= AsanCeil.alloc_ceiling.
  Proof. unfold BatInv_b.KMAX, BatInv_b.LENMAX, AsanCeil.bottomup_floor, AsanCeil.alloc_ceiling. lia. Qed.
  #[using="BUD_hi"] Lemma mp_gap_h : forall h, (h < 2)%nat ->
    AsanCeil.bottomup_floor + BatInv_b.LENMAX + (APK.a_totsz (HSA h) + BUDGET)
    + (Z.of_nat (length (segments_reserved ASEGS0) + length (APK.a_maps (HSA h))) + BatInv_b.KMAX) * (BatInv_b.LENMAX + 4095) <= AsanCeil.alloc_ceiling.
  Proof.
    intros h Hh. destruct (HSA_numbers h Hh) as (N1 & N2 & N3 & N4). rewrite N4, asan0_res_eq. cbn [length Nat.add]. change (Z.of_nat 21) with 21.
    unfold BatInv_b.KMAX, BatInv_b.LENMAX, AsanCeil.bottomup_floor, AsanCeil.alloc_ceiling. lia.
  Qed.

  #[using="Type"] Lemma HSA_pc : forall h, (h < 2)%nat -> APK.pc (HSA h) = 0xa7b04.
  Proof. intros [|[|h]] H; [reflexivity | reflexivity | lia]. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="Halloc Hfs L C IL Lay LSt BUDGET BUD_ge BUD_hi INST_OK FREE_NULL H4E ICPT_OK EXc EXT_OK GAP_OK LIB_OK DLA_OK DRV_CONSTS DRV_MAIN USAGE LSXFA Hsp Hva Hve Hfit Hvfs"] Theorem as0_main_phase : APSK.holes_stmt ASEGS0 scfg ASAN0 AsanInitK.LIMIT HS_as0 SINV argH (HOLES (fun fs' => spec argv fs')) fs.
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
    pose proof (as0_handoff_static sp brk0 rdraw [a0s; path] envp uid hw fs BUDGET BatInv_b.LENMAX BatInv_b.KMAX mp_bud mp_gap h Hh2 E R FULL model HC) as BS.
    rewrite (as0_RES_art h Hh2 E) in BS. fold cs rn in BS.
    pose proof (sp0_val sp brk0 rdraw [a0s; path] envp uid hw fs Hsp Hva Hve Hfit BUDGET BatInv_b.LENMAX BatInv_b.KMAX (HSA h) (drv_chk_HSA h Hh2) (mp_gap_h h Hh2)
                  E R FULL model HC) as SPV.
    pose proof HT as (REP & _ & _ & _ & CLI & _). destruct REP as (ROK & _).
    (* [comment removed for export] *)
    set (HR0 := HIR BUDGET MAPS0 RESV0 NOACC0 (as0_BASEx cs E) rn).
    assert (INSTR : hl_img_hi L <= BIGSHADOW_LO /\ HAJ.asan_iface_okR L ar C scfg HR0 /\ rt_flag_in_fs L ar HR0).
    { apply (INST_OK MAPS0 RESV0 NOACC0 (as0_BASEx cs E) rn); [exact BS | exact ROK | reflexivity | reflexivity | reflexivity | reflexivity]. }
    destruct INSTR as (IMGL & HIRok & FLG).
    assert (HIok : asan_iface_okB L ar C scfg (HIA BUDGET MAPS0 RESV0 NOACC0 (as0_BASEx cs E) rn)) by exact (strict_ok L ar C scfg HR0 IMGL FLG HIRok).
    assert (FNok : afree_null_spec L ar scfg (HIA BUDGET MAPS0 RESV0 NOACC0 (as0_BASEx cs E) rn)).
    { apply (strict_free_null_of L ar C scfg HR0 HIRok). apply (FREE_NULL MAPS0 RESV0 NOACC0 (as0_BASEx cs E) rn); [exact BS | exact ROK | reflexivity | reflexivity | reflexivity | reflexivity]. }
    assert (ICR : aicpt_ok L ar IL scfg HR0).
    { apply (ICPT_OK MAPS0 RESV0 NOACC0 (as0_BASEx cs E) rn); [exact BS | exact ROK | reflexivity | reflexivity | reflexivity | reflexivity]. }
    assert (EXR : HAJ.asan_ext_ok L ar scfg HR0 EXc).
    { apply (EXT_OK MAPS0 RESV0 NOACC0 (as0_BASEx cs E) rn); [exact BS | exact ROK | reflexivity | reflexivity | reflexivity | reflexivity]. }
    pose proof (strict_of_nil HR0 _ _ _ _ (H4E _ _ _ _ _ _ _ _ _ _ _ _ HT)) as RI.
    set (HI := HIA BUDGET MAPS0 RESV0 NOACC0 (as0_BASEx cs E) rn) in *.
    change (HAJ.strict_of HR0) with HI in RI.
    assert (SPT : ar_sptop ar = usp) by exact SPV.
    assert (ICok : aicpt_ok L ar IL scfg HI) by exact (strict_icpt L ar C IL scfg HR0 IMGL HIRok ICR).
    assert (GAPR : PMAGAP.rt_img_gap HR0).
    { apply (GAP_OK MAPS0 RESV0 NOACC0 (as0_BASEx cs E) rn); [exact BS | exact ROK | reflexivity | reflexivity | reflexivity | reflexivity]. }
    assert (LXok : lib_ext_okG L ar C IL scfg HI EXc).
    { exists HR0. split; [reflexivity|]. split; [exact HIRok|]. split; [exact ICR|]. split; [exact EXR| exact GAPR]. }
    destruct (LIB_OK ar HI HIok ICok LXok) as (LayL & LIok). pose proof (DLA_OK ar HI sp HIok SPT) as DL.
    (* [comment removed for export] *)
    pose proof (as0_EXTRA_wf cs E) as XWF.
    assert (XBL : 16515072 + 2461330432 + A_bytes (as0_EXTRA cs E) + BUDGET <= AsanInitK.LIMIT).
    { unfold as0_EXTRA. cbn [A_bytes fst snd]. unfold AsanInitK.LIMIT, target_alloc_limit. lia. }
    destruct (as0_main_entry sp brk0 rdraw a0s path envp uid hw fs Hsp Hva Hve Hfit BUDGET BatInv_b.LENMAX BatInv_b.KMAX mp_bud (as0_EXTRA cs E) XWF XBL mp_gap
                h Hh2 E R FULL model HC) as (can & tid & HR & HK & LZ & FDS & _ & STR).
    destruct (as0_main_auxv sp brk0 rdraw a0s path envp uid hw fs Hsp Hva Hve Hfit BUDGET BatInv_b.LENMAX BatInv_b.KMAX mp_bud (as0_EXTRA cs E) XBL mp_gap
                h Hh2 E R FULL model HC) as (uidz & rnd & hwz & AUXW & AUXU & AUXH & AUXR1 & AUXR2).
    destruct LZ as (_ & _ & _ & MI & HALT).
    destruct CLI as (_ & _ & _ & _ & S1 & S2 & S3 & S4 & S5 & _).
    cbn [as0_rn rn_ar as0_ar ar_stack_top ar_stack_bottom ar_sptop] in S1, S2, S3, S4, S5.
    assert (SDEF : defined FULL usp (ar_stack_top ar - usp)).
    { apply (as0_main_stack_defined sp brk0 rdraw a0s path envp uid hw fs Hsp Hva Hve Hfit BUDGET BatInv_b.LENMAX BatInv_b.KMAX mp_bud (as0_EXTRA cs E) XBL mp_gap
               h Hh2 E R FULL model HC); unfold ar, cs; cbn [as0_ar ar_stack_top]; rewrite SPV in *.
      - rewrite S5. rewrite <- Z.add_mod_idemp_l by lia. rewrite S3. reflexivity.
      - lia. }
    assert (DI : dinv ar HI sp FULL [] [] (8192, 2 ^ 34) (as0_A0x cs E) FULL model).
    { apply DINV; [exact RI | exact MI | exact HALT | reflexivity | |].
      intros x Hx. apply (as0_stksh_main sp brk0 rdraw [a0s; path] envp uid hw fs Hsp Hva Hve Hfit h Hh2 E R FULL model HC).   (* [comment removed for export] *) unfold STKTOP, ar, cs in Hx. cbn [as0_ar ar_sptop ar_stack_top] in Hx. rewrite SPV in Hx. exact Hx.
      intros x Hx. apply (as0_stksh_main_hi sp brk0 rdraw [a0s; path] envp uid hw fs Hsp Hva Hve Hfit h Hh2 E R FULL model HC). unfold ahl_ceil, ar, cs in Hx. cbn [as0_ar ar_sptop] in Hx. rewrite SPV in Hx. exact Hx. }
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
    refine (DRV_MAIN Halloc Hfs DRV_CONSTS sp a0s path envp fs Hsp Hva Hve Hvfs ar HI _ _ can tid (as0_A0x cs E) (8192, 2 ^ 34) R FULL model HIok FNok ICok LIok (LSXFA ar) DL HR HK _ DI SDEF FDS EFS _ _ eq_refl _ _).
    - exists uidz, rnd, hwz. rewrite UP0.
      split; [intros j Hj; replace (usp + 8 * Z.of_nat (length envp) + 200 - 160 + 8 * Z.of_nat j) with (usp + 8 * Z.of_nat (length envp) + 40 + 8 * Z.of_nat j) by ring; exact (AUXW j Hj)|].
      repeat split; try lia.
      pose proof (Z.div_mod usp 16 ltac:(lia)) as DM. rewrite SA16 in DM.
      replace (usp + 8 * Z.of_nat (length envp) + 200) with ((2 * (usp / 16) + Z.of_nat (length envp) + 25) * 8) by lia. apply Z.mod_mul. lia.
    - rewrite PE. exact STR1.
    - rewrite PE, PV1. rewrite PV1 in PH1. lia.
    - rewrite PE. intros i Hi.
      exact (as0_main_str_defined sp brk0 rdraw a0s path envp uid hw fs Hsp Hva Hve Hfit BUDGET BatInv_b.LENMAX BatInv_b.KMAX mp_bud (as0_EXTRA cs E) XBL mp_gap h Hh2 E R FULL model HC 1%nat ltac:(lia) i Hi).
    - pose proof HT as (_ & _ & _ & _ & CLI' & _). destruct CLI' as (_ & _ & SAH & _). exact SAH.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="Halloc Hfs L C IL Lay LSt BUDGET BUD_ge BUD_hi INST_OK FREE_NULL H4E ICPT_OK EXc EXT_OK GAP_OK LIB_OK DLA_OK DRV_CONSTS DRV_MAIN USAGE LSXFA Hsp Hbrk Hva Hve Hfit Huid Hhw Hvfs"] Theorem as0_realizes_spec_run :
    srealizes ASEGS0 scfg (init_config ASEGS0 AsanUbsan.M.init_pc APH0 sp brk0 mbase rdraw AsanInitK.LIMIT
                                 (AsanInitK.inp argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur))
              (spec argv fs).
  Proof.
    apply (as0_startup_closed scfg Halloc sp brk0 mbase rdraw argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur
             Hsp Hbrk Hva Hve Hfit Huid Hhw (fun fs' => spec argv fs')).
    - intros fs'. apply spec_has_nil.
    - exact as0_main_phase.
  Qed.
End MainPhase.
