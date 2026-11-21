(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the channel-reader fact, the SIGPIPE disposition left free, the reserved-interval ledger, the rseq-dependent auxv, the nine-byte string read-ahead, the launch input's kernel build): changed HSA_pc, Hsp, Huid and 15 more; added B, Hapc, Hbrk and 24 more; taken in part from projects/jsoncons/fuzz_json_cursor/proofs/lib/Pm9MainPhaseA.v, lines 87, 94-97, 170-194, 202-245, 265-267, 272-304. *)
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
    (* DROPPED, old beside new: [auxv_atA sp p0 M0 ->] (Main's ruling, option D; Pm5DrvEntry). *)
    dinv ar HI sp M0 [] [] cr0 A0 M0 model ->
    defined M0 (bv_unsigned sp) (ar_stack_top ar - bv_unsigned sp) ->
    m_fds model = APSK.fds_std -> m_fs model = fs ->
    rdn ASEGS (mrestrict (ahid A0 model) M0) p1 (length path + 1) = Some (path ++ [Z_to_bv 8 0]) ->
    bv_unsigned sp <= bv_unsigned p1 /\ bv_unsigned p1 + Z.of_nat (length path) + 1 + 9 <= 2 ^ 47 ->
    cr0 = (8192, B0) ->
    (* [comment removed for export] *)
    defined M0 (bv_unsigned p1) (Z.of_nat (length path) + 1 + 8) ->
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

  (* THE SECTION'S PARAMETERS, old beside new.
       OLD  sp brk0 mbase rdraw argv envp fs stdin uid gid hw groups net nofile sigmask abrt ifs urnd tmp0,
            Hsp Hbrk Hva Hve Hfit Huid Hhw Hvfs Hseed; SINV0/argH0 at eight/seven places.
       NEW  the launch's whole input in [HandoffBridgeK]'s Section Image order ([ifs] the input's
            filesystem, [fs] the plan's FS0) with [Pm5StartupFinalK]'s hypotheses, plus Hvfs.
     Every Section lemma of another file is reached by [eapply ..; eassumption]. *)
  Variables (sp : word) (rdraw : EntryDraw) (brk0 mbase : word) (argv envp : list (list byte)).
  Variables (ifs : Fs.Fs) (stdin : InputStream) (uid gid hw : word) (groups : list word) (net : NetQueue).
  Variables (nofile sigmask : word) (abrt : bool) (urnd : InputStream) (tmp0 : Fs.Fs).
  Variables (kb : KernelBuild) (execfn : list byte) (sdf : bool) (apc : N) (fs : Fs.Fs).
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk ASEGS0 brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Hypothesis Huid : valid_id uid.
  Hypothesis Hhw : valid_hwcap hw.
  Hypothesis Hapc : Z.of_N apc = APK.a_entry ASAN0.
  #[local] Notation INP := (AsanInitK.inp argv envp ifs stdin uid gid hw groups net nofile sigmask abrt urnd tmp0 kb execfn sdf).
  Hypothesis Hlaunch : valid_launch INP.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) INP.
  Hypothesis Hvfs : valid_fs fs.
  Hypothesis Hseed : fs_seed_tmp ifs tmp0 = fs.
  (* [comment removed for export] *)
  Hypothesis PHIOK : forall a0s path, argv = [a0s; path] -> phi_okD PHI path fs.
  #[local] Notation B := (kb_rseq (in_kernel INP)).
  #[local] Notation SINV := (SINV0 APH0 sp rdraw brk0 mbase argv envp ifs stdin uid gid hw groups net nofile sigmask abrt urnd tmp0 kb execfn sdf apc).
  #[local] Notation argH := (argH0 sp rdraw argv envp ifs stdin uid gid hw groups net nofile sigmask abrt urnd tmp0 kb execfn sdf).
  #[local] Notation CSOK := (APSK.cs_ok ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs).
  #[local] Notation usp := (bv_unsigned sp).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma mp_bud : 0 <= BUDGET /\ 0 <= Pm5ArtInv.KMAX /\ 0 <= Pm5ArtInv.LENMAX < 2 ^ 62.
  Proof. unfold Pm5ArtInv.KMAX, Pm5ArtInv.LENMAX. lia. Qed.
  (* the [a_totsz] term is DERIVED, not the measured literal: see Pm5HandoffInstK's
     [HSA_numbers].  [resx0 : APCK.resx_bytes ASAN0 = 81920] is by [reflexivity]. *)
  Lemma mp_gap : AsanCeil.bottomup_floor + Pm5ArtInv.LENMAX + (17729665388544 + APCK.resx_bytes ASAN0 + BUDGET) + (23 + Pm5ArtInv.KMAX) * (Pm5ArtInv.LENMAX + 4095) <= AsanCeil.alloc_ceiling.
  Proof. rewrite resx0. unfold Pm5ArtInv.KMAX, Pm5ArtInv.LENMAX, AsanCeil.bottomup_floor, AsanCeil.alloc_ceiling. lia. Qed.
  Lemma mp_gap_h : forall b h, (h < 2)%nat ->
    AsanCeil.bottomup_floor + Pm5ArtInv.LENMAX + (APK.a_totsz (HSA b h) + BUDGET)
    + (Z.of_nat (length (segments_reserved ASEGS0) + APK.n_resx ASAN0 + length (APK.a_maps (HSA b h))) + Pm5ArtInv.KMAX) * (Pm5ArtInv.LENMAX + 4095) <= AsanCeil.alloc_ceiling.
  Proof.
    intros b h Hh. destruct (HSA_numbers b h Hh) as (N1 & N2 & N3 & N4). rewrite resx0 in N1. rewrite N4, asan0_res_eq. cbn [length Nat.add APK.n_resx ASAN0]. change (Z.of_nat 23) with 23.
    unfold Pm5ArtInv.KMAX, Pm5ArtInv.LENMAX, AsanCeil.bottomup_floor, AsanCeil.alloc_ceiling. lia.
  Qed.

  Lemma HSA_pc : forall b h, (h < 2)%nat -> APK.pc (HSA b h) = 0xb0980.
  Proof. intros [|] [|[|h]] H; first [lia | reflexivity]. Qed.

  (* STATEMENT CHANGED, old beside new: the hand-off table is the run's flag's.
       OLD  holes_stmt .. HS_as0 SINV argH (HOLES ..) fs
       NEW  holes_stmt .. (HS_as0 B) SINV argH (HOLES ..) fs   -- Pm5StartupFinalK's [HS_sound].
     Proof: as before, except that every other file's Section lemma is reached by
     [eapply ..; eassumption], the per-state facts are posed first so [eassumption] finds
     them, and argv[k]'s pointer is CatExec's [cat_argv_ptr (ed_top rdraw) ..] throughout
     (the old [PE]/[UP0] closed forms are false at the revision and are gone). *)
  Theorem as0_main_phase : APSK.holes_stmt ASEGS0 scfg ASAN0 AsanInitK.LIMIT (HS_as0 B) SINV argH (HOLES (fun fs' => spec argv fs')) fs.
  Proof.
    intros h ch Hh E R FULL model HC.
    assert (Hh2 : (h < 2)%nat).
    { destruct (Nat.lt_ge_cases h 2) as [Hlt|Hge]; [exact Hlt|]. rewrite (HSA_none B h Hge) in Hh. discriminate Hh. }
    rewrite (HSA_some B h Hh2) in Hh. injection Hh as <-.
    pose proof (as0_chk_HSA B h Hh2) as C0. pose proof (drv_chk_HSA B h Hh2) as CD.
    pose proof (stk_chk_HSA B h Hh2) as CS. pose proof (lib_chk_HSA B h Hh2) as CL.
    pose proof mp_bud as MB. pose proof mp_gap as MG. pose proof (mp_gap_h B h Hh2) as MGH.
    assert (EFS : m_fs model = fs) by (eapply ent_model; eassumption).
    unfold HOLES. rewrite EFS.
    destruct (Nat.eq_dec (length argv) 2) as [Hargc|Hargc]; [|eapply USAGE; eassumption].
    destruct argv as [|a0s [|path [|x l]]] eqn:Hargv; try discriminate Hargc. clear Hargc.

    set (cs := HSA B h). set (rn := as0_rn E cs). set (ar := as0_ar E cs).
    set (MAPS0 := vm_maps (m_vmmaps model)). set (RESV0 := vm_reserved (m_vmmaps model)). set (NOACC0 := vm_noaccess (m_vmmaps model)).
    assert (HT : art_handoff_target art_fsg MAPS0 RESV0 NOACC0 (as0_BASEx cs E) BUDGET art_fsinv rn art_fsg0 K0D 8192 BUDGET
                   (as0_A0x cs E) FULL (vml_of model))
      by (eapply as0_art_handoff_h; eassumption).
    assert (BS : bridge_static ASEGS0 MAPS0 RESV0 NOACC0 (as0_RES E) (APSK.uE E APK.e_sp0 - 8388608) BUDGET Pm5ArtInv.LENMAX Pm5ArtInv.KMAX)
      by (eapply as0_handoff_static; eassumption).
    rewrite (as0_RES_art B h Hh2 E) in BS. fold cs rn in BS.
    assert (SPV : APSK.uE E APK.e_sp0 = usp) by (eapply sp0_val; eassumption).
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
    edestruct as0_main_entry as (can & tid & HR & HK & LZ & FDS & _ & STR); [eassumption .. |].
    (* DROPPED, old beside new: [destruct (as0_main_auxv ..) as (uidz & rnd & hwz & AUXW & ..)] --
       the ten-pair auxv fact is false at LPS 75d69e00 and no consumer reads it (option D). *)
    destruct LZ as (_ & _ & _ & MI & HALT).
    (* [CLI] is stated over the [set] variables [rn]/[cs], which [cbn] cannot unfold: without
       this the [cbn] below leaves [S1..S5] at [ar_stack_top (rn_ar rn)] while [SDEF]'s goals
       are computed down to [uE E (topE ..)], so [rewrite S5] matches no subterm.  Main's
       [pose proof (as0_art_handoff_h ..)] gave these facts in the unfolded form. *)
    unfold rn, cs in CLI.
    destruct CLI as (_ & _ & _ & _ & S1 & S2 & S3 & S4 & S5 & _).
    cbn [as0_rn rn_ar as0_ar ar_stack_top ar_stack_bottom ar_sptop] in S1, S2, S3, S4, S5.
    assert (SDEF : defined FULL usp (ar_stack_top ar - usp)).
    { eapply as0_main_stack_defined; [eassumption .. | |]; unfold ar, cs; cbn [as0_ar ar_stack_top]; rewrite SPV in *.
      - rewrite S5. rewrite <- Z.add_mod_idemp_l by lia. rewrite S3. reflexivity.
      - lia. }
    assert (DI : dinv ar HI sp FULL [] [] (8192, BUDGET) (as0_A0x cs E) FULL model).
    { apply DINV; [exact RI | exact MI | exact HALT | reflexivity | | | | exact (APSK.co_rdr _ _ _ _ _ _ _ _ _ _ _ HC)].
      - intros x Hx. eapply as0_stksh_main; [eassumption .. |].
        unfold STKTOP, ar, cs in Hx. cbn [as0_ar ar_sptop ar_stack_top] in Hx. rewrite SPV in Hx. exact Hx.
      - intros x Hx. eapply as0_stksh_main_hi; [eassumption .. |].
        unfold ahl_ceil, ar, cs in Hx. cbn [as0_ar ar_sptop] in Hx. rewrite SPV in Hx. exact Hx.
      - intros b []. }
    destruct (STR 1%nat ltac:(lia)) as (STR1 & PV1 & PH1). cbn [nth] in STR1, PH1.
    (* [_], not [B]: [destruct argv .. eqn:Hargv] above put [[a0s; path]] for [argv] in the goal,
       while [B] still names the Section variable [argv], so a closed [HSA_pc B ..] matches nothing *)
    unfold APSK.cfg_of, cs. rewrite (HSA_pc _ h Hh2). fold cs.
    refine (DRV_MAIN Halloc Hfs DRV_CONSTS sp a0s path envp fs Hsp Hva Hve Hvfs (PHIOK a0s path eq_refl) ar HI _ _ can tid (as0_A0x cs E) (8192, BUDGET) R FULL model HIok FNok ICok LIok DL HR HK DI SDEF FDS EFS _ _ eq_refl _ _).
    - exact STR1.
    - (* argv[1] sits above sp: its offset from sp is [cat_string_off + |argv[0]| + 1 >= 0] *)
      split; [rewrite PV1; lia | exact PH1].
    - intros i Hi. eapply as0_main_str_defined; [eassumption .. | |]; first [exact Hi | lia].
    - pose proof HT as (_ & _ & _ & _ & CLI' & _). destruct CLI' as (_ & _ & SAH & _). exact SAH.
  Qed.

  (* STATEMENT CHANGED, old beside new (consumers PmCasanFinal.v:76 / PmCbothFinal.v:76, which
     call this positionally and must move to the new Section list):
       OLD  srealizes ASEGS0 scfg (init_config ASEGS0 AsanUbsan.M.init_pc APH0 sp brk0 mbase rdraw LIM
                                    (AsanInitK.inp argv envp ifs stdin uid gid hw groups net nofile sigmask abrt urnd tmp0))
                      (spec argv fs)
       NEW  srealizes ASEGS0 scfg (init_config ASEGS0 apc APH0 sp brk0 mbase rdraw LIM INP) (spec argv fs),
            over [apc]/[Hapc] and the input's kernel build and exec name -- Pm5StartupFinalK's
            [as0_startup_closed] at the revision. *)
  Theorem as0_realizes_spec_run :
    srealizes ASEGS0 scfg (init_config ASEGS0 apc APH0 sp brk0 mbase rdraw AsanInitK.LIMIT INP) (spec argv fs).
  Proof.
    eapply as0_startup_closed with (T := fun fs' => spec argv fs');
      first [ eassumption | exact as0_main_phase | (intros fs'; apply spec_has_nil) ].
  Qed.
End MainPhaseW.
