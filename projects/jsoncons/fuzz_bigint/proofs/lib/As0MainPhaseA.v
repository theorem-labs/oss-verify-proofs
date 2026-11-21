(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: for LPS 727298f3, the main phase runs from the entry states computed for each CONFIG_RSEQ flag (the certificate's flag tied to the run's by HRZ) in place of the recorded ones, the section takes the kernel build, the exec file name and the launch facts (valid_launch, entry_launch_ok_va), argv[1] is read from the launch's string layout, the auxv base is its own slot (auxvp), the channel reader is passed on, and a string ends at least 9 bytes below 2 ^ 47, was 16. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec ShapeAlg SpinAlg CatExec AgentLib AxSymExec3K AxSymExec3SoundK AsanPlanCoreK AsanPlanK AsanPlanSoundK AsanInitK
  As0DefsK As0PlanImagesK As0StartupK HandoffBridgeK HandoffBInvK HandoffRolesK As0HandoffK As0CertK_202 As0HandoffInstK As0DrvEntryK As0StartupFinalK.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import SymExec2 SymExec2Sound SymRun SymDrive HeapIface HeapIfaceA HeapIfaceANull IcptIfaceA LibIface LibIfaceA
  ArtRuns ArtBridge ArtInv ArtFsInv As0ArtHandoffK As0ArtHandoffInstK As0StkShK As0DrvKitA As0DrvEntry As0DrvEntryInst As0Drv_defs As0DrvLib As0DrvRead As0DrvStdio.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import ShapeLaws Spec BigintSpec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
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
Definition HIA (BUDGET : Z) (MAPS0 RESV0 NOACC0 : list (word * word)) (BASE : Z) (rn : art_run) : asan_iface :=
  art_iface art_fsg MAPS0 RESV0 NOACC0 BASE BUDGET art_fsinv rn.

(* [comment removed for export] *)
Definition inst_ok_stmt (scfg : SpuriousCfg) (L : asan_layout) (C : asan_statics_cells) (BUDGET : Z) : Prop :=
  forall MAPS0 RESV0 NOACC0 BASE rn,
    bridge_static ASEGS0 MAPS0 RESV0 NOACC0 (art_RES rn) (rn_HI rn) BUDGET ArtInv.LENMAX ArtInv.KMAX ->        (* [comment removed for export] *)
    art_run_ok rn -> rn_tp rn = 0x610d08 -> rn_key rn = 0 -> rn_tsd rn = 0x6320b0 -> rn_loff rn = 0x10 ->
    asan_iface_ok L (rn_ar rn) C scfg (HIA BUDGET MAPS0 RESV0 NOACC0 BASE rn).
(* [comment removed for export] *)
Definition free_null_stmt (scfg : SpuriousCfg) (L : asan_layout) (BUDGET : Z) : Prop :=
  forall MAPS0 RESV0 NOACC0 BASE rn,
    bridge_static ASEGS0 MAPS0 RESV0 NOACC0 (art_RES rn) (rn_HI rn) BUDGET ArtInv.LENMAX ArtInv.KMAX ->
    art_run_ok rn -> rn_tp rn = 0x610d08 -> rn_key rn = 0 -> rn_tsd rn = 0x6320b0 -> rn_loff rn = 0x10 ->
    afree_null_spec L (rn_ar rn) scfg (HIA BUDGET MAPS0 RESV0 NOACC0 BASE rn).
(* [comment removed for export] *)
Definition h4e_stmt (BUDGET : Z) : Prop :=
  forall MAPS0 RESV0 NOACC0 BASE rn gfs0 k0 K0 B0 A0 M V,
    art_handoff_target art_fsg MAPS0 RESV0 NOACC0 BASE BUDGET art_fsinv rn gfs0 k0 K0 B0 A0 M V ->
    ri_inv (HIA BUDGET MAPS0 RESV0 NOACC0 BASE rn) [] [] [] (K0, B0) A0 M V.
(* [comment removed for export] *)
Definition icpt_ok_stmt (scfg : SpuriousCfg) (L : asan_layout) (IL : icpt_layout) (BUDGET : Z) : Prop :=
  forall MAPS0 RESV0 NOACC0 BASE rn,
    bridge_static ASEGS0 MAPS0 RESV0 NOACC0 (art_RES rn) (rn_HI rn) BUDGET ArtInv.LENMAX ArtInv.KMAX ->
    art_run_ok rn -> rn_tp rn = 0x610d08 -> rn_key rn = 0 -> rn_tsd rn = 0x6320b0 -> rn_loff rn = 0x10 ->
    aicpt_ok L (rn_ar rn) IL scfg (HIA BUDGET MAPS0 RESV0 NOACC0 BASE rn).
(* [comment removed for export] *)
Definition lib_ok_stmt (scfg : SpuriousCfg) (L : asan_layout) (C : asan_statics_cells) (IL : icpt_layout) (Lay : lib_layoutA) (LSt : asan_run -> lib_statics) : Prop :=
  forall ar HI, asan_iface_ok L ar C scfg HI -> aicpt_ok L ar IL scfg HI -> lla_L Lay = L /\ lib_iface_okA Lay ar scfg HI (LSt ar).
(* [comment removed for export] *)
Definition dla_ok_stmt (scfg : SpuriousCfg) (L : asan_layout) (C : asan_statics_cells) (IL : icpt_layout) : Prop :=
  forall ar HI (sp0 : word), asan_iface_ok L ar C scfg HI -> ar_sptop ar = bv_unsigned sp0 -> drv_layoutA L ar IL sp0.
(* [comment removed for export] *)
Definition drv_consts_stmt (L : asan_layout) (C : asan_statics_cells) (IL : icpt_layout) : Prop :=
  as0_icpt_layout IL /\ incl RD_CELLS (asc_cells C) /\ 0 <= hl_k_per_malloc L /\ 0 <= hl_b_lin L /\ 0 <= hl_b_overhead L
  /\ incl PR_CELLS (asc_cells C)       (* [comment removed for export] *)
  /\ incl EX_CELLS (asc_cells C)       (* [comment removed for export] *)
  /\ incl DG_CELLS (asc_cells C) /\ incl DGS_CELLS (asc_cells C)       (* [comment removed for export] *)
  /\ incl [(911384, 1, 1); (882384, 8, 800988); (908088, 8, 2147450880)] (asc_cells C).      (* [comment removed for export] *)
(* [comment removed for export] *)
Definition drv_main_stmt (scfg : SpuriousCfg) (L : asan_layout) (C : asan_statics_cells) (IL : icpt_layout) (Lay : lib_layoutA) (LSt : asan_run -> lib_statics) : Prop :=
  sc_alloc scfg = false -> sc_fs scfg = true -> drv_consts_stmt L C IL ->
  forall (sp : word) (a0s path : list byte) (envp : list (list byte)) (fs : Fs.Fs),
    valid_sp sp -> valid_argv [a0s; path] -> valid_envp envp -> valid_fs fs ->
  forall (ar : asan_run) (HI : asan_iface) (p0 p1 can tid auxvp : word) (A0 : list (Z * Z)) (cr0 : credit)
         (R : bvmap 5 word) (M0 : word -> option byte) (model : Model),
    asan_iface_ok L ar C scfg HI -> afree_null_spec L ar scfg HI -> aicpt_ok L ar IL scfg HI -> lib_iface_okA Lay ar scfg HI (LSt ar) -> drv_layoutA L ar IL sp ->
    SX2S.regs_ok (env_mainA sp p0 p1 can tid auxvp R) sr_mainA R ->
    SX2S.know_ok ASEGS (env_mainA sp p0 p1 can tid auxvp R) (mrestrict (ahid A0 model) M0) kn_mainA ->
    auxv_atA sp auxvp M0 ->                                                     (* [comment removed for export] *)
    dinv ar HI sp M0 [] [] cr0 A0 M0 model ->
    defined M0 (bv_unsigned sp) (ar_stack_top ar - bv_unsigned sp) ->
    m_fds model = APSK.fds_std -> m_fs model = fs ->
    rdn ASEGS (mrestrict (ahid A0 model) M0) p1 (length path + 1) = Some (path ++ [Z_to_bv 8 0]) ->
    bv_unsigned sp <= bv_unsigned p1 /\ bv_unsigned p1 + Z.of_nat (length path) + 1 + 9 <= 2 ^ 47 ->
    cr0 = (8192, 2 ^ 34) ->
    (* [comment removed for export] *)
    defined M0 (bv_unsigned p1) (Z.of_nat (length path) + 1 + 8) ->
    shadow_allowed A0 (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) ->
    srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x8d9e8) M0 (seg_rom ASEGS)) model) (spec [a0s; path] fs).
(* [comment removed for export] *)
Definition usage_stmt (scfg : SpuriousCfg) : Prop :=
  forall sp brk0 rdraw argv envp uid hw fs mbase stdin gid groups net nofile sigmask abrt sdf ur kb execfn apc (r : Z),
  valid_sp sp -> valid_argv argv -> valid_envp envp -> entry_stack_fits sp argv envp -> valid_fs fs ->
  (* [hbi_vals] applies [AsanInitK.uE0]/[uE0_s2a], which
     carry [Run.entry_launch_ok_va] -- the only thing that pins the
     [arch_align_stack] pad -- so every consumer that reaches [hbi_sp0] or
     [sp0_val] carries it.  Spelled exactly as [HandoffBridgeK.v:630-631].
     [valid_launch] is [Run.valid_input_either]'s conjunct the usage strings'
     headroom needs ([As0UsageEntryK.entg_str0_hi]); same order as [Bo0MainPhaseA]. *)
  entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw)
    (AsanInitK.inp argv envp fs stdin uid gid hw groups net nofile sigmask abrt sdf ur kb execfn) ->
  valid_launch (AsanInitK.inp argv envp fs stdin uid gid hw groups net nofile sigmask abrt sdf ur kb execfn) ->
  r = AsanPlanCoreK.APCK.rseq_z (kb_rseq (in_kernel (AsanInitK.inp argv envp fs stdin uid gid hw groups net nofile sigmask abrt sdf ur kb execfn))) ->
  forall h, (h < 2)%nat -> forall E R FULL model,
    APSK.cs_ok ASEGS0 ASAN0 AsanInitK.LIMIT (SINV0 APH0 sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask abrt sdf ur kb execfn apc) (argH0 sp rdraw argv envp fs stdin uid gid hw groups net nofile sigmask abrt sdf ur kb execfn) fs E (HSA r h) R FULL model ->
    length argv <> 2%nat ->
    srealizes ASEGS0 scfg (APSK.cfg_of ASEGS0 R (APCK.pc (HSA r h)) FULL model) (spec argv fs).

(* [comment removed for export] *)
Lemma role_ks_HSA : forall r h, (h < 2)%nat -> role (HSA r h) I_KSPACE = M_KSPACE /\ role (HSA r h) I_PARR = M_PTRARR.
Proof. intros r [|[|h]] H; [| |lia]; unfold HSA; destruct (Z.eqb r 1); vm_compute; split; reflexivity. Qed.
Lemma as0_RES_art : forall r h, (h < 2)%nat -> forall E, as0_RES E = art_RES (as0_rn E (HSA r h)).
Proof.
  intros r h Hh E. unfold as0_RES, HandoffBInvK.RES_of, RESm0, art_RES. cbn [map as0_rn rn_kbase rn_parr]. unfold HandoffBInvK.resZ, rbase.
  assert (R : role (HSA r h) I_KSPACE = M_KSPACE /\ role (HSA r h) I_PARR = M_PTRARR) by exact (role_ks_HSA r h Hh).
  destruct R as (-> & ->). cbn [APK.am_base APK.am_len M_KSPACE M_PTRARR]. rewrite !As0ArtHandoffK.uE_lit by lia. reflexivity.
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
  Variable BUDGET : Z.
  Hypothesis BUD_ge : 2 ^ 34 <= BUDGET.
  Hypothesis BUD_hi : BUDGET <= 2 ^ 39 - 2 ^ 35.

  Hypothesis INST_OK : inst_ok_stmt scfg L C BUDGET.
  Hypothesis FREE_NULL : free_null_stmt scfg L BUDGET.
  Hypothesis H4E : h4e_stmt BUDGET.
  Hypothesis ICPT_OK : icpt_ok_stmt scfg L IL BUDGET.
  Hypothesis LIB_OK : lib_ok_stmt scfg L C IL Lay LSt.
  Hypothesis DLA_OK : dla_ok_stmt scfg L C IL.
  Hypothesis DRV_CONSTS : drv_consts_stmt L C IL.
  Hypothesis DRV_MAIN : drv_main_stmt scfg L C IL Lay LSt.
  Hypothesis USAGE : usage_stmt scfg.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variable sp brk0 mbase : word. Variable rdraw : EntryDraw. Variables argv envp : list (list byte). Variable fs : Fs.Fs.
  Variable stdin : InputStream. Variables uid gid hw : word. Variable groups : list word. Variable net : NetQueue.
  Variables nofile sigmask : word. Variables abrt sdf : bool. Variable ur : InputStream.
  (* The kernel build, the exec file name and [sdf] above are the three places of
     [State.mkProcInput_full] this cone leaves free; see [AsanInitK.inp]. *)
  Variable kb : KernelBuild.
  Variable execfn : list byte.
  (* [AsanInitK.SINV0] discharges [apc] too, through [entryw]; the block above
     is otherwise already the full [mkProcInput_full] field list. *)
  #[local] Notation apc := Asan.M.init_pc.
  (* the certificate's CONFIG_RSEQ flag, tied to the run's by [HRZ] below
     *)
  Variable r : Z.
  Hypothesis Hsp : valid_sp sp. Hypothesis Hbrk : valid_brk ASEGS0 brk0. Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Hva : valid_argv argv. Hypothesis Hve : valid_envp envp. Hypothesis Hfit : entry_stack_fits sp argv envp.
  (* Same launch fact [usage_stmt] carries; [APSK.init_cs_ok], which is
     what produces the [CSOK] this Section consumes, requires it. *)
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw)
    (AsanInitK.inp argv envp fs stdin uid gid hw groups net nofile sigmask abrt sdf ur kb execfn).
  Hypothesis Hvl : valid_launch (AsanInitK.inp argv envp fs stdin uid gid hw groups net nofile sigmask abrt sdf ur kb execfn).
  Hypothesis HRZ : r = AsanPlanCoreK.APCK.rseq_z (kb_rseq (in_kernel (AsanInitK.inp argv envp fs stdin uid gid hw groups net nofile sigmask abrt sdf ur kb execfn))).
  Remark r01 : 0 <= r <= 1.
  Proof. rewrite HRZ. apply AsanPlanCoreK.APCK.rseq_z_range. Qed.
  Hypothesis Huid : valid_id uid. Hypothesis Hhw : valid_hwcap hw. Hypothesis Hvfs : valid_fs fs.
  #[local] Notation SINV := (SINV0 APH0 sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask abrt sdf ur kb execfn apc).
  #[local] Notation argH := (argH0 sp rdraw argv envp fs stdin uid gid hw groups net nofile sigmask abrt sdf ur kb execfn).
  #[local] Notation CSOK := (APSK.cs_ok ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs).
  #[local] Notation usp := (bv_unsigned sp).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma mp_bud : 0 <= BUDGET /\ 0 <= ArtInv.KMAX /\ 0 <= ArtInv.LENMAX < 2 ^ 62.
  Proof. unfold ArtInv.KMAX, ArtInv.LENMAX. lia. Qed.
  Lemma mp_gap : AsanCeil.bottomup_floor + ArtInv.LENMAX + (17729664876544 + BUDGET) + (23 + ArtInv.KMAX) * (ArtInv.LENMAX + 4095) <= AsanCeil.alloc_ceiling.
  Proof. unfold ArtInv.KMAX, ArtInv.LENMAX, AsanCeil.bottomup_floor, AsanCeil.alloc_ceiling. lia. Qed.
  Lemma mp_gap_h : forall h, (h < 2)%nat ->
    AsanCeil.bottomup_floor + ArtInv.LENMAX + (APK.a_totsz (HSA r h) + BUDGET)
    + (Z.of_nat (length (segments_reserved ASEGS0) + AsanPlanCoreK.APCK.n_resx ASAN0 + length (APK.a_maps (HSA r h))) + ArtInv.KMAX) * (ArtInv.LENMAX + 4095) <= AsanCeil.alloc_ceiling.
  Proof.
    intros h Hh. destruct (HSA_numbers r h Hh) as (N1 & N2 & N3 & N4). rewrite N4, asan0_res_eq. change (AsanPlanCoreK.APCK.n_resx ASAN0) with 2%nat. cbn [length Nat.add]. change (Z.of_nat 23) with 23.
    unfold ArtInv.KMAX, ArtInv.LENMAX, AsanCeil.bottomup_floor, AsanCeil.alloc_ceiling. lia.
  Qed.

  Lemma HSA_pc : forall h, (h < 2)%nat -> APK.pc (HSA r h) = 0x8d9e8.
  Proof. intros [|[|h]] H; [| |lia]; unfold HSA; destruct (Z.eqb r 1); vm_compute; reflexivity. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem as0_main_phase : APSK.holes_stmt ASEGS0 scfg ASAN0 AsanInitK.LIMIT (HS_as0 r) SINV argH (HOLES (fun fs' => spec argv fs')) fs.
  Proof.
    intros h ch Hh E R FULL model HC.
    assert (Hh2 : (h < 2)%nat) by (destruct h as [|[|h]]; [lia | lia | unfold HS_as0 in Hh; destruct (Z.eqb r 1); cbn in Hh; discriminate Hh]).
    rewrite (HSA_some r h Hh2) in Hh. injection Hh as <-.
    assert (EFS : m_fs model = fs).
    { exact (proj2 (ent_model sp brk0 rdraw argv envp uid hw fs mbase stdin gid groups net nofile sigmask abrt sdf ur kb execfn apc r HRZ (HSA r h) (drv_chk_HSA r h r01 Hh2) E R FULL model HC)). }
    unfold HOLES. rewrite EFS.
    destruct (Nat.eq_dec (length argv) 2) as [Hargc|Hargc]; [|exact (USAGE sp brk0 rdraw argv envp uid hw fs mbase stdin gid groups net nofile sigmask abrt sdf ur kb execfn apc r Hsp Hva Hve Hfit Hvfs Hlau Hvl HRZ h Hh2 E R FULL model HC Hargc)].
    destruct argv as [|a0s [|path [|x l]]] eqn:Hargv; try discriminate Hargc. clear Hargc.
    (* [comment removed for export] *)
    set (cs := HSA r h). set (rn := as0_rn E cs). set (ar := as0_ar E cs).
    set (MAPS0 := vm_maps (m_vmmaps model)). set (RESV0 := vm_reserved (m_vmmaps model)). set (NOACC0 := vm_noaccess (m_vmmaps model)).
    pose proof (as0_art_handoff_h sp brk0 rdraw [a0s; path] envp uid hw fs mbase stdin gid groups net nofile sigmask abrt sdf ur kb execfn apc Hsp Hva Hve Hfit Hlau BUDGET BUD_ge BUD_hi r h Hh2 E R FULL model HC) as HT.
    pose proof (as0_handoff_static sp brk0 rdraw [a0s; path] envp uid hw fs mbase stdin gid groups net nofile sigmask abrt sdf ur kb execfn apc BUDGET ArtInv.LENMAX ArtInv.KMAX mp_bud mp_gap r h Hh2 E R FULL model HC) as BS.
    rewrite (as0_RES_art r h Hh2 E) in BS. fold cs rn in BS.
    (* the telescope of [hbi_sp0], which is
       what [sp0_val] goes through; [As0DrvEntryK]'s own [Section Entry] block
       is [As0Layout]'s, declared as the block after [fs] then [Hlau] after
       [Hfit]. *)
    pose proof (sp0_val sp brk0 rdraw [a0s; path] envp uid hw fs mbase stdin gid groups net nofile sigmask abrt sdf ur kb execfn apc r Hsp Hva Hve Hfit Hlau HRZ BUDGET ArtInv.LENMAX ArtInv.KMAX (HSA r h) (drv_chk_HSA r h r01 Hh2) (mp_gap_h h Hh2)
                  E R FULL model HC) as SPV.
    pose proof HT as (REP & _ & _ & _ & CLI & _). destruct REP as (ROK & _).
    assert (HIok : asan_iface_ok L ar C scfg (HIA BUDGET MAPS0 RESV0 NOACC0 (as0_BASEx cs E) rn)).
    { apply (INST_OK MAPS0 RESV0 NOACC0 (as0_BASEx cs E) rn); [exact BS | exact ROK | reflexivity | reflexivity | reflexivity | reflexivity]. }
    assert (FNok : afree_null_spec L ar scfg (HIA BUDGET MAPS0 RESV0 NOACC0 (as0_BASEx cs E) rn)).
    { apply (FREE_NULL MAPS0 RESV0 NOACC0 (as0_BASEx cs E) rn); [exact BS | exact ROK | reflexivity | reflexivity | reflexivity | reflexivity]. }
    set (HI := HIA BUDGET MAPS0 RESV0 NOACC0 (as0_BASEx cs E) rn) in *.
    pose proof (H4E _ _ _ _ _ _ _ _ _ _ _ _ HT) as RI. fold HI in RI.
    assert (SPT : ar_sptop ar = usp) by exact SPV.
    assert (ICok : aicpt_ok L ar IL scfg HI).
    { apply (ICPT_OK MAPS0 RESV0 NOACC0 (as0_BASEx cs E) rn); [exact BS | exact ROK | reflexivity | reflexivity | reflexivity | reflexivity]. }
    destruct (LIB_OK ar HI HIok ICok) as (LayL & LIok). pose proof (DLA_OK ar HI sp HIok SPT) as DL.
    (* [comment removed for export] *)
    pose proof (as0_EXTRA_wf cs E) as XWF.
    assert (XBL : 16515072 + 2460874240 + A_bytes (as0_EXTRA cs E) + BUDGET <= AsanInitK.LIMIT).
    { unfold as0_EXTRA. cbn [A_bytes fst snd]. unfold AsanInitK.LIMIT, target_alloc_limit. lia. }
    (* the four [as0_main_*] share one telescope ([As0DrvEntryInst], [Proof using All]) *)
    destruct (as0_main_entry sp brk0 rdraw a0s path envp uid hw fs mbase stdin gid groups net nofile sigmask abrt sdf ur kb execfn apc r Hsp Hva Hve Hfit Hlau Hvl HRZ BUDGET ArtInv.LENMAX ArtInv.KMAX mp_bud (as0_EXTRA cs E) XWF XBL mp_gap
                h Hh2 E R FULL model HC) as (can & tid & HR & HK & LZ & FDS & _ & STR).
    pose proof (as0_main_auxv sp brk0 rdraw a0s path envp uid hw fs mbase stdin gid groups net nofile sigmask abrt sdf ur kb execfn apc r Hsp Hva Hve Hfit Hlau Hvl HRZ BUDGET ArtInv.LENMAX ArtInv.KMAX mp_bud (as0_EXTRA cs E) XWF XBL mp_gap
                h Hh2 E R FULL model HC) as AUXA.
    destruct LZ as (_ & _ & _ & MI & HALT).
    destruct CLI as (_ & _ & _ & _ & S1 & S2 & S3 & S4 & S5 & _).
    cbn [as0_rn rn_ar as0_ar ar_stack_top ar_stack_bottom ar_sptop] in S1, S2, S3, S4, S5.
    assert (SDEF : defined FULL usp (ar_stack_top ar - usp)).
    { apply (as0_main_stack_defined sp brk0 rdraw a0s path envp uid hw fs mbase stdin gid groups net nofile sigmask abrt sdf ur kb execfn apc r Hsp Hva Hve Hfit Hlau Hvl HRZ BUDGET ArtInv.LENMAX ArtInv.KMAX mp_bud (as0_EXTRA cs E) XWF XBL mp_gap
               h Hh2 E R FULL model HC); unfold ar, cs; cbn [as0_ar ar_stack_top]; rewrite SPV in *.
      - rewrite S5. rewrite <- Z.add_mod_idemp_l by lia. rewrite S3. reflexivity.
      - lia. }
    assert (DI : dinv ar HI sp FULL [] [] (8192, 2 ^ 34) (as0_A0x cs E) FULL model).
    { apply DINV; [exact RI | exact MI | exact HALT | reflexivity | | | exact (APSK.co_rdr _ _ _ _ _ _ _ _ _ _ _ HC)].
      intros x Hx. apply (as0_stksh_main sp brk0 rdraw [a0s; path] envp uid hw fs mbase stdin gid groups net nofile sigmask abrt sdf ur kb execfn apc Hsp Hva Hve Hfit Hlau r h Hh2 E R FULL model HC).   (* [comment removed for export] *) unfold STKTOP, ar, cs in Hx. cbn [as0_ar ar_sptop ar_stack_top] in Hx. rewrite SPV in Hx. exact Hx.
      intros x Hx. apply (as0_stksh_main_hi sp brk0 rdraw [a0s; path] envp uid hw fs mbase stdin gid groups net nofile sigmask abrt sdf ur kb execfn apc Hsp Hva Hve Hfit Hlau r h Hh2 E R FULL model HC). unfold ahl_ceil, ar, cs in Hx. cbn [as0_ar ar_sptop] in Hx. rewrite SPV in Hx. exact Hx. }
    destruct (STR 1%nat ltac:(lia)) as (STR1 & PV1 & PH1). cbn [nth] in STR1, PH1.
    (* argv[1] at 727298f3: [cat_argv_ptr top argv envp execfn 1] = [STR0 + |argv[0]| + 1], the
       [p1] of [as0_main_entry]'s environment *)
    assert (T1 : Z.of_nat (total_arg_bytes_nat (firstn 1 [a0s; path])) = Z.of_nat (length a0s) + 1)
      by (unfold total_arg_bytes_nat; cbn [firstn fold_right]; lia).
    assert (CP1 : cat_argv_ptr (ed_top rdraw) [a0s; path] envp execfn 1 = Z_to_bv 64 (bv_unsigned (cat_argv_ptr (ed_top rdraw) [a0s; path] envp execfn 1)))
      by (symmetry; apply Z_to_bv_bv_unsigned).
    rewrite PV1, T1, Z.add_assoc in CP1. rewrite PV1, T1 in PH1.
    unfold APSK.cfg_of, cs. rewrite (HSA_pc h Hh2). fold cs.
    refine (DRV_MAIN Halloc Hfs DRV_CONSTS sp a0s path envp fs Hsp Hva Hve Hvfs ar HI _ _ can tid _ (as0_A0x cs E) (8192, 2 ^ 34) R FULL model HIok FNok ICok LIok DL HR HK _ DI SDEF FDS EFS _ _ eq_refl _ _).
    - (* the auxv at [auxvp], slot 5 of the main environment: [usp + 8*envc + 40] *)
      exact AUXA.
    - rewrite <- CP1. exact STR1.
    - rewrite <- CP1, PV1, T1. lia.
    - rewrite <- CP1. intros i Hi.
      exact (as0_main_str_defined sp brk0 rdraw a0s path envp uid hw fs mbase stdin gid groups net nofile sigmask abrt sdf ur kb execfn apc r Hsp Hva Hve Hfit Hlau Hvl HRZ BUDGET ArtInv.LENMAX ArtInv.KMAX mp_bud (as0_EXTRA cs E) XWF XBL mp_gap
               h Hh2 E R FULL model HC 1%nat ltac:(lia) i Hi).
    - pose proof HT as (_ & _ & _ & _ & CLI' & _). destruct CLI' as (_ & _ & SAH & _). exact SAH.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem as0_realizes_spec_run :
    srealizes ASEGS0 scfg (init_config ASEGS0 Asan.M.init_pc APH0 sp brk0 mbase rdraw AsanInitK.LIMIT
                                 (AsanInitK.inp argv envp fs stdin uid gid hw groups net nofile sigmask abrt sdf ur kb execfn))
              (spec argv fs).
  Proof.
    (* [As0StartupFinalK]'s [as0_startup_closed] takes the main phase's holes at the
       run's own flag; [as0_main_phase] states them at [r], which [HRZ] ties to it. *)
    pose proof as0_main_phase as HM. rewrite HRZ in HM.
    exact (as0_startup_closed scfg Halloc sp brk0 mbase rdraw argv envp fs stdin uid gid hw groups net nofile sigmask abrt sdf ur kb execfn
             Hsp Hbrk Hmb Hva Hve Hfit Huid Hhw Hvl Hlau (fun fs' => spec argv fs') (fun fs' => spec_has_nil argv fs') HM).
  Qed.
End MainPhase.
