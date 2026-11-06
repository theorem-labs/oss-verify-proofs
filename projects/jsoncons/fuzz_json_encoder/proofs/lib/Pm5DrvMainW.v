(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk StreamSim ShapeAlg SpinAlg Hoare AsanAcctShape FileSim SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4
  RefNodes HeapIface HeapIfaceA PmHeapIfaceA HeapIfaceANull IcptIfaceA PmIcptIfaceA Pm5IcptLayout PmIcptDrvA LibIface PmLibIfaceA DrvKitA DrvNodesLazyK As0DrvKitA Pm5DrvEntry Pm5Drv_defs Pm5DrvLib Pm5DrvRead Pm5DrvA
  Pm5DrvG_defs Pm5DrvG Pm5DrvC_defs Pm5DrvC Pm5DrvD_defs Pm5DrvLibL Pm5DrvD Pm5DrvE_defs Pm5DrvStdio Pm5DrvLibInit Pm5DrvE Pm5DrvE2 AsanPlanSoundK Pm5MainPhaseA
  Pm5DrvC Pm5DrvD Pm5DrvHRead Pm5DrvH Pm5DrvOpenFail Pm5DiagArmRefuse Pm5DrvMain PmLibIfaceAW Pm5DrvLibLW Pm5DrvE2W Pm5MainPhaseAW.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import ShapeLaws AgentLib Spec BigintSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Import SX2. Import SX2S.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Existing Instance PropExec.fx0.
Section MainW.
Variable scfg : SpuriousCfg.
Variable PHI : list byte -> Prop.

(* [comment removed for export] *)
Definition drv_main_onW (P : list byte -> Fs.Fs -> Prop) (KP : list byte -> Fs.Fs -> TSet)
           (L : asan_layout) (C : asan_statics_cells) (IL : icpt_layout) (Lay : lib_layoutA) (LSt : asan_run -> lib_statics) (B0 : Z) : Prop :=   (* [comment removed for export] *)
  sc_alloc scfg = false -> sc_fs scfg = true -> drv_consts_stmt L C IL ->
  forall (sp : word) (a0s path : list byte) (envp : list (list byte)) (fs : Fs.Fs),
    valid_sp sp -> valid_argv [a0s; path] -> valid_envp envp -> valid_fs fs -> phi_okD PHI path fs -> P path fs ->
  forall (ar : asan_run) (HI : asan_iface) (p0 p1 can tid : word) (A0 : list (Z * Z)) (cr0 : credit)
         (R : bvmap 5 word) (M0 : word -> option byte) (model : Model),
    asan_iface_ok L ar C scfg HI -> afree_null_spec L ar scfg HI -> aicpt_ok L ar IL scfg HI -> lib_iface_okDW Lay ar scfg HI (LSt ar) PHI -> drv_layoutA L ar IL sp ->
    SX2S.regs_ok (env_mainA sp p0 p1 can tid R) sr_mainA R ->
    SX2S.know_ok ASEGS (env_mainA sp p0 p1 can tid R) (mrestrict (ahid A0 model) M0) kn_mainA ->
    auxv_atA sp p0 M0 ->
    dinv ar HI sp M0 [] [] cr0 A0 M0 model ->
    defined M0 (bv_unsigned sp) (ar_stack_top ar - bv_unsigned sp) ->
    m_fds model = APSK.fds_std -> m_fs model = fs ->
    rdn ASEGS (mrestrict (ahid A0 model) M0) p1 (length path + 1) = Some (path ++ [Z_to_bv 8 0]) ->
    bv_unsigned sp <= bv_unsigned p1 /\ bv_unsigned p1 + Z.of_nat (length path) + 1 + 16 <= 2 ^ 47 ->
    cr0 = (8192, B0) ->
    defined M0 (bv_unsigned p1) (Z.of_nat (length path) + 1 + 16) ->
    shadow_allowed A0 (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) ->
    srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0xb0980) M0 (seg_rom ASEGS)) model) (KP path fs).
Definition dg_nofile_stmtW := drv_main_onW (fun path fs => (4096 <= length path)%nat \/ path = [] \/ (path <> dot_path /\ fs_lookup fs path = None))
                                           (fun path fs => t_die (msg_cannot_open path) fs).
Definition dg_dot_stmtW := drv_main_onW (fun path _ => path = dot_path) (fun path fs => t_alt2 (t_die (msg_cannot_open path) fs) (t_die (msg_read_error path) fs)).

Theorem dg_nofile_of_openerrW : forall (L : asan_layout) (C : asan_statics_cells) (IL : icpt_layout) (Lay : lib_layoutA) (LSt : asan_run -> lib_statics) (B0 : Z),
  dg_openerr_stmt scfg L C IL -> dg_nofile_stmtW L C IL Lay LSt B0.
Proof.
  intros L C IL Lay LSt B0 DG_OPENERR.
  unfold dg_nofile_stmtW, drv_main_onW.
  intros Halloc Hfs CONSTS sp a0s path envp fs Hvsp Hva Hve Hvfs HPHIOK Hcase ar HI p0 p1 can tid A0 cr0 R M0 model HIok FNok ICok LIok DL HR HK AUXV DI M0def FDS EFS STR PLO Ecr PDEF SAH.
  assert (Hsp : 0x7fff80000000 <= bv_unsigned sp <= 2 ^ 47) by (destruct Hvsp as (H1 & H2 & H3); unfold sp_window_lo, sp_window_hi in H1, H2; lia).
  assert (Hal : bv_unsigned sp mod 16 = 0) by (destruct Hvsp as (_ & _ & H3); exact H3).
  pose proof CONSTS as CONSTS'. destruct CONSTS as (ILY & HRD & Hkpm & Hlin & Hovh & HPR & HEX & _).
  assert (CTX : drv_ctxA scfg L C IL ar HI sp M0) by (constructor; try assumption).
  assert (Hnonul : ~ In (Z_to_bv 8 0) path).
  { destruct Hva as (_ & _ & _ & Hnn & _). inversion Hnn as [|x l _ Hn2]; subst. inversion Hn2 as [|y l2 Hy _]; subst. exact Hy. }
  assert (Hplen131 : Z.of_nat (length path) <= 131071).
  { destruct Hva as (_ & _ & Hfa & _). inversion Hfa as [|x l _ Hf2]; subst. inversion Hf2 as [|y l2 Hy _]; subst. exact Hy. }
  pose proof (dinv_lzinv scfg L ar C IL HI HIok sp DL M0 _ _ _ _ _ _ DI) as (HOFF & _).
  assert (STRF : rdn ASEGS M0 p1 (length path + 1) = Some (path ++ [Z_to_bv 8 0])) by (exact (rdn_of_mrestrict ASEGS _ M0 HOFF _ _ _ STR)).
  assert (PTH : drv_pathA sp M0 p1 path) by (constructor; assumption).
  destruct main_nb as (NB1 & NB2).
  unfold env_mainA in HR, HK.
  pose proof (regs_ok_nb _ _ (blobs_ev [[]; []; []; []; []]) _ _ NB1 HR) as HR'.
  pose proof (know_ok_nb ASEGS _ _ (blobs_ev [[]; []; []; []; []]) _ _ NB2 HK) as HK'.
  apply (open_fail_nofileA scfg L ar C IL HI HIok sp Hsp Hal DL path fs p0 p1 can M0 Hnonul ltac:(lia) STRF [] cr0 A0
           (t_die (msg_cannot_open path) fs) R model tid); try assumption.
  - destruct Hcase as [H1|[H2|[Hnd Hlk]]]; [left; exact H1 | right; left; exact H2 |].
    destruct (list_byte_eqb path []) eqn:Hemp; [right; left; apply list_byte_eqb_iffA; exact Hemp|].
    right. right. split; [intros E; apply list_byte_eqb_iffA in E; rewrite E in Hemp; discriminate Hemp|]. split; [|exact Hlk].
    destruct Hva as (_ & _ & _ & _ & Htl). cbn [tl] in Htl. inversion Htl as [|p' l' [Hsl Hdd] _]; subst.
    unfold openat_plain_name, path_is_dirref. rewrite Hsl, Hdd.
    lazymatch goal with |- context [path_eqb path ?d] => destruct (path_eqb path d) eqn:E; [|reflexivity] end.
    exfalso. apply Hnd. apply path_eqb_eq in E. rewrite E. reflexivity.
  - exact (DG_OPENERR ar HI sp M0 CTX path fs [] p1 cr0 A0 PTH SAH).
Qed.

Theorem dg_dot_ofW : forall (L : asan_layout) (C : asan_statics_cells) (IL : icpt_layout) (Lay : lib_layoutA) (LSt : asan_run -> lib_statics) (B0 : Z),
  drv_lib_layoutA Lay L -> drv_budgetA L Lay B0 ->
  dg_openerr_stmt scfg L C IL -> dg_readerr_stmt scfg L C IL -> dg_dot_stmtW L C IL Lay LSt B0.
Proof.
  intros L C IL Lay LSt B0 DLL HBUD DG_OPENERR DG_READERR.
  unfold dg_dot_stmtW, drv_main_onW.
  intros Halloc Hfs CONSTS sp a0s path envp fs Hvsp Hva Hve Hvfs HPHIOK Hdot ar HI p0 p1 can tid A0 cr0 R M0 model HIok FNok ICok LIok DL HR HK AUXV DI M0def FDS EFS STR PLO Ecr PDEF SAH.
  subst path.
  assert (Hsp : 0x7fff80000000 <= bv_unsigned sp <= 2 ^ 47) by (destruct Hvsp as (H1 & H2 & H3); unfold sp_window_lo, sp_window_hi in H1, H2; lia).
  assert (Hal : bv_unsigned sp mod 16 = 0) by (destruct Hvsp as (_ & _ & H3); exact H3).
  pose proof CONSTS as CONSTS'. destruct CONSTS as (ILY & HRD & Hkpm & Hlin & Hovh & HPR & HEX & _).
  assert (CTX : drv_ctxA scfg L C IL ar HI sp M0) by (constructor; try assumption).
  pose proof (dinv_lzinv scfg L ar C IL HI HIok sp DL M0 _ _ _ _ _ _ DI) as (HOFF & _).
  assert (STRF : rdn ASEGS M0 p1 (length dot_path + 1) = Some (dot_path ++ [Z_to_bv 8 0])) by (exact (rdn_of_mrestrict ASEGS _ M0 HOFF _ _ _ STR)).
  assert (Hnonul : ~ In (Z_to_bv 8 0) dot_path) by (cbn; intros [E0|[]]; apply (f_equal bv_unsigned) in E0; vm_compute in E0; lia).
  assert (PTH : drv_pathA sp M0 p1 dot_path) by (constructor; try assumption; cbn; lia).
  change (Z.of_nat (length dot_path)) with 1 in PLO.
  subst cr0.
  (* [comment removed for export] *)
  assert (Hcr : acredit_ok L (8192, B0) 65536).
  { destruct (dlla_credit_pos Lay L DLL 0 ltac:(lia)) as [CP1 CP2].
    pose proof (HBUD 0 ltac:(lia)) as (HB1 & HB2).
    unfold credA, adebit, acredit_ok, CAPk in *. cbn [fst snd] in *. rewrite Z.pow_0_r in HB2. nia. }
  destruct main_nb as (NB1 & NB2).
  unfold env_mainA in HR, HK.
  pose proof (regs_ok_nb _ _ (blobs_ev [[]; []; []; []; []]) _ _ NB1 HR) as HR'.
  pose proof (know_ok_nb ASEGS _ _ (blobs_ev [[]; []; []; []; []]) _ _ NB2 HK) as HK'.
  apply (@drv_dirA PropExec.fx0 scfg L ar C IL HI HIok sp Hsp Hal DL HRD fs p0 p1 can M0 M0def Hfs ltac:(lia) STRF [] (8192, B0) A0 Hcr
           (t_die (msg_cannot_open dot_path) fs) (t_die (msg_read_error dot_path) fs) R model tid HR' HK' DI FDS EFS).
  - exact (DG_OPENERR ar HI sp M0 CTX dot_path fs [] p1 (8192, B0) A0 PTH SAH).
  - exact (DG_READERR ar HI sp M0 CTX fs p0 p1 can (8192, B0) A0 PTH SAH).
  - unfold t_die. apply ShapeAlg.t_emit_has_nil.
Qed.

Theorem as0_drv_mainW : forall (L : asan_layout) (C : asan_statics_cells) (IL : icpt_layout) (Lay : lib_layoutA) (LSt : asan_run -> lib_statics) (B0 : Z),
  drv_lib_layoutA Lay L -> drv_lib_cellsA Lay -> drv_budgetA L Lay B0 ->
  dg_openerr_stmt scfg L C IL -> dg_short_stmt scfg L C IL -> dg_overrun_stmt scfg L C IL -> dg_refuse_stmt scfg L C IL ->
  dg_nofile_stmtW L C IL Lay LSt B0 -> dg_dot_stmtW L C IL Lay LSt B0 ->
  drv_main_stmtW scfg L C IL Lay LSt B0 PHI.
Proof.
  intros L C IL Lay LSt B0 DLL DLC HBUD DG_OPENERR DG_SHORT DG_OVERRUN DG_REFUSE DG_NOFILE DG_DOT.
  unfold drv_main_stmtW.
  intros Halloc Hfs CONSTS sp a0s path envp fs Hvsp Hva Hve Hvfs HPHIOK ar HI p0 p1 can tid A0 cr0 R M0 model HIok FNok ICok LIok DL HR HK AUXV DI M0def FDS EFS STR PLO Ecr PDEF SAH.
  cbn [spec].
  destruct (Nat.leb_spec0 4096 (length path)) as [Hlong|Hshort].
  { exact (DG_NOFILE Halloc Hfs CONSTS sp a0s path envp fs Hvsp Hva Hve Hvfs HPHIOK (or_introl Hlong) ar HI p0 p1 can tid A0 cr0 R M0 model HIok FNok ICok LIok DL HR HK AUXV DI M0def FDS EFS STR PLO Ecr PDEF SAH). }
  destruct (list_byte_eqb path []) eqn:Hemp.
  { apply list_byte_eqb_iffA in Hemp.
    exact (DG_NOFILE Halloc Hfs CONSTS sp a0s path envp fs Hvsp Hva Hve Hvfs HPHIOK (or_intror (or_introl Hemp)) ar HI p0 p1 can tid A0 cr0 R M0 model HIok FNok ICok LIok DL HR HK AUXV DI M0def FDS EFS STR PLO Ecr PDEF SAH). }
  assert (Hne : path <> []) by (intros E; apply list_byte_eqb_iffA in E; rewrite E in Hemp; discriminate).
  destruct (list_byte_eqb path dot_path) eqn:Hdot.
  { apply list_byte_eqb_iffA in Hdot.
    exact (DG_DOT Halloc Hfs CONSTS sp a0s path envp fs Hvsp Hva Hve Hvfs HPHIOK Hdot ar HI p0 p1 can tid A0 cr0 R M0 model HIok FNok ICok LIok DL HR HK AUXV DI M0def FDS EFS STR PLO Ecr PDEF SAH). }
  assert (Hnd : path <> dot_path) by (intros E; apply list_byte_eqb_iffA in E; rewrite E in Hdot; discriminate).
  destruct (fs_lookup fs path) as [fdata|] eqn:Hlk.
  2:{ exact (DG_NOFILE Halloc Hfs CONSTS sp a0s path envp fs Hvsp Hva Hve Hvfs HPHIOK (or_intror (or_intror (conj Hnd Hlk))) ar HI p0 p1 can tid A0 cr0 R M0 model HIok FNok ICok LIok DL HR HK AUXV DI M0def FDS EFS STR PLO
               Ecr PDEF SAH). }
  (* [comment removed for export] *)
  assert (Hsp : 0x7fff80000000 <= bv_unsigned sp <= 2 ^ 47) by (destruct Hvsp as (H1 & H2 & H3); unfold sp_window_lo, sp_window_hi in H1, H2; lia).
  assert (Hal : bv_unsigned sp mod 16 = 0) by (destruct Hvsp as (_ & _ & H3); exact H3).
  pose proof CONSTS as CONSTS'. destruct CONSTS as (ILY & HRD & Hkpm & Hlin & Hovh & HPR & HEX & _).
  assert (CTX : drv_ctxA scfg L C IL ar HI sp M0) by (constructor; try assumption).
  assert (Hppl : openat_plain_name path = true).
  { destruct Hva as (_ & _ & _ & _ & Htl). cbn [tl] in Htl. inversion Htl as [|p' l' [Hsl Hdd] _]; subst.
    unfold openat_plain_name, path_is_dirref. rewrite Hsl, Hdd.
    lazymatch goal with |- context [path_eqb path ?d] => destruct (path_eqb path d) eqn:E; [|reflexivity] end.
    exfalso. apply Hnd. apply path_eqb_eq in E. rewrite E. reflexivity. }
  assert (Hnonul : ~ In (Z_to_bv 8 0) path).
  { destruct Hva as (_ & _ & _ & Hnn & _). inversion Hnn as [|x l _ Hn2]; subst. inversion Hn2 as [|y l2 Hy _]; subst. exact Hy. }
  assert (Hplen131 : Z.of_nat (length path) <= 131071).
  { destruct Hva as (_ & _ & Hfa & _). inversion Hfa as [|x l _ Hf2]; subst. inversion Hf2 as [|y l2 Hy _]; subst. exact Hy. }
  pose proof (dinv_lzinv scfg L ar C IL HI HIok sp DL M0 _ _ _ _ _ _ DI) as (HOFF & _).
  assert (STRF : rdn ASEGS M0 p1 (length path + 1) = Some (path ++ [Z_to_bv 8 0])) by (exact (rdn_of_mrestrict ASEGS _ M0 HOFF _ _ _ STR)).
  assert (PTH : drv_pathA sp M0 p1 path) by (constructor; assumption).
  subst cr0. destruct LIok as (LSAx & LIok & LSXa).
  (* [comment removed for export] *)
  set (PLv := Z.max 0 (Z.min (PLA fdata) 67108863)).
  assert (HPLv : 0 <= PLv < 67108864) by lia.
  destruct (dlla_credit_pos Lay L DLL PLv ltac:(lia)) as [CP1 CP2].
  pose proof (HBUD PLv HPLv) as HB. pose proof HB as (HB1 & HB2).
  assert (Hcr65536 : acredit_ok L (8192, B0) 65536).
  { unfold credA, adebit, acredit_ok, CAPk in *. cbn [fst snd] in *. rewrite Z.pow_0_r in HB2. nia. }
  destruct main_nb as (NB1 & NB2).
  unfold env_mainA in HR, HK.
  pose proof (regs_ok_nb _ _ (blobs_ev [[]; []; []; []; fdata]) _ _ NB1 HR) as HR'.
  pose proof (know_ok_nb ASEGS _ _ (blobs_ev [[]; []; []; []; fdata]) _ _ NB2 HK) as HK'.
  apply (@drv_openA PropExec.fx0 scfg L ar C IL HI HIok sp Hsp Hal DL path fs fdata p0 p1 can M0 M0def Hlk Hne Hppl Hfs ltac:(lia) Hnonul ltac:(lia) STRF [] (8192, B0) A0 Hcr65536
           (t_die (msg_cannot_open path) fs) (t_body fdata fs) R model tid HR' HK' DI FDS EFS).
  - exact (DG_OPENERR ar HI sp M0 CTX path fs fdata p1 (8192, B0) A0 PTH SAH).
  - apply (@drv_fileA PropExec.fx0 scfg L ar C IL HI HIok ICok ILY sp Hsp Hal DL HRD (conj Hkpm (conj Hlin Hovh)) path fs fdata p0 p1 can M0 M0def Hlk [] A0
             (hl_k_per_malloc L + 4 * fst (lla_credit Lay PLv)) (hl_b_lin L * PLv + hl_b_overhead L + 4 * snd (lla_credit Lay PLv)) ltac:(lia) ltac:(nia)
             (t_body fdata fs) (t_body_nilA fdata fs)); [ | | exact HB].
    + (* [comment removed for export] *)
      intros Hlt CAP crC HCAP HltC HK1 HB1'.
      destruct (Nat.lt_ge_cases (length fdata) 6) as [Hs|Hge6].
      { rewrite (t_body_shortA fdata fs) by (unfold MAX_INPUT; lia). exact (DG_SHORT ar HI sp M0 CTX fs fdata p0 p1 can A0 CAP crC HCAP HltC Hs). }
      destruct (Z.lt_ge_cases (Z.of_nat (length fdata)) (6 + CFGA fdata)) as [Hov|Hok].
      { rewrite (t_body_overrunA fdata fs) by (unfold MAX_INPUT; lia). exact (DG_OVERRUN ar HI sp M0 CTX fs fdata p0 p1 can A0 CAP crC HCAP HltC Hge6 Hov). }
      rewrite (t_body_okA fdata fs) by (unfold MAX_INPUT; lia).
      apply (@hdr_okA PropExec.fx0 scfg L ar C IL HI HIok sp Hsp Hal DL fs fdata p0 p1 can M0 [] A0 CAP HCAP crC HltC Hok); [| apply t_emit_has_nil].
      assert (HPLeq : PLA fdata = PLv) by (unfold PLv, PLA; pose proof (CFGA_range sp fdata); lia).
      apply (@drv_targetA PropExec.fx0 scfg L ar C IL HI HIok ICok sp Hsp Hal DL fs fdata p0 p1 can M0 M0def [] A0 CAP HCAP crC HltC Hok); [ | | apply t_emit_has_nil | exact FPSteps.fp_frm_zero_fx0].
      * intros HPLp. unfold acredit_ok. rewrite HPLeq. lia.
      * assert (Hp4096 : (length path < 4096)%nat) by lia.
        assert (HPHI : PHI (payloadA fdata)) by (apply (HPHIOK Hp4096 Hne Hnd fdata Hlk); unfold MAX_INPUT in *; lia).
        apply (@drv_loopA scfg L ar C IL HI HIok ICok sp Hsp Hal DL fs fdata p0 p1 can M0 M0def A0 CAP HCAP HltC Lay (LSt ar) ILY HPR DLL DLC LSAx PHI LIok HPHI [] crC AUXV).
        -- (* [comment removed for export] *)
           pose proof (CALLSA_range sp fdata) as HCL.
           unfold Pm5DrvE.lib_roomA, Pm5DrvE.credit_scaleA, credit_le, cr1A. rewrite HPLeq. cbn [fst snd].
           split.
           ++ destruct (PLv =? 0)%Z eqn:EP; unfold adebit; cbn [fst snd]; split; nia.
           ++ intros c Hc. destruct (dlla_frames Lay L DLL c Hc) as (LK1 & LK2). change (ff_count c []) with 0%nat. change (Z.of_nat 0) with 0. nia.
        -- exact (tail_XA scfg L ar C IL HI HIok ICok sp Hsp Hal DL fs fdata p0 p1 can M0 M0def A0 CAP HCAP Lay (LSt ar) ILY HEX FNok LSAx DLL (lioaw_exit _ _ _ _ _ _ _ LIok) LSXa).
    + (* [comment removed for export] *)
      intros Hge. rewrite (t_body_refusedA fdata fs) by (unfold MAX_INPUT; lia).
      exact (DG_REFUSE ar HI sp M0 CTX path fs fdata p0 p1 can A0 Hlk Hge).
  - apply t_body_nilA.
Qed.
End MainW.
