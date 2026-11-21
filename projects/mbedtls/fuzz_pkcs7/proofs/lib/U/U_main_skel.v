(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (U_file_exists and U_realizes_spec written out from their encoded form, the initial model carrying the vDSO state and U_realizes_spec taking the in_channel_reader, valid_launch and entry_launch_ok_va premises; the dir lemma's model gains the vDSO state; the proof takes the new process-input fields; file_kont_stmt and dir_kont_stmt pass the entry draw rd to file_seg2_kont_g and dir_seg2_kont). *)
(* [comment removed for export] *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.mbedtls.fuzz_pkcs7.images Require Import Ubsan.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec Shape.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import Amb CatExec CatSim SeqExec StoreOk ShapeX BBFrame
  ShapeLaws SymExec SymExec2 SymExec2Sound SymRun SymDrive.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Spec.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import U_startup U_main_entry U_mainleaf_usage U_mainleaf_openfail U_mainleaf_openfail_branch U_main_open_defs U_main_open U_main_opendir.
#[local] Existing Instance PropExec.fx0.
Import ListNotations.
Import SX2. Import SX2S.
Open Scope bv_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_main_skel () : Init.string Init.list := ["OSSVerify.KrLib.Lib.Shape.realizes"; "OSSVerify.KrImg.Tgt_fuzz_pkcs7_ubsan.M.loaded_segments"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "OSSVerify.KrLib.Lib.PropExec.mkst"; "OSSVerify.KrLib.Lib.PropExec.fx0"; "stdpp.bitvector.definitions.BV"; "Corelib.Init.Logic.I"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"; "LinuxProcessSemantics.LinuxProcessSem.State.with_tid"; "LinuxProcessSemantics.LinuxProcessSem.State.init_model"; "LinuxProcessSemantics.LinuxProcessSem.Run.segments_reserved"; "OSSVerify.KrLib.P.P_lim.LIM"; "OSSVerify.KrLib.BB.Amb.mkProcInputC"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.list"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.nil"; "OSSVerify.KrLib.Lib.Shape.t_alt2"; "OSSVerify.KrLib.Spec.Spec.t_die"; "OSSVerify.KrLib.Spec.Spec.msg_cannot_open"; "OSSVerify.KrLib.Spec.Spec.t_opened"; "LinuxProcessSemantics.LinuxProcessSem.StackLayout.EntryDraw"; "LinuxProcessSemantics.LinuxProcessSem.State.ProcInput"; "LinuxProcessSemantics.LinuxProcessSem.Run.valid_sp"; "LinuxProcessSemantics.LinuxProcessSem.Run.valid_brk"; "usegs'"; "LinuxProcessSemantics.LinuxProcessSem.Run.valid_argv"; "LinuxProcessSemantics.LinuxProcessSem.State.in_argv"; "LinuxProcessSemantics.LinuxProcessSem.Run.valid_envp"; "LinuxProcessSemantics.LinuxProcessSem.State.in_envp"; "LinuxProcessSemantics.LinuxProcessSem.Fs.valid_fs"; "LinuxProcessSemantics.LinuxProcessSem.State.in_fs"; "LinuxProcessSemantics.LinuxProcessSem.Run.entry_stack_fits"; "LinuxProcessSemantics.LinuxProcessSem.Run.init_config"; "upc"; "uph"; "OSSVerify.KrLib.Spec.Spec.spec"].


Definition usegs' := Ubsan.M.loaded_segments.   (* [comment removed for export] *)
Definition upc := Ubsan.M.init_pc.
Definition uph := Ubsan.M.phdrs.

Lemma ref_list_byte_eqb_eq : forall p q, list_byte_eqb p q = true <-> p = q.
Proof.
  induction p as [|a p IH]; destruct q as [|b q]; cbn; try (split; congruence).
  rewrite Bool.andb_true_iff, IH. unfold bv_eqb. rewrite Z.eqb_eq.
  split.
  - intros [H1 ->]. f_equal. apply bv_eq. exact H1.
  - intros H. injection H. intros -> ->. auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition file_kont_stmt {LM : Lim} : Prop :=
  forall (AMB : Amb) (sp0 : word) (a0s path : list byte) (envv : list (list byte)) (tid : word) (rd : EntryDraw)
         (regs0 : bvmap 5 word) (mem0 : word -> option byte) (brk mbase : word) (fs0 : Fs) (stdin0 : InputStream)
         (fdata : list byte),
    valid_argv [a0s; path] -> valid_envp envv -> valid_sp sp0 -> (0 < bv_unsigned tid < 2 ^ 22)%Z ->
    main_entry sp0 [a0s; path] envv tid rd regs0 mem0 -> valid_brk Ubsan.M.loaded_segments brk ->
    fs_lookup fs0 path = Some fdata -> path <> [] -> path <> dot_path -> (length path <= 4095)%nat ->
    file_seg2_kont_g sp0 a0s path envv tid rd mem0 brk mbase fs0 stdin0 (FdFile path (Z_to_bv 64 0)) (t_opened fdata fs0).

(* [comment removed for export] *)
Definition dir_kont_stmt {LM : Lim} : Prop :=
  forall (AMB : Amb) (sp0 : word) (a0s : list byte) (envv : list (list byte)) (tid : word) (rd : EntryDraw)
         (regs0 : bvmap 5 word) (mem0 : word -> option byte) (brk mbase : word) (fs0 : Fs) (stdin0 : InputStream),
    valid_argv [a0s; dot_path] -> valid_envp envv -> valid_sp sp0 -> (0 < bv_unsigned tid < 2 ^ 22)%Z ->
    main_entry sp0 [a0s; dot_path] envv tid rd regs0 mem0 -> valid_brk Ubsan.M.loaded_segments brk ->
    dir_seg2_kont sp0 a0s envv tid rd mem0 brk mbase fs0 stdin0 (t_opened_dir dot_path fs0).

Section Skel.
  Context {LM : Lim}.   (* [comment removed for export] *)
  Hypothesis FILE : file_kont_stmt.
  Hypothesis DIR : dir_kont_stmt.

  Section FileExists.
    Context {AMB : Amb}.
    Variable sp0 : word.
    Variables a0s path : list byte.
    Variable envv : list (list byte).
    Variable tid : word.
    Variable rd : EntryDraw.
    Variable regs0 : bvmap 5 word.
    Variable mem0 : word -> option byte.
    Variable brk : word.
    Variable mbase : word.
    Variable fs0 : Fs.
    Variable stdin0 : InputStream.
    Variable fdata : list byte.
    Hypothesis Hva : valid_argv [a0s; path].
    Hypothesis Hve : valid_envp envv.
    Hypothesis Hvsp : valid_sp sp0.
    Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
    Hypothesis ME : main_entry sp0 [a0s; path] envv tid rd regs0 mem0.
    Hypothesis Hbrk : valid_brk Ubsan.M.loaded_segments brk.
    Hypothesis Hfile : fs_lookup fs0 path = Some fdata.
    Hypothesis Hpne : path <> [].
    Hypothesis Hpnd : path <> dot_path.
    Hypothesis Hplen : (length path <= 4095)%nat.

    #[using="FILE rd Hva Hve Hvsp Htid ME Hbrk Hfile Hpne Hpnd Hplen"] Theorem U_file_exists : (realizes Ubsan.M.loaded_segments (mkCfg (mkst regs0 (0x1d24c : word) mem0 (seg_rom Ubsan.M.loaded_segments))
                      (with_tid tid (with_vdso a_vdso (init_model (segments_reserved Ubsan.M.loaded_segments) brk mbase sp0 (@LIM LM)
                         (mkProcInputC [a0s; path] envv fs0 stdin0)))))
                (t_alt2 (t_die (msg_cannot_open path) fs0) (t_opened fdata fs0))).
    Proof.
      replace (0x1d24c : word) with (Z_to_bv 64 0x1d24c) by (apply bv_eq; reflexivity).
      change (with_tid tid (with_vdso a_vdso (init_model (segments_reserved Ubsan.M.loaded_segments) brk mbase sp0 LIM (mkProcInputC [a0s; path] envv fs0 stdin0))))
        with (model0 sp0 a0s path envv tid brk mbase fs0 stdin0).
      apply (file_seg1 sp0 a0s path envv tid rd regs0 mem0 brk mbase fs0 stdin0 fdata Hva Hve Hvsp Htid ME Hfile Hpne Hpnd Hplen).
      - apply (open_err_branch_cannot_open sp0 a0s path envv tid rd regs0 mem0 brk mbase fs0 stdin0 Hva Hve Hvsp ME).
      - unfold file_seg2_kont.
        exact (FILE AMB sp0 a0s path envv tid rd regs0 mem0 brk mbase fs0 stdin0 fdata Hva Hve Hvsp Htid ME Hbrk Hfile Hpne Hpnd Hplen).
    Qed.
  End FileExists.

  #[using="DIR"] Lemma U_dir_path {AMB : Amb} : forall (sp0 : word) (a0s : list byte) (envv : list (list byte)) (tid : word) (rd : EntryDraw)
      (regs0 : bvmap 5 word) (mem0 : word -> option byte) (brk mbase : word) (fs0 : Fs) (stdin0 : InputStream),
    valid_argv [a0s; dot_path] -> valid_envp envv -> valid_sp sp0 -> (0 < bv_unsigned tid < 2 ^ 22)%Z ->
    main_entry sp0 [a0s; dot_path] envv tid rd regs0 mem0 -> valid_brk Ubsan.M.loaded_segments brk ->
    realizes Ubsan.M.loaded_segments
      (mkCfg (mkst regs0 (0x1d24c : word) mem0 (seg_rom Ubsan.M.loaded_segments))
             (with_tid tid (with_vdso a_vdso (init_model (segments_reserved Ubsan.M.loaded_segments) brk mbase sp0 LIM
                                       (mkProcInputC [a0s; dot_path] envv fs0 stdin0)))))
      (t_alt2 (t_die (msg_cannot_open dot_path) fs0) (t_opened_dir dot_path fs0)).
  Proof.
    intros sp0 a0s envv tid rd regs0 mem0 brk mbase fs0 stdin0 Hva Hve Hvsp Htid ME Hbrk.
    replace (0x1d24c : word) with (Z_to_bv 64 0x1d24c) by (apply bv_eq; reflexivity).
    change (with_tid tid (with_vdso a_vdso (init_model (segments_reserved Ubsan.M.loaded_segments) brk mbase sp0 LIM (mkProcInputC [a0s; dot_path] envv fs0 stdin0))))
      with (model0 sp0 a0s dot_path envv tid brk mbase fs0 stdin0).
    apply (dir_seg1 sp0 a0s envv tid rd regs0 mem0 brk mbase fs0 stdin0 Hva Hve Hvsp Htid ME).
    - apply (open_err_branch_cannot_open sp0 a0s dot_path envv tid rd regs0 mem0 brk mbase fs0 stdin0 Hva Hve Hvsp ME).
    - exact (DIR AMB sp0 a0s envv tid rd regs0 mem0 brk mbase fs0 stdin0 Hva Hve Hvsp Htid ME Hbrk).
  Qed.

  (* [comment removed for export] *)
  #[using="FILE DIR"] Theorem U_realizes_spec : forall sp brk mbase (rd : EntryDraw) (inp : ProcInput),
    valid_sp sp -> valid_brk usegs' brk ->
    valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) ->
    entry_stack_fits sp (in_argv inp) (in_envp inp) ->
    in_channel_reader inp = true -> valid_launch inp ->
    entry_launch_ok_va Sv48 (mkEntry sp brk mbase rd) inp ->
    realizes usegs' (init_config usegs' upc uph sp brk mbase rd (@LIM LM) inp) (spec (in_argv inp) (in_fs inp)).
  Proof.
    intros sp brk mbase rd [argv envp ifs stdin0 uid gid groups net nf sm hwc ab va ur tm kb ef cr sd st]
      Hsp Hbrk Hva Hve Hfs Hfit Hrd Hvl Hlau.
    (* [comment removed for export] *)
    unfold in_fs in *. cbn [in_argv in_envp in_image_fs in_tmp] in *.
    set (fs0 := fs_seed_tmp ifs tm) in *.
    pose (AMB := amb_of (mkProcInput_full argv envp ifs stdin0 uid gid groups net nf sm hwc ab va ur tm kb ef cr sd st)
                   Hrd (Vdso.vdso_run_init (ed_vdso rd))).
    apply (ref_startup sp brk mbase rd LIM _ _ Hrd Hsp Hbrk Hva Hve Hfit Hvl Hlau).
    change (amb_of _ _ _) with AMB.
    match goal with |- context [init_model ?r ?b ?m ?s ?l (mkProcInput_full _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)] =>
      change (init_model r b m s l (mkProcInput_full argv envp ifs stdin0 uid gid groups net nf sm hwc ab va ur tm kb ef cr sd st))
        with (init_model r b m s l (@mkProcInputC AMB argv envp fs0 stdin0)) end.
    change (Vdso.vdso_run_init (ed_vdso rd)) with (@a_vdso AMB).
    intros tid regs mem Htid ME.
    destruct argv as [|a0s [|path [|x l]]].
    - apply (ref_usage_w sp [] envp tid rd regs mem brk mbase fs0 stdin0 LIM Hva Hve Hsp Htid ME). cbn; lia.
    - apply (ref_usage_w sp [a0s] envp tid rd regs mem brk mbase fs0 stdin0 LIM Hva Hve Hsp Htid ME). cbn; lia.
    - cbn [spec].
      destruct (Nat.leb_spec0 4096 (length path)) as [Hlong|Hshort].
      + apply (ref_open_fail_toolong_w sp a0s path envp tid rd regs mem brk mbase fs0 stdin0 LIM Hva Hve Hsp Htid ME Hlong).
      + destruct (list_byte_eqb path []) eqn:Hemp.
        * apply ref_list_byte_eqb_eq in Hemp.
          apply (ref_open_fail_empty_w sp a0s path envp tid rd regs mem brk mbase fs0 stdin0 LIM Hva Hve Hsp Htid ME Hemp).
        * assert (Hne : path <> []) by (intros E; apply ref_list_byte_eqb_eq in E; rewrite E in Hemp; discriminate).
          destruct (list_byte_eqb path dot_path) eqn:Hdot.
          -- apply ref_list_byte_eqb_eq in Hdot. rewrite Hdot in *.
             apply (U_dir_path sp a0s envp tid rd regs mem brk mbase fs0 stdin0 Hva Hve Hsp Htid ME Hbrk).
          -- assert (Hnd : path <> dot_path)
               by (intros E; apply ref_list_byte_eqb_eq in E; rewrite E in Hdot; discriminate).
             destruct (fs_lookup fs0 path) as [data|] eqn:Hlk.
             ++ apply (U_file_exists sp a0s path envp tid rd regs mem brk mbase fs0 stdin0 data
                         Hva Hve Hsp Htid ME Hbrk Hlk Hne Hnd ltac:(lia)).
             ++ apply (ref_open_fail_absent_w sp a0s path envp tid rd regs mem brk mbase fs0 stdin0 LIM Hva Hve Hsp Htid ME
                         ltac:(lia) Hne Hnd Hlk).
    - apply (ref_usage_w sp (a0s :: path :: x :: l) envp tid rd regs mem brk mbase fs0 stdin0 LIM Hva Hve Hsp Htid ME). cbn; lia.
  Qed.
End Skel.
