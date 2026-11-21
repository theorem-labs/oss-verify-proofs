(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the state invariants take the launch record [LaunchX], and the argument area is read from it). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Namei.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Open.
From OSSVerify.openssl.hashtable.images Require Import Asan.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import PropExec CatExec ShapeAlg AgentLib AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanNodesIO AsanInit.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import ClaVerdict Spec SpecGen HTSpec.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import CxRel CxPlan CxPlanSound HAPlanImage HAAtable HAOpenDefs HAHdrDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import CAP. Import CXS.
Open Scope Z_scope.

(* [comment removed for export] *)
(* the launch's input fields, mapping base and entry pc come from one [LaunchX] *)
Definition INITA (sp : word) (rdraw : EntryDraw) (brk0 : word) (lim : Z) (argv envp : list (list byte))
                 (uid hw : word) (L : LaunchX) :=
  INITL HASEGS HAPH sp rdraw brk0 lim argv envp uid hw L.

(* [comment removed for export] *)
Definition ha_full_stmt (KT : list byte -> Fs.Fs -> TSet) : Prop :=
  forall lim, (AsanInit.LIMIT <= lim)%Z ->
  forall sp brk mbase rnd (i : ProcInput),
    valid_sp sp -> valid_brk HASEGS brk -> valid_mmap_base mbase ->
    entry_stack_fits sp (in_argv i) (in_envp i) ->
    (* LPS 75d69e00: carried, see HtHaltsLib.full_stmt. *)
    entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) i ->
    valid_input i ->
    crz HASEGS (init_config HASEGS Asan.M.init_pc HAPH sp brk mbase rnd lim i) (spec_g KT (in_argv i) (in_fs i)).

(* [comment removed for export] *)
Definition T_file (path cont : list byte) (fs : Fs.Fs) : TSet := t_alt2 (T_cannot path fs) (t_target_ht cont fs).
Definition refused_lit : list Z := [99; 108; 105; 58; 32; 105; 110; 112; 117; 116; 32; 62; 61; 32; 54; 55; 49; 48; 56; 56; 54; 52; 32; 98; 121; 116; 101; 115; 44; 32; 114; 101; 102; 117; 115; 101; 100; 10].
Definition T_refused (path cont : list byte) (fs : Fs.Fs) : TSet := T_hdr refused_lit path fs.

(* [comment removed for export] *)
Definition K0 (cont : list byte) : Prop := 6 <= flen cont <= 65535 /\ 0 <= ION.room cont.
Definition KGE1 (cont : list byte) : Prop := 65536 <= flen cont <= 2 ^ 26 - 1.
Definition REFUSED (cont : list byte) : Prop := 2 ^ 26 <= flen cont.

(* [comment removed for export] *)
Definition file_leaf_stmt (CLASS : list byte -> Prop) (T : list byte -> list byte -> Fs.Fs -> TSet) : Prop :=
  forall lim, (AsanInit.LIMIT <= lim)%Z ->
  forall sp rdraw brk0 argv envp uid hw (L : LaunchX),
    valid_sp sp -> valid_brk HASEGS brk0 -> valid_argv argv -> valid_envp envp -> entry_stack_fits sp argv envp -> valid_id uid ->
    launchL HAT sp rdraw brk0 argv envp uid hw L ->
    length argv = 2%nat ->
    forall cont, nth 1 argv [] <> [] -> path_has_slash (nth 1 argv []) = false -> path_is_dirref (nth 1 argv []) = false ->
      (length (nth 1 argv []) <= 4095)%nat -> fs_lookup (lx_fs L) (nth 1 argv []) = Some cont -> CLASS cont ->
      crz HASEGS (INITA sp rdraw brk0 lim argv envp uid hw L) (T (nth 1 argv []) cont (lx_fs L)).
