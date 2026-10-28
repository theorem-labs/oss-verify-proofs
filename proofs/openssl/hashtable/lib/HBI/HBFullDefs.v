(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Namei.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Open.
From OssFuzzTheorems.openssl.hashtable.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import PropExec CatExec ShapeAlg AgentLib AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanNodesIO AsanInit.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import ClaVerdict Spec SpecGen HTSpec.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import CxRel CxPlan CxPlanSound HBPlanImage HBAtable HBOpenDefs HBHdrDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import CAP. Import CXS.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition INITA (sp : word) (rdraw : EntryDraw) (brk0 mbase : word) (lim : Z) (argv envp : list (list byte)) (fs : Fs.Fs) (stdin : InStreams)
                 (uid gid hw : word) (groups : list word) (net : NetQueue) (nofile sigmask : word) : config :=
  init_config HASEGS AsanUbsan.M.init_pc HAPH sp brk0 mbase rdraw lim (inp argv envp fs stdin uid gid hw groups net nofile sigmask).

(* [comment removed for export] *)
Definition ha_full_stmt (KT : list byte -> Fs.Fs -> TSet) : Prop :=
  forall lim, (AsanInit.LIMIT <= lim)%Z ->
  forall sp brk mbase rnd (i : ProcInput),
    valid_sp sp -> valid_brk HASEGS brk -> valid_mmap_base mbase ->
    entry_stack_fits sp (in_argv i) (in_envp i) -> valid_input i ->
    crz HASEGS (init_config HASEGS AsanUbsan.M.init_pc HAPH sp brk mbase rnd lim i) (spec_g KT (in_argv i) (in_fs i)).

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
  forall sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask,
    valid_sp sp -> valid_brk HASEGS brk0 -> valid_argv argv -> valid_envp envp -> entry_stack_fits sp argv envp -> valid_id uid ->
    length argv = 2%nat ->
    forall cont, nth 1 argv [] <> [] -> path_has_slash (nth 1 argv []) = false -> path_is_dirref (nth 1 argv []) = false ->
      (length (nth 1 argv []) <= 4095)%nat -> fs_lookup fs (nth 1 argv []) = Some cont -> CLASS cont ->
      crz HASEGS (INITA sp rdraw brk0 mbase lim argv envp fs stdin uid gid hw groups net nofile sigmask) (T (nth 1 argv []) cont fs).
