(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import ModelAmb.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import H0Lim.   (* [comment removed for export] *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.openssl.hashtable.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Frame
  Spec ShapeLaws ExistsRun PhaseG HUStartup HUMainEntryDefs HUMainEntry
  HUPilotOOM_defs HUPilotOOM HUW65x HULeafWorld HUOomTail HUOpenFailBranch HUReadBase HUReadStage HUTargetPre HUWorld
  HURead0 HULeafBigFile HUHeader_defs HULeafHeader HUMainFile HUTargetFull HTHgTop ConeInput HUUsage HUOpenFail HULeafDir.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import ConeCfg.   (* [comment removed for export] *)
Import ListNotations.
Import ConeCfg.
Open Scope bv_scope.

Definition rsegs := Ubsan.M.loaded_segments.
Definition rpc := Ubsan.M.init_pc.
Definition rph := Ubsan.M.phdrs.
#[local] Abbreviation RSEGS := Ubsan.M.loaded_segments.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma teq_pilot : forall A O K : TSet,
  t_eq (t_alt2 A (t_alt2 (t_alt2 O (t_alt2 O (t_alt2 O K))) (t_alt2 O K))) (t_alt2 A (t_alt2 O K)).
Proof. intros A O K tr. unfold t_alt2. tauto. Qed.

Lemma teq_absorb3 : forall A O B : TSet,
  t_eq (t_alt2 A (t_alt2 O (t_alt2 O B))) (t_alt2 A (t_alt2 O B)).
Proof. intros A O B tr. unfold t_alt2. tauto. Qed.

Lemma t_alt2_congr_r : forall A B B' : TSet, t_eq B B' -> t_eq (t_alt2 A B) (t_alt2 A B').
Proof. intros A B B' H tr. unfold t_alt2. pose proof (H tr). tauto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section FileExists.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variables uid hw : word.
  Variable rdraw : EntryDraw.
  Variable tid : word.
  Variable regs0 : bvmap 5 word.
  Variable mem0 : word -> option byte.
  Variables brk mbase : word.
  Variable fs0 : Fs.
  Variable stdin0 : AmbIn.
  Variable fdata : list byte.
  Variable lim : Z.                              (* [comment removed for export] *)
  Hypothesis lim_ge : (LIM <= lim)%Z.
  Hypothesis Hva : valid_argv [a0s; path].
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 [a0s; path] envv uid hw rdraw tid regs0 mem0.
  Hypothesis Hfits : entry_stack_fits sp0 [a0s; path] envv.
  Hypothesis Hbrk : valid_brk RSEGS brk.
  Hypothesis Hfile : fs_lookup fs0 path = Some fdata.
  Hypothesis Hpne : path <> [].
  Hypothesis Hpns : path_has_slash path = false.
  Hypothesis Hpnd : path_is_dirref path = false.
  Hypothesis Hplen : (length path <= 4095)%nat.

  Let L : Z := Z.of_nat (length fdata).

  (* [comment removed for export] *)
  Lemma after_malloc_main : forall mode Q (KT : TSet),
    (mode = false -> (6 + hdr_cfglen fdata <= L < 67108864)%Z) ->
    (* [comment removed for export] *)
    (forall (can : word) (k buf : Z) (V' : VmMaps) R' M',
       tgt_entry_full sp0 k buf can fdata V' R' M' ->
       GG RSEGS mode Q KT (mkCfg (mkst R' (Z_to_bv 64 0xe1c8c) M' (seg_rom RSEGS)) (model_post V' stdin0 fs0 tid))) ->
    HULeafWorld.after_malloc sp0 a0s path envv tid fs0 stdin0 mode Q (Kdd0a8 fdata fs0 KT).
  Proof.
    intros mode Q KT HLT HTGT.
    unfold HULeafWorld.after_malloc. intros R M VM mb bw gm can sec area brkv mas Harea Hbw RP W MF VP VS.
    apply (file_phase sp0 (p1 sp0 a0s path envv) mb bw gm can sec R M area brkv mas VM path fdata stdin0 fs0 tid
             Hfile Harea Hbw RP W MF VP mode Q KT).   (* [comment removed for export] *)
    - intros Hm. apply (HUOomTail.H0BigLeaves.big_oom_branch sp0 gm area brkv mas tid can sec M path stdin0 fs0 Hvsp W).
    - intros Hm. apply (HUOomTail.H0BigLeaves.big_refused_leaf sp0 gm area brkv mas tid can sec M path stdin0 fs0 Hvsp W).
    - exact HLT.
    - intros k buf V' R' M' TE. exact (HTGT can k buf V' R' M' TE).
  Qed.

  Let model0 : Model :=
    with_tid tid (init_model (segments_reserved RSEGS) brk mbase sp0 lim (mkProcInputA [a0s; path] envv fs0 stdin0)).

  (* [comment removed for export] *)
  Theorem ref_file_exists : forall mode Q (KA KT : TSet),
    (mode = true -> open_err_branch sp0 a0s path envv rdraw tid mem0 brk mbase fs0 stdin0 lim KA) ->
    (mode = false -> (6 + hdr_cfglen fdata <= L < 67108864)%Z) ->
    (* [comment removed for export] *)
    (forall (can : word) (k buf : Z) (V' : VmMaps) R' M',
       tgt_entry_full sp0 k buf can fdata V' R' M' ->
       GG RSEGS mode Q KT (mkCfg (mkst R' (Z_to_bv 64 0xe1c8c) M' (seg_rom RSEGS)) (model_post V' stdin0 fs0 tid))) ->
    GG RSEGS mode Q (t_alt2 KA (Kdd0a8 fdata fs0 KT))     (* [comment removed for export] *)
       (mkCfg (mkst regs0 (Z_to_bv 64 0xe1984) mem0 (seg_rom RSEGS)) model0).
  Proof.
    intros mode Q KA KT HKA HLT HTGT.
    pose proof (main_str sp0 a0s path envv uid hw rdraw tid regs0 mem0 Hva Hve Hvsp Hfits ME 1%nat ltac:(lia)) as (S1 & S2 & S3 & S4 & S5).
    cbn [nth] in S1, S2, S3, S4, S5.
    apply (oom_pilot sp0 a0s path envv rdraw tid regs0 mem0 brk mbase fs0 stdin0 fdata lim lim_ge Hva Hvsp
             (regs_exec_of_main sp0 a0s path envv rdraw tid regs0 (main_regs_ok sp0 a0s path envv uid hw rdraw tid regs0 mem0 Hvsp Htid ME))
             (know_exec_of_main sp0 a0s path envv rdraw tid regs0 mem0 (main_know_ok sp0 a0s path envv uid hw rdraw tid regs0 mem0 Hva Hve Hvsp Hfits Htid ME))
             S1 S2 S5 Hbrk Hfile Hpne Hpns Hpnd Hplen mode Q KA).
    - exact HKA.
    - apply (HULeafWorld.brk_ok_sem sp0 a0s path envv rdraw tid mem0 brk mbase fs0 stdin0 fdata lim lim_ge Hva Hve Hvsp Htid Hbrk Hfile Hpne Hplen
               (main_entry_hi sp0 a0s path envv uid hw rdraw tid regs0 mem0 Hva Hve Hvsp Hfits ME) mode Q).     (* [comment removed for export] *)
      apply after_malloc_main; assumption.
  Qed.
End FileExists.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem h0_reach_target :
  forall lim, (LIM <= lim)%Z ->      (* [comment removed for export] *)
  forall sp brk mbase rnd (inp : ProcInput) a0 path data,
    valid_sp sp -> valid_brk RSEGS brk -> valid_mmap_base mbase ->
    entry_stack_fits sp (in_argv inp) (in_envp inp) ->
    hb_input inp a0 path data ->
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    exists R' M' V' (can : word) (k buf : Z) (tid : word),
      reach RSEGS (init_config RSEGS rpc rph sp brk mbase rnd lim inp)
                  (mkCfg (mkst R' (Z_to_bv 64 0xe1c8c) M' (seg_rom RSEGS)) (model_post V' (amb_of inp) (in_fs inp) tid))
      /\ tgt_entry_full sp k buf can data V' R' M'.
Proof.
  intros lim lim_ge sp brk mbase rnd [argv envp ifs sin uid gid groups net nofile sigmask hwcap abt vasz urnd tmp] a0 path data Hsp Hbrk Hmb Hfits HBI.
  destruct HBI as [Hargv Hva Hve Hplen Hpne Hslash Hdirref Hfile Hlen6 Hcfg Hmax]. cbn [in_argv in_envp in_uid in_hwcap] in *.
  subst argv.
  (* [comment removed for export] *)
  set (stdin0 := mkAmbIn sin uid gid groups net nofile sigmask hwcap abt vasz urnd).
  set (inp0 := mkProcInput_full [a0; path] envp ifs sin uid gid groups net nofile sigmask hwcap abt vasz urnd tmp) in *.
  set (fs0 := in_fs inp0) in *.
  destruct (ref_startup_fwd sp brk mbase rnd lim inp0 Hsp Hva Hve) as (tid & regs & mem & Htid & ME & REACH0).
  change (main_entry sp [a0; path] envp uid hwcap rnd tid regs mem) in ME.
  rewrite (init_model_A_of _ _ _ _ _ inp0) in REACH0.
  change (mkProcInputA (in_argv inp0) (in_envp inp0) (in_fs inp0) (amb_of inp0)) with (mkProcInputA [a0; path] envp fs0 stdin0) in REACH0.
  set (Q := fun c : config => exists R' M' V' (can : word) (k buf : Z),
         c = mkCfg (mkst R' (Z_to_bv 64 0xe1c8c) M' (seg_rom RSEGS)) (model_post V' stdin0 fs0 tid)
         /\ tgt_entry_full sp k buf can data V' R' M').
  assert (G : GG RSEGS false Q (t_alt2 t_nil (Kdd0a8 data fs0 t_nil))
                 (mkCfg (mkst regs (Z_to_bv 64 0xe1984) mem (seg_rom RSEGS))
                        (with_tid tid (init_model (segments_reserved RSEGS) brk mbase sp lim (mkProcInputA [a0; path] envp fs0 stdin0))))).
  { apply (ref_file_exists sp a0 path envp uid hwcap rnd tid regs mem brk mbase fs0 stdin0 data lim lim_ge Hva Hve Hsp Htid ME Hfits Hbrk Hfile Hpne Hslash Hdirref ltac:(lia) false Q t_nil t_nil).
    - intros Hm. discriminate Hm.
    - intros _. pose proof (hdr_cfglen_range data) as CR. rewrite HULeafHeader.H0Header.config_len_hdr in Hcfg. lia.
    - intros can k buf V' R' M' TE. apply gg_here. exists R', M', V', can, k, buf. split; [reflexivity | exact TE]. }
  destruct G as (c' & REACH1 & (R' & M' & V' & can & k & buf & -> & TE)).
  exists R', M', V', can, k, buf, tid. cbn [in_fs]. change (amb_of _) with stdin0.
  split.
  - eapply reach_trans; [| exact REACH1].
    replace (Z_to_bv 64 0xe1984) with (0xe1984 : word) by (apply bv_eq; reflexivity). exact REACH0.
  - exact TE.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ref_list_byte_eqb_eq : forall p q, path_eqb p q = true <-> p = q.
Proof. intros p q. apply path_eqb_eq. Qed.

(* [comment removed for export] *)
Lemma teq_opened : forall path data (fs0 : Fs),
  t_eq (t_alt2 (t_die (msg_cannot_open path) fs0) (Kdd0a8 data fs0 (t_target data fs0)))
       (t_alt2 (t_die (msg_cannot_open path) fs0) (t_opened data fs0)).
Proof.     (* [comment removed for export] *)
  intros path data fs0. unfold t_opened. apply t_alt2_congr_r. apply Kdd0a8_body.
Qed.

(* [comment removed for export] *)
Definition dir_case_stmt : Prop :=
  forall (sp0 : word) (a0s : list byte) (envv : list (list byte)) (uid hw : word) (rdraw : EntryDraw) (tid : word)
         (regs0 : bvmap 5 word) (mem0 : word -> option byte) (brk mbase : word) (fs0 : Fs) (stdin0 : AmbIn) (lim : Z),
    (LIM <= lim)%Z ->      (* [comment removed for export] *)
    valid_argv [a0s; dot_path] -> valid_envp envv -> valid_sp sp0 -> entry_stack_fits sp0 [a0s; dot_path] envv ->
    (0 < bv_unsigned tid < 2 ^ 22)%Z ->
    main_entry sp0 [a0s; dot_path] envv uid hw rdraw tid regs0 mem0 -> valid_brk RSEGS brk ->
    realizes RSEGS (mkCfg (mkst regs0 (0xe1984 : word) mem0 (seg_rom RSEGS))
                          (with_tid tid (init_model (segments_reserved RSEGS) brk mbase sp0 lim (mkProcInputA [a0s; dot_path] envv fs0 stdin0))))
             (t_alt2 (t_die (msg_cannot_open dot_path) fs0) (t_opened_dir dot_path fs0)).

Theorem h0_acc_core : dir_case_stmt -> hu_acc_stmt.
Proof.
  intros DIR. unfold hu_acc_stmt.
  intros lim lim_ge sp brk mbase rnd [argv envp ifs sin uid gid groups net nofile sigmask hwcap abt vasz urnd tmp] Hsp Hbrk Hmb Hfits Hvi Hverdict.   (* [comment removed for export] *)
  cbn [in_argv in_envp in_uid in_hwcap] in *.
  destruct Hvi as (Hva & Hve & Hfs & _).
  (* [comment removed for export] *)
  set (stdin0 := mkAmbIn sin uid gid groups net nofile sigmask hwcap abt vasz urnd).
  set (inp0 := mkProcInput_full argv envp ifs sin uid gid groups net nofile sigmask hwcap abt vasz urnd tmp) in *.
  set (fs0 := in_fs inp0) in *.
  apply ref_startup; try assumption.
  intros tid regs mem Htid ME. change (main_entry sp argv envp uid hwcap rnd tid regs mem) in ME.
  rewrite (init_model_A_of _ _ _ _ _ inp0).
  change (mkProcInputA (in_argv inp0) (in_envp inp0) (in_fs inp0) (amb_of inp0)) with (mkProcInputA argv envp fs0 stdin0).
  change (valid_argv argv) in Hva. change (valid_envp envp) in Hve. change (valid_fs fs0) in Hfs.
  clearbody fs0. subst inp0.
  unfold drv_verdict in Hverdict. unfold spec.
  destruct argv as [|a0s [|path [|x l]]].
  - rewrite (drv_classify_usage [] fs0) by (cbn; lia).
    apply (ref_usage_w sp [] envp uid hwcap rnd tid regs mem brk mbase fs0 stdin0 lim Hva Hve Hsp Hfits Htid ME). cbn; lia.
  - rewrite (drv_classify_usage [a0s] fs0) by (cbn; lia).
    apply (ref_usage_w sp [a0s] envp uid hwcap rnd tid regs mem brk mbase fs0 stdin0 lim Hva Hve Hsp Hfits Htid ME). cbn; lia.
  - unfold drv_classify in *.
    destruct (Nat.leb_spec0 4096 (length path)) as [Hlong|Hshort].
    + apply (ref_open_fail_toolong_w sp a0s path envp uid hwcap rnd tid regs mem brk mbase fs0 stdin0 lim Hva Hve Hsp Hfits Htid ME Hlong).
    + destruct (path_eqb path []) eqn:Hemp.
      * apply ref_list_byte_eqb_eq in Hemp.
        apply (ref_open_fail_empty_w sp a0s path envp uid hwcap rnd tid regs mem brk mbase fs0 stdin0 lim Hva Hve Hsp Hfits Htid ME Hemp).
      * assert (Hne : path <> []) by (intros E; apply ref_list_byte_eqb_eq in E; rewrite E in Hemp; discriminate).
        destruct (path_eqb path dot_path) eqn:Hdot.
        -- apply ref_list_byte_eqb_eq in Hdot. subst path. cbn [hd].
           apply (DIR sp a0s envp uid hwcap rnd tid regs mem brk mbase fs0 stdin0 lim lim_ge Hva Hve Hsp Hfits Htid ME Hbrk).
        -- assert (Hnd : path_is_dirref path = false).
           { unfold path_is_dirref. rewrite Hdot. cbn [orb].
             destruct Hva as (_ & _ & _ & _ & Htl). cbn [tl] in Htl.
             apply Forall_cons_iff in Htl as [[_ Hdd] _]. exact Hdd. }
           assert (Hns : path_has_slash path = false).
           { destruct Hva as (_ & _ & _ & _ & Htl). cbn [tl] in Htl.
             apply Forall_cons_iff in Htl as [[Hs _] _]. exact Hs. }
           destruct (fs_lookup fs0 path) as [data|] eqn:Hlk.
           ++ (* [comment removed for export] *)
              eapply rz_conseq; [| apply (teq_opened path data fs0)].
              apply (rz_of_gg RSEGS (fun _ => True)).
              replace (0xe1984 : word) with (Z_to_bv 64 0xe1984) by (apply bv_eq; reflexivity).
              apply (ref_file_exists sp a0s path envp uid hwcap rnd tid regs mem brk mbase fs0 stdin0 data lim lim_ge
                       Hva Hve Hsp Htid ME Hfits Hbrk Hlk Hne Hns Hnd ltac:(lia) true (fun _ => True)
                       (t_die (msg_cannot_open path) fs0) (t_target data fs0)).
              ** intros _. apply (open_err_branch_cannot_open sp a0s path envp uid hwcap rnd tid regs mem brk mbase fs0 stdin0 lim Hva Hve Hsp Hfits ME).
              ** intros Hm. discriminate Hm.
              ** (* [comment removed for export] *)
                 intros can k buf V' R' M' TEF. exfalso. pose proof (tgt_entry_of_full _ _ _ _ _ _ _ _ TEF) as TE.
                 pose proof (te_len _ _ _ _ _ _ TE) as HL.
                 unfold body_pre_target, MAX_INPUT, HDR_MIN in Hverdict.
                 rewrite HULeafHeader.H0Header.config_len_hdr in Hverdict.
                 pose proof (hdr_cfglen_range data) as CR.
                 apply Bool.orb_true_iff in Hverdict as [Hverdict|Hverdict];
                   [apply Bool.orb_true_iff in Hverdict as [Hverdict|Hverdict]|].
                 --- apply Z.leb_le in Hverdict. lia.
                 --- apply Nat.ltb_lt in Hverdict. lia.
                 --- apply Nat.ltb_lt in Hverdict. lia.
           ++ apply (ref_open_fail_absent_w sp a0s path envp uid hwcap rnd tid regs mem brk mbase fs0 stdin0 lim Hva Hve Hsp Hfits Htid ME
                       ltac:(lia) Hne Hnd Hlk).
  - rewrite (drv_classify_usage (a0s :: path :: x :: l) fs0) by (cbn; lia).
    apply (ref_usage_w sp (a0s :: path :: x :: l) envp uid hwcap rnd tid regs mem brk mbase fs0 stdin0 lim Hva Hve Hsp Hfits Htid ME). cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma dir_case : dir_case_stmt.
Proof.
  unfold dir_case_stmt. intros sp0 a0s envv uid hw rdraw tid regs0 mem0 brk mbase fs0 stdin0 lim lim_ge Hva Hve Hvsp Hfits Htid ME Hbrk.
  replace (0xe1984 : word) with (Z_to_bv 64 0xe1984) by (apply bv_eq; reflexivity).
  exact (HULeafDir.ref_dir_path sp0 a0s envv uid hw rdraw tid regs0 mem0 brk mbase fs0 stdin0 lim lim_ge Hva Hve Hvsp Hfits Htid ME Hbrk).
Qed.

Theorem h0_acc : hu_acc_stmt.
Proof. exact (h0_acc_core dir_case). Qed.
