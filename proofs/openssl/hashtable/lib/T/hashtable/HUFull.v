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
  Spec SpecGen ShapeLaws ExistsRun PhaseG HUStartup HUMainEntryDefs HUMainEntry
  HUPilotOOM_defs HUPilotOOM HUW65x HULeafWorld HUOomTail HUOpenFailBranch HUReadBase HUReadStage HUTargetPre HUWorld
  HURead0 HULeafBigFile HUHeader_defs HULeafHeader HUMainFile HUTargetFull HTHgTop ConeInput HUUsage HUOpenFail HULeafDir HUMain.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import ConeCfg.   (* [comment removed for export] *)
Import ListNotations.
Import ConeCfg.
Open Scope bv_scope.

#[local] Abbreviation RSEGS := Ubsan.M.loaded_segments.

(* [comment removed for export] *)
Definition tail_stmt (KT : list byte -> Fs -> TSet) : Prop :=
  forall (sp0 tid : word) (stdin0 : AmbIn) (fs0 : Fs) (can : word) (k buf : Z) (fdata : list byte) (V' : VmMaps)
         (R' : bvmap 5 word) (M' : word -> option byte),
    valid_sp sp0 -> (0 < bv_unsigned tid < 2 ^ 22)%Z ->
    tgt_entry_full sp0 k buf can fdata V' R' M' ->
    realizes RSEGS (mkCfg (mkst R' (Z_to_bv 64 0xe1c8c) M' (seg_rom RSEGS)) (model_post V' stdin0 fs0 tid)) (KT fdata fs0).

(* [comment removed for export] *)
Definition h0_full_stmt (KT : list byte -> Fs -> TSet) : Prop :=
  forall lim, (LIM <= lim)%Z ->
  forall sp brk mbase rnd (inp : ProcInput),
    valid_sp sp -> valid_brk RSEGS brk -> valid_mmap_base mbase ->
    entry_stack_fits sp (in_argv inp) (in_envp inp) ->
    valid_input inp ->
    realizes RSEGS (init_config RSEGS rpc rph sp brk mbase rnd lim inp) (spec_g KT (in_argv inp) (in_fs inp)).

(* [comment removed for export] *)
Lemma t_hdr_body_g : forall KT content fs, HULeafHeader.t_hdr content fs (KT content fs) = t_body_g KT content fs.
Proof.
  intros KT content fs. unfold HULeafHeader.t_hdr, HULeafHeader.H0Header.t_hdr, t_body_g, t_body_pre, body_pre_target.
  destruct (MAX_INPUT <=? Z.of_nat (length content))%Z; [reflexivity|].
  destruct (length content <? HDR_MIN)%nat; [reflexivity|]. cbn [orb].
  destruct (length content <? HDR_MIN + config_len content)%nat; reflexivity.
Qed.

Lemma Kdd0a8_body_g : forall KT content fs0, t_eq (Kdd0a8 content fs0 (KT content fs0)) (t_body_g KT content fs0).
Proof.
  intros KT content fs0. unfold Kdd0a8. rewrite t_hdr_body_g.
  destruct (Z.ltb_spec0 (Z.of_nat (length content)) 65536) as [Hs|Hb]; [apply t_eq_refl|].
  destruct (Z.ltb_spec0 (Z.of_nat (length content)) 67108864) as [Hs2|Hb2]; [apply t_eq_refl|].
  unfold t_body_g, t_body_pre, body_pre_target.
  rewrite (proj2 (Z.leb_le MAX_INPUT (Z.of_nat (length content)))) by (unfold MAX_INPUT; lia). apply t_eq_refl.
Qed.

Theorem h0_full : forall KT, tail_stmt KT -> h0_full_stmt KT.
Proof.
  intros KT HT lim lim_ge sp brk mbase rnd inp Hsp Hbrk Hmb Hfits Hvi.
  destruct (drv_verdict (in_argv inp) (in_fs inp)) eqn:Hverdict.
  { rewrite (spec_g_acc KT _ _ Hverdict). exact (h0_acc lim lim_ge sp brk mbase rnd inp Hsp Hbrk Hmb Hfits Hvi Hverdict). }
  destruct inp as [argv envp ifs sin uid gid groups net nofile sigmask hwcap abt vasz urnd tmp].
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
  unfold drv_verdict in Hverdict. unfold spec_g.
  destruct argv as [|a0s [|path [|x l]]];
    try (rewrite (drv_classify_usage _ fs0) in Hverdict by (cbn; lia); discriminate Hverdict).
  unfold drv_classify in *.
  destruct (Nat.leb_spec0 4096 (length path)) as [Hlong|Hshort]; [discriminate Hverdict|].
  destruct (path_eqb path []) eqn:Hemp; [discriminate Hverdict|].
  assert (Hne : path <> []) by (intros E; apply ref_list_byte_eqb_eq in E; rewrite E in Hemp; discriminate).
  destruct (path_eqb path dot_path) eqn:Hdot; [discriminate Hverdict|].
  assert (Hnd : path_is_dirref path = false).
  { unfold path_is_dirref. rewrite Hdot. cbn [orb].
    destruct Hva as (_ & _ & _ & _ & Htl). cbn [tl] in Htl.
    apply Forall_cons_iff in Htl as [[_ Hdd] _]. exact Hdd. }
  assert (Hns : path_has_slash path = false).
  { destruct Hva as (_ & _ & _ & _ & Htl). cbn [tl] in Htl.
    apply Forall_cons_iff in Htl as [[Hs _] _]. exact Hs. }
  destruct (fs_lookup fs0 path) as [data|] eqn:Hlk; [|discriminate Hverdict].
  (* [comment removed for export] *)
  eapply rz_conseq; [| apply t_alt2_congr_r; apply (Kdd0a8_body_g KT data fs0)].
  apply (rz_of_gg RSEGS (fun _ => True)).
  replace (0xe1984 : word) with (Z_to_bv 64 0xe1984) by (apply bv_eq; reflexivity).
  apply (ref_file_exists sp a0s path envp uid hwcap rnd tid regs mem brk mbase fs0 stdin0 data lim lim_ge
           Hva Hve Hsp Htid ME Hfits Hbrk Hlk Hne Hns Hnd ltac:(lia) true (fun _ => True)
           (t_die (msg_cannot_open path) fs0) (KT data fs0)).
  - intros _. apply (open_err_branch_cannot_open sp a0s path envp uid hwcap rnd tid regs mem brk mbase fs0 stdin0 lim Hva Hve Hsp Hfits ME).
  - intros Hm. discriminate Hm.
  - intros can k buf V' R' M' TEF. apply gg_of_rz.
    exact (HT sp tid stdin0 fs0 can k buf data V' R' M' Hsp Htid TEF).
Qed.
