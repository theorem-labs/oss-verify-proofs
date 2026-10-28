(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import ModelAmb.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import H0Lim.   (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.openssl.hashtable.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk SimInv ExitSim ShapeAlg ShapeLaws Nodes
  MmapSim AllocSim FileSim AgentLib SpecConsts MemSplit Frame
  SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymAbove LibKnowFrame
  Spec RefNodes RefNodesEx PhaseG RefNodesG
  HUStartupDefs HUStartup HUMainEntryDefs HUMainEntry HUMainEntryN
  HUWorld HUReadBase HUReadStage HUReadChunk HURead0 HUReadErr_defs HUReadErr
  HUPilotOOM_defs HUPilotOOM HUOpenFailBranch HUDirWalk.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require HUW65x.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import HU_code_277000_278000 HU_code_dd000_de000.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import ConeCfg.   (* [comment removed for export] *)
Import ListNotations.
Import ConeCfg.
Open Scope bv_scope.
Import SX2. Import SX2S.
Import HUReadChunk.H0ReadChunkW.
Import ConeCfg.

#[local] Abbreviation RSEGS := Ubsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
#[local] Ltac inlist := cbv [In front_kept loopB_kept direrr_kept]; tauto.
(* [comment removed for export] *)
#[local] Ltac rne := let E := fresh "E" in intros E; apply (f_equal bv_unsigned) in E; vm_compute in E; lia.

(* [comment removed for export] *)
Tactic Notation "gg_block_keep" constr(scr) constr(NX) := gg_block_gen FUEL STOPS scr NX true.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record dir_tail_pre (sp0 p1 : word) (tid can : Z) (mem0 : word -> option byte)
       (R : bvmap 5 word) (M : word -> option byte) : Prop := DIR_TAIL_PRE {
  dt_sp : getr R 2 = Z_to_bv 64 (bv_unsigned sp0 - 128);
  dt_gp : getr R 3 = Z_to_bv 64 0x10800;
  dt_tp : getr R 4 = Z_to_bv 64 0x331ae8;
  dt_s2 : getr R 18 = p1;                                  (* [comment removed for export] *)
  dt_stack : stack_writable M sp0;
  dt_img : Forall (fun iv => img_clear M (fst iv) (snd iv)) re_ivs;
  dt_tid : cell M 0x331a40 4 tid;
  dt_tidr : (0 < tid < 2 ^ 22)%Z;
  dt_self : cell M 0x331a20 8 0x331a20;
  dt_canary : cell M 0x351b28 8 can;
  dt_canr : (0 <= can < 2 ^ 64)%Z;
  dt_pagesz : cell M 0x351da8 8 4096;
  dt_above : above_eq sp0 mem0 M
}.

Section DirTail.
  Variable sp0 : word.
  Variable a0s : list byte.
  Variable envv : list (list byte).
  Variables uid hw : word.
  Variable rdraw : EntryDraw.
  Variable tid : word.
  Variable regs0 : bvmap 5 word.
  Variable mem0 : word -> option byte.
  Hypothesis Hva : valid_argv [a0s; dot_path].
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Hfits : entry_stack_fits sp0 [a0s; dot_path] envv.
  Hypothesis ME : main_entry sp0 [a0s; dot_path] envv uid hw rdraw tid regs0 mem0.

  Theorem dir_tail : forall (R : bvmap 5 word) (M : word -> option byte) (model : Model) (can : Z),
    m_halted model = None -> m_vm_lazy model = [] ->
    fd_lookup (m_fds model) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
    dir_tail_pre sp0 (p1 sp0 a0s dot_path envv) (bv_unsigned tid) can mem0 R M ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0xe1bdc) M (seg_rom RSEGS)) model)
               (t_die (msg_read_error dot_path) (m_fs model)).
  Proof.
    intros R M model can Hh Hlazy Hfd2 P.
    destruct P as [Rsp Rgp Rtp Rs2 Mstack Mimg Mtid Htidr Mself Mcanary Hcan Mpagesz Habove].
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi.
    unfold sp_window_lo, sp_window_hi in SPlo, SPhi.
    edestruct (main_strN sp0 [a0s; dot_path] envv uid hw rdraw tid regs0 mem0 Hva Hve Hvsp Hfits ME 1%nat) as (Sr & Slo & Shi & Slen & [t8 Ht8] & Send);
      [cbn; lia|].
    cbn [nth length Nat.add dot_path app] in Sr, Slo, Shi, Ht8, Send.
    set (pp := p1 sp0 a0s dot_path envv) in *.
    change (cat_argv_ptr sp0 [a0s; dot_path] envv 1) with pp in Sr, Slo, Shi, Ht8, Send.
    change (Z.of_nat 1) with 1%Z in Ht8, Send.
    pose proof (u64_range pp) as Hppr.
    assert (Hstr : rdn RSEGS M pp 2 = Some [Z_to_bv 8 46; Z_to_bv 8 0]).
    { rewrite <- Sr. apply rdn_agree. intros j Hj. apply Habove. rewrite u_small by lia. lia. }
    assert (Ht8' : rdn RSEGS M (Z_to_bv 64 (bv_unsigned pp + 1)) 8 = Some t8).
    { rewrite <- Ht8. apply rdn_agree. intros j Hj. apply Habove.
      rewrite (u_small (bv_unsigned pp + 1)) by lia. rewrite u_small by lia. lia. }
    apply (ref_read_error_dot sp0 [] model Hvsp Hh Hlazy Hfd2 pp (bv_unsigned tid) can R M
             Rsp Rgp Rtp Rs2 Mstack Mimg Mtid Htidr Mself Mcanary Hcan Mpagesz Slo t8 ltac:(lia) Hstr Ht8').
  Qed.
End DirTail.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma fd3_dir : fd_lookup (HUW65x.H0W65.fdsV FdDir) (Z_to_bv 64 3) = Some FdDir.
Proof. vm_compute. reflexivity. Qed.

Lemma access_okb_stage : access_okb (Z_to_bv 64 STAGE) 65536 = true.
Proof. apply access_okb_true_intro; [lia|]. unfold STAGE. rewrite u_small by lia. lia. Qed.

(* [comment removed for export] *)
Definition modelDir (VM : VmMaps) (stdin0 : AmbIn) (fs0 : Fs) (tid : word) : Model :=
  mkModelA (HUW65x.H0W65.fdsV FdDir) VM stdin0 fs0 None (Some tid) None.

Section DirMid.
  Variable sp0 : word.
  Variable a0s : list byte.
  Variable envv : list (list byte).
  Variable tid : word.
  Variable mem0 : word -> option byte.
  Variable fs0 : Fs.
  Variable stdin0 : AmbIn.

  (* [comment removed for export] *)
  Theorem dir_read : forall mode Q K,
    (forall R' M' VM' (can : Z), dir_tail_pre sp0 (p1 sp0 a0s dot_path envv) (bv_unsigned tid) can mem0 R' M' ->
       GG RSEGS mode Q K (mkCfg (mkst R' (Z_to_bv 64 0xe1bdc) M' (seg_rom RSEGS)) (modelDir VM' stdin0 fs0 tid))) ->
    HUW65x.after_malloc_gen sp0 a0s dot_path envv tid fs0 stdin0 mode Q FdDir (above_eq sp0 mem0) K.
  Proof.
    intros mode Q K TAIL R M VM mb bw gm can sec area brkv mas EA EB RP W MF VP VS HA.
    change (mkModelA (HUW65x.H0W65.fdsV FdDir) VM stdin0 fs0 None (Some tid) None) with (modelDir VM stdin0 fs0 tid).
    pose proof RP as [Rsp Rgp Rtp Rs0 Ra0 Rs2 Rs4 Rs5 Hsp Hp1 Hb Hbi Hgm Hgb Hst Hgr Hmw Her Hsw Hkm].
    pose proof (u64_range sp0) as Hspw. pose proof (u64_range gm) as Hgmw.
    (* [comment removed for export] *)
    destruct (front_walk R M (seg_rom RSEGS) (bv_unsigned gm + 32) Ra0 ltac:(lia) Rs5)
      as (R1 & RUN1 & A9 & A23 & A19 & A22 & AK).
    replace (Z_to_bv 64 0xe19e0) with (0xe19e0 : word) by (apply bv_eq; reflexivity).
    eapply gg_msteps; [reflexivity | reflexivity | exact RUN1 |].
    (* [comment removed for export] *)
    assert (SOK136 : store_ok RSEGS M (Z_to_bv 64 (bv_unsigned sp0 - 136)) 8 = true).
    { replace (bv_unsigned sp0 - 136)%Z with (bv_unsigned sp0 - 8388608 + (8388608 - 136))%Z by lia. apply Hst; lia. }
    assert (SOK144 : store_ok RSEGS M (Z_to_bv 64 (bv_unsigned sp0 - 144)) 8 = true).
    { replace (bv_unsigned sp0 - 144)%Z with (bv_unsigned sp0 - 8388608 + (8388608 - 144))%Z by lia. apply Hst; lia. }
    destruct (walkA R1 M (seg_rom RSEGS) (bv_unsigned sp0) (bv_unsigned gm + 32) 0 65536) as
      (R2 & RUN2 & B17 & B10 & B11 & B12 & B1 & B2 & B9 & B19 & BK).
    { rewrite (AK 2%bv) by inlist. exact Rsp. }
    { exact A19. }
    { rewrite (AK 21%bv) by inlist. exact Rs5. }
    { exact A9. }
    { rewrite (AK 20%bv) by inlist. exact Rs4. }
    { exact A22. }
    { lia. }
    { lia. }
    { lia. }
    { lia. }
    { exact SOK136. }
    eapply gg_msteps; [reflexivity | reflexivity | exact RUN2 |].
    set (M1 := wbytes M (Z_to_bv 64 (bv_unsigned sp0 - 136)) (word_to_le_bytes 8 (Z_to_bv 64 0xe1a88))).
    (* [comment removed for export] *)
    eapply (gg_read_dir RSEGS mode Q R2 (0x2bd1dc : word) M1 (modelDir VM stdin0 fs0 tid) W_2775f0 (Z_to_bv 64 3) K F_2775f0 E_2775f0).
    - reflexivity.
    - reflexivity.
    - exact B17.
    - exact B10.
    - rewrite u_small by lia. lia.
    - exact fd3_dir.
    - rewrite B11, B12. change (want 65536 0) with 65536%Z. rewrite (u_small 65536) by lia. exact access_okb_stage.
    - (* [comment removed for export] *)
      replace (v_addi (0x2bd1dc : word) 4) with (0x2bd1e0 : word) by (apply bv_eq; reflexivity).
      assert (MG1 : mem_grows M M1) by (subst M1; apply wbytes_grows).
      destruct (direrr_walk (regupd R2 10 (errno_ret EISDIR)) M1 (seg_rom RSEGS) sp0 (Z_to_bv 64 2)) as
        (R3 & RUN3 & C2 & C10 & CK).
      { lia. }
      { rewrite getr_other by rne. exact B1. }
      { rewrite getr_other by rne. rewrite B2. f_equal. }
      { rewrite getr_other by rne. rewrite (BK 4%bv) by inlist. rewrite (AK 4%bv) by inlist. exact Rtp. }
      { rewrite getr_other by rne. rewrite (BK 8%bv) by inlist. rewrite (AK 8%bv) by inlist. exact Rs0. }
      { apply getr_same. rne. }
      { subst M1. apply rdn_wbytes_hit8. rewrite u_small by lia. lia. }
      { eapply store_ok_mono; [exact MG1 | exact SOK136]. }
      { eapply store_ok_mono; [exact MG1 | exact SOK144]. }
      { apply HUExitBase.store_ok_data; rewrite u_small by lia; cbn; lia. }
      eapply gg_msteps; [reflexivity | reflexivity | exact RUN3 |].
      replace (0xe1bdc : word) with (Z_to_bv 64 0xe1bdc) by (apply bv_eq; reflexivity).
      set (M3 := wbytes (wbytes (wbytes M1 _ _) _ _) _ _).
      (* [comment removed for export] *)
      assert (AG : forall x : word,
                 (bv_unsigned x < 0x331a44 \/ 0x331a48 <= bv_unsigned x)%Z ->
                 (bv_unsigned x < bv_unsigned sp0 - 144 \/ bv_unsigned sp0 - 128 <= bv_unsigned x)%Z ->
                 M3 x = M x).
      { intros x Hx1 Hx2. subst M3 M1.
        rewrite (MemSplit.wbytes_outside _ _ (Z_to_bv 64 0x331a44) x) by (rewrite length_N_to_le_bytes, u_small by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
        rewrite (MemSplit.wbytes_outside _ _ (Z_to_bv 64 (bv_unsigned sp0 - 144)) x) by (rewrite length_N_to_le_bytes, u_small by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
        rewrite (MemSplit.wbytes_outside _ _ (Z_to_bv 64 (bv_unsigned sp0 - 136)) x) by (rewrite length_N_to_le_bytes, u_small by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
        rewrite (MemSplit.wbytes_outside _ _ (Z_to_bv 64 (bv_unsigned sp0 - 136)) x) by (rewrite length_N_to_le_bytes, u_small by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
        reflexivity. }
      assert (MG3 : mem_grows M M3).
      { subst M3. eapply mem_grows_trans; [exact MG1|]. eapply mem_grows_trans; [apply wbytes_grows|].
        eapply mem_grows_trans; apply wbytes_grows. }
      assert (AGc : forall a n v, (0 <= a)%Z -> (a + Z.of_nat n <= 0x331a44 \/ (0x331a48 <= a /\ a + Z.of_nat n <= 0x354000))%Z ->
                    cell M a n v -> cell M3 a n v).
      { intros a n v Ha Hn Hc. eapply cell_agree; [lia | lia | | exact Hc].
        intros i Hi. apply AG; rewrite u_small by lia; lia. }
      apply (TAIL R3 M3 VM (bv_unsigned can)). constructor.
      + exact C2.
      + rewrite (CK 3%bv) by inlist. rewrite getr_other by rne.
        rewrite (BK 3%bv) by inlist. rewrite (AK 3%bv) by inlist. exact Rgp.
      + rewrite (CK 4%bv) by inlist. rewrite getr_other by rne.
        rewrite (BK 4%bv) by inlist. rewrite (AK 4%bv) by inlist. exact Rtp.
      + rewrite (CK 18%bv) by inlist. rewrite getr_other by rne.
        rewrite (BK 18%bv) by inlist. rewrite (AK 18%bv) by inlist. exact Rs2.
      + eapply stack_writable_grows; [exact MG3 | exact Hst].
      + (* [comment removed for export] *)
        pose proof (re_ivs_of_world M (w_img _ _ _ _ _ _ _ _ _ W)) as Himg.
        apply Forall_forall. intros [lo hi] Hin. pose proof (proj1 (Forall_forall _ _) Himg _ Hin) as Hc. cbn [fst snd] in *.
        assert (Hiv : (0x10000 <= lo /\ hi <= 0x354000 /\ (hi <= 0x331a44 \/ 0x331a48 <= lo))%Z).
        { unfold re_ivs in Hin. cbn in Hin.
          repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; lia|]). destruct Hin. }
        intros i Hi. rewrite AG; [apply Hc; exact Hi | rewrite u_small by lia; lia | rewrite u_small by lia; lia].
      + apply AGc; [lia | cbn; lia | exact (w_tid _ _ _ _ _ _ _ _ _ W)].
      + pose proof (w_tidr _ _ _ _ _ _ _ _ _ W). lia.
      + apply AGc; [lia | cbn; lia | exact (w_self _ _ _ _ _ _ _ _ _ W)].
      + apply AGc; [lia | cbn; lia | exact (w_canary _ _ _ _ _ _ _ _ _ W)].
      + apply u64_range.
      + apply AGc; [lia | cbn; lia | exact (w_pagesz _ _ _ _ _ _ _ _ _ W)].
      + eapply above_eq_step; [| exact HA]. intros a Ha. apply AG; lia.
  Qed.

  (* [comment removed for export] *)
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis Hva : valid_argv [a0s; dot_path].
  Hypothesis Hve : valid_envp envv.
  Variables (rdraw : EntryDraw) (brk mbase : word).
  Hypothesis Hbrk : valid_brk RSEGS brk.
  Variable lim : Z.                              (* [comment removed for export] *)
  Hypothesis lim_ge : (LIM <= lim)%Z.

  Lemma dot_len : (length dot_path <= 4095)%nat.
  Proof. cbn. lia. Qed.

  Theorem dir_brk : forall mode Q K,
    (exists s : Z, (bv_unsigned sp0 + 192 <= s < 2 ^ 47 - 32)%Z /\ (s mod 8 = 0)%Z /\ mem0 (Z_to_bv 64 s) = Some (Z_to_bv 8 0)) ->   (* [comment removed for export] *)
    HUW65x.after_malloc_gen sp0 a0s dot_path envv tid fs0 stdin0 mode Q FdDir (above_eq sp0 mem0) K ->
    brk_ok_branch_G sp0 a0s dot_path envv rdraw tid mem0 brk mbase fs0 stdin0 lim mode Q FdDir K.     (* [comment removed for export] *)
  Proof.
    intros mode Q K Hhi0 AM.
    exact (HUW65x.brk_ok_sem_g sp0 a0s dot_path envv rdraw tid mem0 brk mbase fs0 stdin0 lim lim_ge Hva Hve Hvsp Htid Hbrk dot_len Hhi0 mode Q FdDir K AM).
  Qed.

  (* [comment removed for export] *)
End DirMid.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section DirFront.
  Variable sp0 : word.
  Variable a0s : list byte.
  Variable envv : list (list byte).
  Variable rdraw : EntryDraw.
  Variable tid : word.
  Variable regs0 : bvmap 5 word.
  Variable mem0 : word -> option byte.
  Variable brk : word.
  Variable mbase : word.
  Variable fs0 : Fs.
  Variable stdin0 : AmbIn.
  Variable lim : Z.                              (* [comment removed for export] *)
  Hypothesis lim_ge : (LIM <= lim)%Z.
  Hypothesis Hvsp : valid_sp sp0.
  Let path := dot_path.
  Let ENV := HUPilotOOM.ENV a0s path rdraw.
  Let valsP := HUPilotOOM.valsP sp0 a0s path envv rdraw tid regs0.
  Let model0 := HUPilotOOM.model0 sp0 a0s path envv tid brk mbase fs0 stdin0 lim.
  Let model1g := HUPilotOOM.model1g sp0 tid brk mbase fs0 stdin0 lim.
  Hypothesis HR0 : regs_ok (ENV valsP) sr_main regs0.
  Hypothesis HK0 : know_ok RSEGS (ENV valsP) mem0 kn_exec.
  Hypothesis Hstr : rdn RSEGS mem0 (p1 sp0 a0s path envv) (length path + 1) = Some (path ++ [Z_to_bv 8 0]).
  Hypothesis Hstr_lo : (bv_unsigned sp0 <= bv_unsigned (p1 sp0 a0s path envv))%Z.
  Hypothesis Hstr_hi : (bv_unsigned (p1 sp0 a0s path envv) + Z.of_nat (length path) + 1 <= 0x800000000000)%Z.
  Hypothesis Hbrk : valid_brk RSEGS brk.

  Lemma dot_nonul : ~ In (Z_to_bv 8 0) dot_path.
  Proof. cbn. intros [E|[]]. apply (f_equal bv_unsigned) in E. vm_compute in E. lia. Qed.

  Lemma dir_seg1 : forall mode Q KA KBb,     (* [comment removed for export] *)
    (mode = true -> open_err_branch sp0 a0s path envv rdraw tid mem0 brk mbase fs0 stdin0 lim KA) ->
    brk_ok_branch_G sp0 a0s path envv rdraw tid mem0 brk mbase fs0 stdin0 lim mode Q FdDir KBb ->
    GG RSEGS mode Q (t_alt2 KA KBb)
       (mkCfg (mkst regs0 (Z_to_bv 64 0xe1984) mem0 (seg_rom RSEGS)) model0).
  Proof.
    intros mode Q KA KBb HKA HKBb.
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi.
    unfold sp_window_lo, sp_window_hi in *.
    pose proof HR0 as HR. pose proof HK0 as HK. subst valsP. unfold HUPilotOOM.valsP in HR, HK.
    set (vals := vals0 sp0 a0s path envv tid regs0 ++ _) in *.
    assert (HL : length vals = 41%nat) by (subst vals; unfold vals0; rewrite !length_app, junk_vals_length; reflexivity).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P1 : vals_ev vals 1 = p0 sp0 a0s path envv) by reflexivity.
    assert (P2 : vals_ev vals 2 = p1 sp0 a0s path envv) by reflexivity.
    assert (P5t : vals_ev vals 5 = tid) by reflexivity.
    pose proof Hstr as Sr. pose proof Hstr_lo as Slo.
    clearbody vals. subst ENV.
    (* [comment removed for export] *)
    gg_block_keep scr0 41%nat.
    (* [comment removed for export] *)
    assert (Sr' : rdn RSEGS M (p1 sp0 a0s path envv) (length path + 1) = Some (path ++ [Z_to_bv 8 0])).
    { rewrite EQM. rewrite (rdn_mem_denot_above RSEGS (HUPilotOOM.ENV a0s path rdraw vals) mem0 _ 0%nat 0x354000);
        [exact Sr | vm_compute; reflexivity | cbn [ev HUPilotOOM.ENV]; rewrite P0; lia | cbn [ev HUPilotOOM.ENV]; rewrite P0; lia | lia
        | lia]. }
    (* [comment removed for export] *)
    eapply (gg_openat_dot RSEGS _ _ _ model0 ECALLW); try apply is_ecall_ECALLW.
    - vm_compute. reflexivity.
    - reflexivity.
    - reflexivity.
    - regv HR (17 : reg). reflexivity.
    - regv HR (10 : reg). apply bv_eq. reflexivity.
    - regv HR (12 : reg). vm_compute. reflexivity.
    - (* [comment removed for export] *) subst model0. rewrite m0_fds. rewrite alloc_fd_fds0. apply fd_lookup_fds0_3.
    - (* [comment removed for export] *) split; [cbn; lia|]. split; [apply dot_nonul|].
      regv HR (11 : reg). cbn [edenot ev HUPilotOOM.ENV]. rewrite P2. exact Sr'.
    - (* [comment removed for export] *)
      intros Hmode e He. rewrite v_addi_pc4 by lia. change (0x2bd1dc + 4)%Z with 0x2bd1e0%Z.
      lazymatch type of HR with regs_ok _ ?sr ?Rc =>
        pose proof (env_app_regs vals [errno_ret e] _ sr Rc ltac:(rewrite HL; vm_compute; reflexivity) HR) as HR2 end.
      lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
        pose proof (env_app_know RSEGS vals [errno_ret e] _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2 end.
      change (Env (vals_ev (vals ++ [errno_ret e])) (blobs_ev (blobs0 a0s path rdraw))) with (HUPilotOOM.ENV a0s path rdraw (vals ++ [errno_ret e])) in HR2, HK2.
      eapply (HKA Hmode e (vals ++ [errno_ret e])); try eassumption.
      + rewrite length_app, HL. reflexivity.
      + rewrite vals_ev_app_l by (rewrite HL; lia). exact P0.
      + rewrite <- HL, <- (Nat.add_0_r (length vals)). rewrite vals_ev_app_r. reflexivity.
      + rewrite vals_ev_app_l by (rewrite HL; lia). exact P1.
      + rewrite vals_ev_app_l by (rewrite HL; lia). exact P2.
      + rewrite vals_ev_app_l by (rewrite HL; lia). exact P5t.
      + apply regs_set_a0; [exact HR2|]. cbn [edenot ev HUPilotOOM.ENV].
        rewrite <- HL, <- (Nat.add_0_r (length vals)). rewrite vals_ev_app_r. reflexivity.
      + intros x Hx. rewrite EQM. apply (mem_denot_above (HUPilotOOM.ENV a0s path rdraw vals) mem0 _ 0%nat 0x354000);
          [vm_compute; reflexivity | cbn [ev HUPilotOOM.ENV]; rewrite P0; lia | cbn [ev HUPilotOOM.ENV]; rewrite P0; lia | lia].
    - (* [comment removed for export] *)
      rewrite v_addi_pc4 by lia. change (0x2bd1dc + 4)%Z with 0x2bd1e0%Z.
      subst model0. rewrite m0_fds. rewrite alloc_fd_fds0.
      change (with_fds (fd_insert fds0 (Z_to_bv 64 3) FdDir) (HUPilotOOM.model0 sp0 a0s path envv tid brk mbase fs0 stdin0 lim))
        with (model1g FdDir).
      pose proof (regs_set_a0 (HUPilotOOM.ENV a0s path rdraw vals) _ _ (Z_to_bv 64 3) (ELit 3) HR eq_refl) as HR2.
      assert (HA : above_sp0 sp0 mem0 M).
      { intros x Hx. rewrite EQM. apply (mem_denot_above (HUPilotOOM.ENV a0s path rdraw vals) mem0 _ 0%nat 0x354000);
          [vm_compute; reflexivity | cbn [ev HUPilotOOM.ENV]; rewrite P0; lia | cbn [ev HUPilotOOM.ENV]; rewrite P0; lia | lia]. }
      eapply (oom_seg2 sp0 a0s path envv rdraw tid mem0 brk mbase fs0 stdin0 lim lim_ge Hvsp Hstr_lo Hstr_hi Hbrk ltac:(cbn; lia)
                mode Q FdDir KBb vals); try eassumption.
  Qed.
End DirFront.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Section LeafDir.
  Variable sp0 : word.
  Variable a0s : list byte.
  Variable envv : list (list byte).
  Variables uid hw : word.
  Variable rdraw : EntryDraw.
  Variable tid : word.
  Variable regs0 : bvmap 5 word.
  Variable mem0 : word -> option byte.
  Variables brk mbase : word.
  Variable fs0 : Fs.
  Variable stdin0 : AmbIn.
  Variable lim : Z.                              (* [comment removed for export] *)
  Hypothesis lim_ge : (LIM <= lim)%Z.
  Hypothesis Hva : valid_argv [a0s; dot_path].
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Hfits : entry_stack_fits sp0 [a0s; dot_path] envv.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 [a0s; dot_path] envv uid hw rdraw tid regs0 mem0.
  Hypothesis Hbrk : valid_brk RSEGS brk.

  (* [comment removed for export] *)
  Theorem dir_path_gg : forall mode Q KA,
    (mode = true -> open_err_branch sp0 a0s dot_path envv rdraw tid mem0 brk mbase fs0 stdin0 lim KA) ->
    (mode = true) ->
    GG RSEGS mode Q (t_alt2 KA (t_opened_dir dot_path fs0))
       (mkCfg (mkst regs0 (Z_to_bv 64 0xe1984) mem0 (seg_rom RSEGS))
              (with_tid tid (init_model (segments_reserved RSEGS) brk mbase sp0 lim (mkProcInputA [a0s; dot_path] envv fs0 stdin0)))).
  Proof.
    intros mode Q KA HKA Hmode.
    pose proof (main_str sp0 a0s dot_path envv uid hw rdraw tid regs0 mem0 Hva Hve Hvsp Hfits ME 1%nat ltac:(lia)) as (Sr & Slo & Shi & Slen & Send).
    cbn [nth length dot_path app Nat.add] in Sr, Slo, Send.
    change (cat_argv_ptr sp0 [a0s; dot_path] envv 1) with (p1 sp0 a0s dot_path envv) in Sr, Slo, Send.
    set (K := t_die (msg_read_error dot_path) fs0).
    assert (AM : HUW65x.after_malloc_gen sp0 a0s dot_path envv tid fs0 stdin0 mode Q FdDir (above_eq sp0 mem0) K).
    { apply (dir_read sp0 a0s envv tid mem0 fs0 stdin0). intros R' M' VM' can P. subst K mode.
      apply gg_of_rz. change fs0 with (m_fs (modelDir VM' stdin0 fs0 tid)).
      exact (dir_tail sp0 a0s envv uid hw rdraw tid regs0 mem0 Hva Hve Hvsp Hfits ME R' M' (modelDir VM' stdin0 fs0 tid) can
               eq_refl eq_refl eq_refl P). }
    change (with_tid tid (init_model (segments_reserved RSEGS) brk mbase sp0 lim (mkProcInputA [a0s; dot_path] envv fs0 stdin0)))
      with (HUPilotOOM.model0 sp0 a0s dot_path envv tid brk mbase fs0 stdin0 lim).
    apply (dir_seg1 sp0 a0s envv rdraw tid regs0 mem0 brk mbase fs0 stdin0 lim lim_ge Hvsp
             (regs_exec_of_main sp0 a0s dot_path envv rdraw tid regs0
                (main_regs_ok sp0 a0s dot_path envv uid hw rdraw tid regs0 mem0 Hvsp Htid ME))
             (know_exec_of_main sp0 a0s dot_path envv rdraw tid regs0 mem0
                (main_know_ok sp0 a0s dot_path envv uid hw rdraw tid regs0 mem0 Hva Hve Hvsp Hfits Htid ME))
             Sr Slo Send Hbrk mode Q KA).
    - exact HKA.
    - exact (dir_brk sp0 a0s envv tid mem0 fs0 stdin0 Hvsp Htid Hva Hve rdraw brk mbase Hbrk lim lim_ge mode Q K
               (main_entry_hi sp0 a0s dot_path envv uid hw rdraw tid regs0 mem0 Hva Hve Hvsp Hfits ME) AM).
  Qed.

  (* [comment removed for export] *)
  Theorem ref_dir_path :
    realizes RSEGS (mkCfg (mkst regs0 (Z_to_bv 64 0xe1984) mem0 (seg_rom RSEGS))
                          (with_tid tid (init_model (segments_reserved RSEGS) brk mbase sp0 lim (mkProcInputA [a0s; dot_path] envv fs0 stdin0))))
             (t_alt2 (t_die (msg_cannot_open dot_path) fs0) (t_opened_dir dot_path fs0)).
  Proof.
    apply (rz_of_gg RSEGS (fun _ => True)). apply (dir_path_gg true (fun _ => True)); [|reflexivity].
    intros _. exact (open_err_branch_cannot_open sp0 a0s dot_path envv uid hw rdraw tid regs0 mem0 brk mbase fs0 stdin0 lim Hva Hve Hvsp Hfits ME).
  Qed.
End LeafDir.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
