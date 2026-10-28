(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import ModelAmb.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import H0Lim.   (* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.openssl.hashtable.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes MmapSim AllocSim FileSim AgentLib MemSplit Frame StreamSim SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX RefMemcpyLib HUMemcpyBase HUMemcpy MallocDefs HUEnframeBase HUEnframe HUGetMeta HUTargetPre RefNodes ExistsRun PhaseG LibKnowFrame LibKnowXfer RefReadLib HUReadBase HUReadStage HUReadChunk HUReadG0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import ConeCfg.   (* [comment removed for export] *)

(* [comment removed for export] *)
Module H0ReadG5.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.PropExec OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.CatExec OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.CatSim OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.SeqExec OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.StoreOk OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.ShapeAlg OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.Nodes OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.MmapSim OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.AllocSim OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.FileSim OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.AgentLib OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.MemSplit OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.Frame OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.StreamSim OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.SymExec OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.SymExec2 OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.SymExec2Sound OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.SymRun OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.SymDrive OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.SymDriveX OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.RefMemcpyLib HUMemcpyBase HUMemcpy OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.MallocDefs HUEnframeBase HUEnframe HUGetMeta OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.RefNodes OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.LibKnowFrame OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.LibKnowXfer OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.RefReadLib HUReadBase HUReadStage HUReadChunk HUReadG0 HUTargetPre OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.ExistsRun OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.PhaseG HUReadChunk.H0ReadChunkW.
Import ConeCfg.
(* [comment removed for export] *)
(* [comment removed for export] *)

Import ListNotations.
Import ConeCfg.
Open Scope bv_scope.
Import SX2. Import SX2S.
Import ConeCfg.

#[local] Abbreviation RSEGS := Ubsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Tactic Notation "run_block" constr(scr) constr(NX) := run_block_gen RFUEL RSTOPS scr NX false.
#[local] Tactic Notation "run_block_keep" constr(scr) constr(NX) := run_block_gen RFUEL RSTOPS scr NX true.
#[local] Tactic Notation "gg_block" constr(scr) constr(NX) := gg_block_gen RFUEL RSTOPS scr NX false.
#[local] Tactic Notation "gg_block_keep" constr(scr) constr(NX) := gg_block_gen RFUEL RSTOPS scr NX true.

Section G.
  Variables (sp0 p1 mb bw gm can sec : word) (path content : list byte).
  Variables (stdin0 : AmbIn) (fs0 : Fs) (tid : word).
  Hypothesis Hfile : fs_lookup fs0 path = Some content.

  Let L : Z := Z.of_nat (length content).
  #[local] Notation modelG := (HUReadStage.modelG path stdin0 fs0 tid) (only parsing).
  #[local] Notation oom_branch := (HUReadStage.oom_branch sp0 path stdin0 fs0 tid) (only parsing).

  (* [comment removed for export] *)
  Definition half_branch (mode : bool) (Q : config -> Prop) (j' : Z) (M0 : word -> option byte) (K : TSet) : Prop :=
    forall R M V B e, half j' sp0 p1 mb bw gm L B e can sec content M0 R M V ->
      GG RSEGS mode Q K (mkCfg (mkst R (Z_to_bv 64 0xe1a68) M (seg_rom RSEGS)) (modelG (held_of j') V)).

  Ltac note_pres HKold EQM PRES :=
    lazymatch type of EQM with ?Mn = mem_denot ?E ?Mo ?log =>
      lazymatch type of PRES with pres ?Mi _ ?sp =>
        let P := fresh "PRES" in
        assert (P : pres Mi Mn sp)
          by (rewrite EQM; eapply (pres_mem_denot_trans E Mi Mo _ log sp (proj1 HKold));
              [cbn [ev]; assumption | | vm_compute; reflexivity | exact PRES]; assumption);
        clear PRES EQM HKold; try clear Mo; rename P into PRES
      end end.
  Ltac save_know HK := pose proof (conj HK I) as HKb.
  Ltac grow_vals HL extra newlen :=
    lazymatch type of HL with length ?vals = ?n =>
      let HL' := fresh "HL" in
      assert (HL' : length (vals ++ extra) = newlen)
        by (rewrite length_app, ?junk_vals_length, HL; reflexivity);
      repeat match goal with
      | P : vals_ev vals ?i = ?v |- _ =>
          let P' := fresh "P" in
          assert (P' : vals_ev (vals ++ extra) i = v) by (rewrite vals_ev_app_l by (rewrite HL; lia); exact P);
          clear P; rename P' into P
      end;
      let v' := fresh "vals" in
      set (v' := vals ++ extra) in *; clearbody v'; clear HL; try clear vals; rename v' into vals; rename HL' into HL
    end.
  Ltac norm_know HK :=
    lazymatch type of HK with know_ok ?segs ?E ?M ?kn =>
      let kn' := eval vm_compute in kn in
      let EQ := fresh "EQkn" in
      assert (EQ : kn = kn') by (vm_compute; reflexivity);
      try rewrite EQ in HK; clear EQ end.
  Ltac norm_regs HR :=
    lazymatch type of HR with regs_ok ?E ?sr ?R =>
      let sr' := eval vm_compute in sr in
      let EQ := fresh "EQsr" in
      assert (EQ : sr = sr') by (vm_compute; reflexivity);
      try rewrite EQ in HR; clear EQ end.

  Ltac hdr_byte EV42 Pf off :=
    lazymatch type of EV42 with _ = ?B =>
    eapply (kword1_of_mem RSEGS _ _ (EVar 42) _ off _ EV42); [lia | lia | lia |
      lazymatch type of Pf with _ (Z_to_bv 64 ?a) = _ => replace (bv_unsigned B + off)%Z with a by lia; exact Pf end] end.
  Ltac hdr_word EV42 Pf off w z :=
    lazymatch type of EV42 with _ = ?B =>
    eapply (kword_intro RSEGS _ _ (EVar 42) _ off w (ELit z) (Z_to_bv 64 z) EV42 eq_refl); [lia | lia | lia | lia |
      lazymatch type of Pf with rdn _ _ (Z_to_bv 64 ?a) _ = _ => replace (bv_unsigned B + off)%Z with a by lia; exact Pf end] end.

  Theorem grow5 : forall mode Q R M V B e M0 K TOOM,
    full 5 sp0 p1 mb bw gm L B e can sec content M0 R M V ->
    (2097152 <= L)%Z ->
    (0x1000 <= bv_unsigned mb)%Z -> (bv_unsigned mb + 8192 <= bv_unsigned sp0 - 8388608)%Z -> (bv_unsigned mb mod 4096 = 0)%Z ->
    (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z ->
    (mode = true -> oom_branch M0 TOOM) -> half_branch mode Q 6 M0 K ->
    GG RSEGS mode Q K (mkCfg   (* [comment removed for export] *)  (mkst R (Z_to_bv 64 0xe1a24) M (seg_rom RSEGS)) (modelG 2097152 V)).
  Proof.
    intros mode Q R M V B e M0 K TOOM ST HL64 Hmb0 Hmb1 Hmba HspR HOOM HK1.
    (* [comment removed for export] *)
    pose (Mkeep := M).
    destruct ST as ((extra & HLx & HR & HK) & PRES & VS).
    destruct VS as (Vres & Vlim & Visp & rest & Vmaps & Vsz & Vlen & Vlive & Vcont & Vdisj & Vseps & Vlg & Vex).
    change (nb_of 5) with 2101248%Z in Vmaps, Vdisj.
    unfold ENV_RD in HR, HK. set (vals := vals_RD sp0 p1 mb bw gm L B e can sec extra) in *.
    assert (HL : length vals = 42%nat) by (subst vals; unfold vals_RD; rewrite length_app, HLx; reflexivity).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P1 : vals_ev vals 1 = p1) by reflexivity.
    assert (P2 : vals_ev vals 2 = mb) by reflexivity.
    assert (P3 : vals_ev vals 3 = gm) by reflexivity.
    assert (P4 : vals_ev vals 4 = Z_to_bv 64 L) by reflexivity.
    assert (P5 : vals_ev vals 5 = B) by reflexivity.
    assert (P6 : vals_ev vals 6 = e) by reflexivity.
    assert (P7 : vals_ev vals 7 = can) by reflexivity.
    assert (P8 : vals_ev vals 8 = sec) by reflexivity.
    clearbody vals. clear HLx extra.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    norm_know HK. norm_regs HR.
    (* [comment removed for export] *)
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_krange (EVar 5)) in exact i end) _ HK eq_refl) as KB.
    cbn [kentry_ok edenot ev] in KB. subst E. cbn [ev] in KB. rewrite P5 in KB.
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_kalign (EVar 5)) in exact i end) _ HK eq_refl) as KBal.
    cbn [kentry_ok edenot ev] in KBal. cbn [ev] in KBal. rewrite P5 in KBal. destruct KBal as [_ KBal].
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_kdisj (EVar 5) (EVar 2)) in exact i end) _ HK eq_refl) as KBmb.
    cbn [kentry_ok] in KBmb. unfold estart in KBmb. cbn [a_base a_off BA LA MBA edenot ev] in KBmb. rewrite P5, P2 in KBmb.
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_kdisj (EVar 0) (EVar 5)) in exact i end) _ HK eq_refl) as KBD.
    cbn [kentry_ok] in KBD. unfold estart, HUGE in KBD. cbn [a_base a_off BA LA MBA edenot ev] in KBD. rewrite P0, P5 in KBD.
    pose proof (u64_range B) as UB.
    assert (KBD' : (bv_unsigned B + bv_unsigned (snd (B, Z_to_bv 64 0)) <= bv_unsigned B)%Z -> True) by (intros; exact I). clear KBD'.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    (* [comment removed for export] *)
    assert (RL1 : length (pref 1048576 (dropz 1048576 content)) = Z.to_nat 1048576)
      by (pose proof (pref_length 1048576 (dropz 1048576 content) ltac:(lia)); pose proof (dropz_length 1048576 content ltac:(lia)); lia).
    assert (EBc : gblobs content 9%nat = pref 1048576 (dropz 1048576 content))
      by (rewrite <- (gblobs_cb 5) by lia; reflexivity).
      (* [comment removed for export] *)
      save_know HK. gg_block_keep scr0 42%nat. note_pres HKb EQM PRES.
      lazymatch goal with |- GG _ _ _ _ (mkCfg (mkst ?Rc _ ?Mc _) ?MD) =>
        eapply (gg_mmap_anon RSEGS mode Q Rc (Z_to_bv 64 0x2b3e20) Mc MD ECALLW 4194324 TOOM K fetch_26e234 is_ecall_ECALLW eq_refl eq_refl) end.
      + regv HR (17 : reg). reflexivity.
      + regv HR (11 : reg). reflexivity.
      + lia.
      + regv HR (12 : reg). reflexivity.
      + regv HR (13 : reg). reflexivity.
      + regv HR (14 : reg). apply bv_eq. vm_compute. reflexivity.
      + regv HR (15 : reg). reflexivity.
      + (* [comment removed for export] *)
        change (page_round_up_Z 4194324) with 4198400%Z.
        apply grant_exists; [ | | | | apply grant_budget_intro; [reflexivity | reflexivity |]];
          cbv [m_vmmaps HUReadStage.modelG mkModelA m_vm vmst_maps]; rewrite ?Vres, ?Visp, ?Vmaps, ?rsegs_reserved.
        * unfold init_sp_ok. cbv [m_vmmaps HUReadStage.modelG mkModelA m_vm vmst_maps]. rewrite Visp. unfold sp_window_lo. lia.
        * lia.
        * apply Forall_app. split.
          -- repeat constructor; cbn [snd]; rewrite u_small by lia; lia.
          -- constructor; [cbn [snd]; rewrite u_small by lia; lia|]. eapply Forall_impl; [|exact Vsz]. intros [? ?]; cbn [snd]; lia.
        * rewrite length_app. cbn [length]. lia.
        * unfold vm_live_bytes. rewrite Vmaps. cbn [live_bytes]. rewrite u_small by lia. pose proof Vlim as Vlim'. unfold LIM in Vlim'. lia.   (* [comment removed for export] *)
      + (* [comment removed for export] *)
        intros Hmode err Herr. cbn [mmap_errnos In] in Herr. destruct Herr as [<-|[]]. subst E.
        rewrite v_addi_pc4 by lia. change (2833952 + 4)%Z with 0x2b3e24%Z.
        lazymatch type of HR with regs_ok ?E _ _ =>
          pose proof (regs_set_a0 E _ _ (errno_ret ENOMEM) (ELit (- 12)) HR eq_refl) as HR2 end.
        clear HR. rename HR2 into HR.
        save_know HK. run_block_keep scr0 42%nat. note_pres HKb EQM PRES.
        apply (HOOM Hmode). split; [|split; [|split; [|split]]].
        * regv HR (2 : reg). rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev]. rewrite P0. f_equal; lia.
        * regv HR (3 : reg). reflexivity.
        * regv HR (4 : reg). reflexivity.
        * exact PRES.
        * intros d m Hd Hm.
          lazymatch type of HK with know_ok _ ?E ?Mc ?kn =>
            let i := kidx kn (is_kwr_cov (EVar 0) (-8388608)%Z 1%Z) in
            pose proof (kwr_store_ok RSEGS E Mc kn i (EVar 0) (-8388608)%Z 8388608%Z (-8388608 + d)%Z m HK eq_refl ltac:(lia) ltac:(lia)) as ST end.
          unfold adenot, v_addi in ST. cbn [a_base a_off BA LA MBA edenot ev] in ST. rewrite P0 in ST.
          replace (bv_unsigned sp0 - 8388608 + d)%Z with (bv_unsigned sp0 + (-8388608 + d))%Z by lia. exact ST.
      + (* [comment removed for export] *)
        intros B' HG.
        change (page_round_up_Z 4194324) with 4198400%Z in HG |- *.
        rewrite v_addi_pc4 by lia. change (2833952 + 4)%Z with 0x2b3e24%Z.
        pose proof (grant_ok_unpack _ _ _ _ HG) as (GA & GP & GC & GF & GLv).
        unfold alloc_top in GC. cbv [m_vmmaps HUReadStage.modelG mkModelA m_vm vmst_maps] in GC. rewrite Visp in GC. unfold stack_max_size in GC.
        unfold page_size in GA.
        cbv [m_vmmaps HUReadStage.modelG mkModelA m_vm vmst_maps] in GF, GLv. rewrite Vres, Vmaps, rsegs_reserved in GF.
        assert (GB1 : (0x354000 <= bv_unsigned B')%Z).
        { pose proof (region_free_In _ _ _ (Z_to_bv 64 65536) (Z_to_bv 64 856064) GF
                        ltac:(apply in_or_app; left; cbn [In]; tauto)) as X1.
          pose proof (region_free_In _ _ _ (Z_to_bv 64 921600) (Z_to_bv 64 1966080) GF
                        ltac:(apply in_or_app; left; cbn [In]; tauto)) as X2.
          pose proof (region_free_In _ _ _ (Z_to_bv 64 2887680) (Z_to_bv 64 380928) GF
                        ltac:(apply in_or_app; left; cbn [In]; tauto)) as X3.
          pose proof (region_free_In _ _ _ (Z_to_bv 64 3268608) (Z_to_bv 64 221184) GF
                        ltac:(apply in_or_app; left; cbn [In]; tauto)) as X.
          rewrite !u_small in X1 by lia. rewrite !u_small in X2 by lia. rewrite !u_small in X3 by lia.
          rewrite !u_small in X by lia. lia. }
        assert (GB2 : (bv_unsigned B' + 4198400 <= bv_unsigned B \/ bv_unsigned B + 2101248 <= bv_unsigned B')%Z).
        { pose proof (region_free_In _ _ _ B (Z_to_bv 64 2101248) GF
                        ltac:(apply in_or_app; right; left; reflexivity)) as X.
          rewrite !u_small in X by lia. lia. }
        assert (GB3 : (bv_unsigned B' + 4198400 <= bv_unsigned mb + 4096 \/ bv_unsigned mb + 8192 <= bv_unsigned B')%Z).
        { destruct Vcont as ([cb cs] & Cin & C1 & C2). cbn [fst snd] in C1, C2.
          pose proof (region_free_In _ _ _ cb cs GF ltac:(apply in_or_app; right; right; exact Cin)) as X.
          rewrite !u_small in X by lia. lia. }
        (* [comment removed for export] *)
        lazymatch type of HR with regs_ok _ ?sr ?Rc =>
          pose proof (env_app_regs vals [B'] _ sr Rc ltac:(rewrite HL; vm_compute; reflexivity) HR) as HR2 end.
        lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
          pose proof (env_app_know RSEGS vals [B'] _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2 end.
        clear HR HK. subst E.
        assert (P42 : vals_ev (vals ++ [B']) 42 = B') by (rewrite <- HL; apply vals_ev_last).
        grow_vals HL [B'] 43%nat.
        set (E := Env (vals_ev vals) (gblobs content)) in *.
        assert (AD42 : adenot E (SA (EVar 42) 0) = B').
        { unfold adenot, v_addi. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P42. apply bv_eq. rewrite u_small by lia. lia. }
        pose proof (regs_set_a0 E _ _ B' (EVar 42) HR2 ltac:(cbn [edenot ev]; subst E; exact P42)) as HR. clear HR2.
        assert (KA42 : kentry_ok RSEGS E M1 (KAlign (EVar 42) 4096)).
        { apply kalign_intro; [lia|]. cbn [edenot ev]. subst E. cbn [ev]. rewrite P42. exact GA. }
        assert (KR42 : kentry_ok RSEGS E M1 (KRange (EVar 42) 0x354000 (CEIL - 4198400))).
        { apply krange_intro. cbn [edenot ev]. subst E. cbn [ev]. rewrite P42. unfold CEIL. lia. }
        assert (KD42a : kentry_ok RSEGS E M1 (KDisj (SA (EVar 42) 0) 4198400 (SA (EVar 5) 0) 2101248)).
        { cbn [kentry_ok]. unfold estart. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P42, P5. lia. }
        assert (KD42b : kentry_ok RSEGS E M1 (KDisj (SA (EVar 42) 0) 4198400 (SA (EVar 2) 4096) 4096)).
        { cbn [kentry_ok]. unfold estart. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P42, P2. lia. }
        assert (KD42s : kentry_ok RSEGS E M1 (KDisj (SA (EVar 0) (-8388608)) HUGE (SA (EVar 42) 0) 4198400)).
        { cbn [kentry_ok]. unfold estart, HUGE. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P42, P0. lia. }
        pose proof (know_ok_cons _ _ _ _ _ KA42 (know_ok_cons _ _ _ _ _ KR42
                     (know_ok_cons _ _ _ _ _ KD42s (know_ok_cons _ _ _ _ _ KD42a (know_ok_cons _ _ _ _ _ KD42b HK2))))) as HK2'.
        clear KA42 KR42 KD42a KD42b KD42s HK2.
        lazymatch type of HK2' with know_ok _ _ ?Mc ?kn =>
          pose proof (know_ok_zfill RSEGS E Mc kn (EVar 42) 0 4198400 HK2'
                        ltac:(apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P42; lia) ltac:(lia) ltac:(lia)) as HK3 end.
        rewrite AD42 in HK3. clear HK2'.
        assert (KW42 : kentry_ok RSEGS E (zfill B' (Z_to_bv 64 4198400) M1) (KWr (SA (EVar 42) 0) 4198400)).
        { cbn [kentry_ok]. split; [apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P42; lia|].
          intros d m Hd Hm. unfold estart. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P42.
          unfold zfill. apply store_ok_zmem; rewrite ?u_small by lia; lia. }
        pose proof (know_ok_cons _ _ _ _ _ KW42 HK3) as HK. clear KW42 HK3.
        norm_know HK.
        assert (PRES2 : pres M0 (zfill B' (Z_to_bv 64 4198400) M1) sp0).
        { eapply pres_trans; [exact PRES|]. eapply (pres_far _ _ sp0 (bv_unsigned B') 4198400); [lia | lia | lia |].
          intros x Hx. apply zfill_outside. rewrite u_small by lia. exact Hx. }
        clear PRES. rename PRES2 into PRES.
        (* [comment removed for export] *)
        save_know HK. gg_block_keep scrT 43%nat.
        { apply xor_m1_ne0. cbn [edenot ev]. subst E. cbn [ev]. rewrite P42. lia. }
        note_pres HKb EQM PRES.
        (* [comment removed for export] *)
        assert (Hflat2 : forall k n, (0 <= k)%Z -> (0 <= n)%Z -> (k + n <= 8192)%Z -> flat E (SA (EVar 2) k) n).
        { intros k n Hk Hn Hkn. apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P2; lia. }
        krdv HK 2%nat 4136%Z 8%nat RM0. { apply Hflat2; lia. }
        krdv HK 2%nat 4152%Z 8%nat RW0. { apply Hflat2; lia. }
        unfold adenot, v_addi in RM0, RW0. cbn [a_base a_off BA LA MBA edenot ev] in RM0, RW0. subst E. cbn [ev] in RM0, RW0.
        rewrite P2 in RM0, RW0. rewrite P42 in RM0.
        set (E := Env (vals_ev vals) (gblobs content)) in *.
        kzero_at HK (EVar 42) 12%Z Z12. kzero_at HK (EVar 42) 13%Z Z13.
        cbn [edenot ev] in Z12, Z13. subst E. cbn [ev] in Z12, Z13. rewrite P42 in Z12, Z13.
        set (E := Env (vals_ev vals) (gblobs content)) in *.
        lazymatch goal with |- GG _ _ _ _ (mkCfg (mkst ?Rc _ ?Mc _) _) =>
        assert (EF : efH Mc (Z_to_bv 64 7) (bv_unsigned mb + 4120) (bv_unsigned B') 4202464 0 4194304 0 0 4198384 (bv_unsigned B' + 16) 7) end.
        { constructor.
          - vm_compute. reflexivity.
          - unfold slot_start, UNIT. lia.
          - vm_compute. reflexivity.
          - lia.
          - lia.
          - lia.
          - lia.
          - lia.
          - intros HH. exfalso. destruct HH as [HH|HH]; revert HH; vm_compute; congruence.
          - lia.
          - lia.
          - lia.
          - lia.
          - lia.
          - lia.
          - replace (bv_unsigned mb + 4120 + 16)%Z with (bv_unsigned mb + 4136)%Z by lia. rewrite RM0. f_equal. f_equal. apply bv_eq. rewrite u_small by lia. reflexivity.
          - replace (bv_unsigned mb + 4120 + 32)%Z with (bv_unsigned mb + 4152)%Z by lia. exact RW0.
          - replace (bv_unsigned B' + 16 - 4)%Z with (bv_unsigned B' + 12)%Z by lia. exact Z12.
          - replace (bv_unsigned B' + 16 - 3)%Z with (bv_unsigned B' + 13)%Z by lia. exact Z13.
          - intros HH. exfalso. apply HH. reflexivity.
          - replace (Z_to_bv 64 (bv_unsigned B' + 16 - 3)) with (adenot E (SA (EVar 42) 13))
              by (unfold adenot, v_addi; cbn [a_base a_off BA LA MBA edenot ev]; subst E; cbn [ev]; rewrite P42; f_equal; lia).
            kwr_solve HK.
          - intros jj Hj. unfold SCT.
            lazymatch type of HK with know_ok _ _ _ ?kn =>
              eapply (kimg_none RSEGS E _ kn ltac:(let i := kidx kn (is_kimg_cov 0x72234 96) in exact i) _ _ HK eq_refl) end. lia. }
        assert (RT : Hoare.ret_ok (Z_to_bv 64 0xe1a3c)) by (apply bv_eq; vm_compute; reflexivity).
        lazymatch goal with |- GG _ _ _ _ (mkCfg (mkst ?Rc _ ?Mc _) _) =>
          assert (G1 : getr Rc 1 = Z_to_bv 64 0xe1a3c) by (regv HR (1:reg); reflexivity);
          assert (G10 : getr Rc 10 = Z_to_bv 64 (bv_unsigned mb + 4120))
            by (regv HR (10:reg); rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off BA LA MBA edenot ev]; subst E; cbn [ev]; rewrite P2; reflexivity);
          assert (G11 : getr Rc 11 = Z_to_bv 64 0) by (regv HR (11:reg); reflexivity);
          assert (G12 : getr Rc 12 = Z_to_bv 64 4194304) by (regv HR (12:reg); reflexivity);
          assert (G13 : getr Rc 13 = Z_to_bv 64 7) by (regv HR (13:reg); reflexivity);
          destruct (ref_enframe Rc Mc (seg_rom RSEGS) (Z_to_bv 64 0xe1a3c) (Z_to_bv 64 7) _ _ _ _ _ _ _ _ _ _ EF G1 RT G10 G11 G12 G13)
            as (R3 & M3 & RUN & KEEP & A0 & FR & POST);
          clear RT G1 G10 G11 G12 G13 EF RM0 RW0 Z12 Z13 end.
        replace (Z_to_bv 64 2830836) with (0x2b31f4 : word) by (apply bv_eq; vm_compute; reflexivity).
        eapply gg_msteps; [reflexivity | reflexivity | exact RUN |]. clear RUN.
        lazymatch type of HR with regs_ok _ ?sr _ =>
          pose proof (regs_after_keeps vals _ sr _ R3 callee_saved ltac:(rewrite HL; vm_compute; reflexivity) HR KEEP callee_saved_no0) as HR3 end.
        rewrite HL in HR3. clear HR KEEP.
        lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
          pose proof (env_app_know RSEGS vals (junk_vals R3) _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2 end.
        clear HK Hflat2 AD42. subst E.
        grow_vals HL (junk_vals R3) 75%nat.
        set (E := Env (vals_ev vals) (gblobs content)) in *.
        lazymatch type of HR3 with regs_ok _ ?sr _ =>
          assert (HR : regs_ok E (sr_upd sr (ridx 10) (EAlu ALU_ADD (EVar 42) (ELit 128))) R3) end.
        { apply regs_ok_pin; [exact HR3|]. rewrite A0, edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off BA LA MBA edenot ev].
          subst E. cbn [ev]. rewrite P42. f_equal. lia. }
        clear HR3 A0. norm_regs HR.
        destruct FR as [FRo FRg].
        assert (OUT3 : forall x : word, (bv_unsigned x < estart E (SA (EVar 42) 13) \/ estart E (SA (EVar 42) 13) + 4198383 <= bv_unsigned x)%Z -> M3 x = M2 x).
        { intros x Hx. apply FRo. cbn [outside]. split; [|exact I]. unfold in_rng. rewrite u_small by lia.
          unfold estart in Hx. cbn [a_base a_off BA LA MBA edenot ev] in Hx. subst E. cbn [ev] in Hx. rewrite P42 in Hx. lia. }
        lazymatch type of HK2 with know_ok _ _ _ ?kn =>
          pose proof (know_ok_frame RSEGS E M2 M3 kn (EVar 42) 13 4198383 HK2
                        ltac:(apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P42; lia) OUT3 FRg) as HK4 end.
        clear HK2 OUT3.
        destruct POST as [Pp Pe Pr Pq Pm4 Pm3 Pm2 Pzr Pe5 Pe4 Ps3 Ps2 Prr]. cbn zeta in *. subst Pp Pe Pr Pq.
        specialize (Pzr ltac:(lia)). specialize (Pe5 ltac:(lia)). specialize (Pe4 ltac:(lia)).
        specialize (Ps3 ltac:(lia)). specialize (Ps2 ltac:(lia)).
        replace (0 + 32 * res_code (4198384 - 4 - 4194304 - 16 * 7))%Z with 160%Z in Pm3 by (vm_compute; reflexivity).
        replace (4198384 * 0 / 16 + 7)%Z with 7%Z in Pm2 by (vm_compute; reflexivity).
        replace (4198384 - 4 - 4194304 - 16 * 7)%Z with 3964%Z in Pe4 by reflexivity.
        assert (EV42 : edenot E (EVar 42) = B') by (cbn [edenot ev]; subst E; cbn [ev]; exact P42).
        assert (K1 : kentry_ok RSEGS E M3 (KWord (SA (EVar 42) 124) 1 (ELit 0))) by (hdr_byte EV42 Pm4 124%Z).
        assert (K2 : kentry_ok RSEGS E M3 (KWord (SA (EVar 42) 125) 1 (ELit 160))) by (hdr_byte EV42 Pm3 125%Z).
        assert (K3 : kentry_ok RSEGS E M3 (KWord (SA (EVar 42) 126) 2 (ELit 7))) by (hdr_word EV42 Pm2 126%Z 2%nat 7%Z).
        assert (K4 : kentry_ok RSEGS E M3 (KWord (SA (EVar 42) 4194432) 1 (ELit 0))) by (hdr_byte EV42 Pzr 4194432%Z).
        assert (K5 : kentry_ok RSEGS E M3 (KWord (SA (EVar 42) 4198391) 1 (ELit 0))) by (hdr_byte EV42 Pe5 4198391%Z).
        assert (K6 : kentry_ok RSEGS E M3 (KWord (SA (EVar 42) 4198392) 4 (ELit 3964))) by (hdr_word EV42 Pe4 4198392%Z 4%nat 3964%Z).
        assert (K7 : kentry_ok RSEGS E M3 (KWord (SA (EVar 42) 13) 1 (ELit 224))) by (hdr_byte EV42 Ps3 13%Z).
        assert (K8 : kentry_ok RSEGS E M3 (KWord (SA (EVar 42) 14) 2 (ELit 7))) by (hdr_word EV42 Ps2 14%Z 2%nat 7%Z).
        pose proof (know_ok_cons _ _ _ _ _ K1 (know_ok_cons _ _ _ _ _ K2 (know_ok_cons _ _ _ _ _ K3 (know_ok_cons _ _ _ _ _ K4
          (know_ok_cons _ _ _ _ _ K5 (know_ok_cons _ _ _ _ _ K6 (know_ok_cons _ _ _ _ _ K7 (know_ok_cons _ _ _ _ _ K8 HK4)))))))) as HK.
        clear K1 K2 K3 K4 K5 K6 K7 K8 HK4 Pm4 Pm3 Pm2 Pzr Pe5 Pe4 Ps3 Ps2 Prr.
        norm_know HK.
        assert (PRES2 : pres M0 M3 sp0).
        { eapply pres_trans; [exact PRES|]. eapply (pres_far _ _ sp0 (bv_unsigned B' + 13) 4198383); [lia | lia | lia |].
          intros x Hx. apply FRo. cbn [outside]. split; [|exact I]. unfold in_rng. rewrite u_small by lia. lia. }
        clear PRES FRo FRg. rename PRES2 into PRES.
        (* [comment removed for export] *)
        save_know HK. gg_block_keep scr0 75%nat. note_pres HKb EQM PRES.
        (* [comment removed for export] *)
        assert (Hflat5 : forall k n, (0 <= k)%Z -> (0 <= n)%Z -> (k + n <= 2101248)%Z -> flat E (SA (EVar 5) k) n).
        { intros k n Hk Hn Hkn. apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P5; lia. }
        lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
          pose proof (kblob_rdn RSEGS E Mc kn (EVar 5) 112 (ELit 1048576) 8%nat HK ltac:(vm_compute; reflexivity)) as SRC1;
          pose proof (kblob_rdn RSEGS E Mc kn (EVar 5) 1048688 (ELit 1048576) 9%nat HK ltac:(vm_compute; reflexivity)) as SRC2 end.
        change (eb E 8%nat) with (gblobs content 8%nat) in SRC1. rewrite (gblobs_hb 5) in SRC1 by lia. change (held_of 5) with 1048576%Z in SRC1.
        change (eb E 9%nat) with (gblobs content 9%nat) in SRC2. rewrite EBc in SRC2.
        assert (RLh : length (pref 1048576 content) = Z.to_nat 1048576) by (pose proof (pref_length 1048576 content ltac:(lia)); lia).
        assert (SRC : rdn RSEGS M4 (adenot E (SA (EVar 5) 112)) (length (pref 2097152 content)) = Some (pref 2097152 content)).
        { replace (pref 2097152 content) with (pref 1048576 content ++ pref 1048576 (dropz 1048576 content))
            by (rewrite pref_app by lia; reflexivity).
          rewrite length_app, RLh, RL1. apply SeqExec.rdn_app.
          - rewrite RLh in SRC1. exact SRC1.
          - rewrite RL1 in SRC2. replace (adenot E (SA (EVar 5) 112) + nat_to_word (Z.to_nat 1048576)) with (adenot E (SA (EVar 5) 1048688)); [exact SRC2|].
            unfold adenot, v_addi, nat_to_word. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P5. apply bv_eq.
            rewrite bv_add_unsigned. rewrite Z2Nat.id by lia. rewrite !u_small by lia. rewrite bv_wrap_small; [lia|]. unfold bv_modulus. lia. }
        clear SRC1 SRC2.
        assert (RLc : length (pref 2097152 content) = Z.to_nat 2097152) by (pose proof (pref_length 2097152 content ltac:(lia)); lia).
        assert (EBf : gblobs content 10%nat = pref 2097152 content) by (rewrite <- (gblobs_fb 5) by lia; reflexivity).
        set (dst := adenot E (SA (EVar 42) 128)). set (src := adenot E (SA (EVar 5) 112)) in SRC.
        assert (Hudst : bv_unsigned dst = (bv_unsigned B' + 128)%Z).
        { subst dst. unfold adenot, v_addi. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P42, u_small by lia. lia. }
        assert (Husrc : bv_unsigned src = (bv_unsigned B + 112)%Z).
        { subst src. unfold adenot, v_addi. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P5, u_small by lia. lia. }
        lazymatch goal with |- GG _ _ _ _ (mkCfg (mkst ?Rc _ ?Mc _) _) =>
          assert (MC : mcH Mc dst src 2097152 (pref 2097152 content)) end.
        { constructor.
          - lia.
          - exact RLc.
          - exact SRC.
          - subst dst. rewrite RLc. kwr_solve HK.
          - lia.
          - lia.
          - lia. }
        assert (RT : Hoare.ret_ok (Z_to_bv 64 0xe1a5c)) by (apply bv_eq; vm_compute; reflexivity).
        lazymatch goal with |- GG _ _ _ _ (mkCfg (mkst ?Rc _ ?Mc _) _) =>
          assert (G1 : getr Rc 1 = Z_to_bv 64 0xe1a5c) by (regv HR (1:reg); reflexivity);
          assert (G10 : getr Rc 10 = dst) by (regv HR (10:reg); subst dst; apply edenot_add_lit);
          assert (G11 : getr Rc 11 = src) by (regv HR (11:reg); subst src; unfold bx; apply edenot_add_lit);
          assert (G12 : getr Rc 12 = Z_to_bv 64 2097152) by (regv HR (12:reg); reflexivity);
          destruct (ref_memcpy Mc dst src 2097152 _ (seg_rom RSEGS) MC Rc (Z_to_bv 64 0xe1a5c) RT G1 G10 G11 G12) as (R5 & RUN & KEEP);
          clear RT G1 G10 G11 G12 MC SRC end.
        replace (Z_to_bv 64 2867236) with (0x2bc024 : word) by (apply bv_eq; vm_compute; reflexivity).
        eapply gg_msteps; [reflexivity | reflexivity | exact RUN |]. clear RUN.
        lazymatch type of HR with regs_ok _ ?sr _ =>
          pose proof (regs_after_keeps vals _ sr _ R5 callee_kept ltac:(rewrite HL; vm_compute; reflexivity) HR KEEP callee_kept_no0) as HR5 end.
        rewrite HL in HR5. clear HR KEEP.
        lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
          pose proof (know_ok_wblob RSEGS E Mc kn (EVar 42) 128 10%nat (pref 2097152 content) HK
                        ltac:(apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P42, ?RLc; lia)
                        EBf ltac:(rewrite RLc; lia) ltac:(rewrite RLc; lia)) as HK2 end.
        fold dst in HK2. rewrite RLc, Z2Nat.id in HK2 by lia.
        assert (Hdst : dst = Z_to_bv 64 (bv_unsigned B' + 128)) by (apply bv_eq; rewrite Hudst, u_small by lia; reflexivity).
        rewrite Hdst in HK2 |- *.
        assert (PRES2 : pres M0 (wbytes M4 (Z_to_bv 64 (bv_unsigned B' + 128)) (pref 2097152 content)) sp0).
        { eapply pres_trans; [exact PRES|]. eapply (pres_far _ _ sp0 (bv_unsigned B' + 128) 2097152); [lia | lia | lia |].
          intros x Hx. apply MemSplit.wbytes_outside; rewrite u_small, RLc by lia; lia. }
        clear PRES HK. rename PRES2 into PRES.
        lazymatch type of HK2 with know_ok _ _ ?Mc ?kn =>
          pose proof (env_app_know RSEGS vals (junk_vals R5) _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK end.
        clear HK2. subst src E. clear dst Hdst Hudst Husrc EV42 Hflat5.
        grow_vals HL (junk_vals R5) 107%nat.
        set (E := Env (vals_ev vals) (gblobs content)) in *. rename HR5 into HR.
        norm_regs HR. norm_know HK.
        (* [comment removed for export] *)
        save_know HK. gg_block_keep scr0 107%nat. note_pres HKb EQM PRES.
        (* [comment removed for export] *)
        assert (Hflat5 : forall k n, (0 <= k)%Z -> (0 <= n)%Z -> (k + n <= 2101248)%Z -> flat E (SA (EVar 5) k) n).
        { intros k n Hk Hn Hkn. apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P5; lia. }
        assert (Hflat2 : forall k n, (0 <= k)%Z -> (0 <= n)%Z -> (k + n <= 8192)%Z -> flat E (SA (EVar 2) k) n).
        { intros k n Hk Hn Hkn. apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P2; lia. }
        krdv HK 5%nat 108%Z 1%nat Gb4. { apply Hflat5; lia. }
        krdv HK 5%nat 109%Z 1%nat Gb3. { apply Hflat5; lia. }
        krdv HK 5%nat 110%Z 2%nat Goff. { apply Hflat5; lia. }
        krdv HK 5%nat 0%Z 8%nat Gmeta. { apply Hflat5; lia. }
        krdv HK 2%nat 4176%Z 8%nat Gmem. { apply Hflat2; lia. }
        krdv HK 2%nat 4192%Z 8%nat GW. { apply Hflat2; lia. }
        krdv HK 2%nat 4184%Z 4%nat Gav. { apply Hflat2; lia. }
        krdv HK 2%nat 4188%Z 4%nat Gfr. { apply Hflat2; lia. }
        krdv HK 2%nat 4096%Z 8%nat Garea. { apply Hflat2; lia. }
        krd HK 0x351df0%Z 8%nat Gsec.
        unfold adenot, v_addi in Gb4, Gb3, Goff, Gmeta, Gmem, GW, Gav, Gfr, Garea.
        cbn [a_base a_off BA LA MBA edenot ev] in Gb4, Gb3, Goff, Gmeta, Gmem, GW, Gav, Gfr, Garea. subst E.
        cbn [ev] in Gb4, Gb3, Goff, Gmeta, Gmem, GW, Gav, Gfr, Garea.
        rewrite P5 in Gb4, Gb3, Goff, Gmeta, Gmem. rewrite P2 in Gmeta, Gmem, GW, Gav, Gfr, Garea.
        cbn [ev] in Gsec. rewrite ?P8 in Garea. rewrite ?P8 in Gsec.
        unfold mbx in Gmeta. rewrite alu_add in Gmeta. unfold v_add in Gmeta.
        set (E := Env (vals_ev vals) (gblobs content)) in *.
        lazymatch goal with |- GG _ _ _ _ (mkCfg (mkst ?Rc _ ?Mc _) _) =>
          assert (GMR : gm_reads Mc (bv_unsigned B + 112) (bv_unsigned B) (bv_unsigned mb + 4160) 0 5 6 2105312 0 0 sec) end.
        { constructor.
          - apply rdn1_mem_high; [rewrite u_small by lia; lia|]. replace (bv_unsigned B + 112 - 4)%Z with (bv_unsigned B + 108)%Z by lia. exact Gb4.
          - apply rdn1_mem_high; [rewrite u_small by lia; lia|]. replace (bv_unsigned B + 112 - 3)%Z with (bv_unsigned B + 109)%Z by lia. exact Gb3.
          - replace (bv_unsigned B + 112 - 2)%Z with (bv_unsigned B + 110)%Z by lia. exact Goff.
          - rewrite Z.add_0_r in Gmeta. change (bv_unsigned (Z_to_bv 64 4160)) with 4160%Z in Gmeta. exact Gmeta.
          - replace (bv_unsigned mb + 4160 + 16)%Z with (bv_unsigned mb + 4176)%Z by lia. rewrite Gmem. f_equal. f_equal. symmetry. apply Z_to_bv_bv_unsigned.
          - replace (bv_unsigned mb + 4160 + 32)%Z with (bv_unsigned mb + 4192)%Z by lia. exact GW.
          - replace (bv_unsigned mb + 4160 + 24)%Z with (bv_unsigned mb + 4184)%Z by lia. exact Gav.
          - replace (bv_unsigned mb + 4160 + 28)%Z with (bv_unsigned mb + 4188)%Z by lia. exact Gfr.
          - assert (HM24 : ((bv_unsigned mb + 4160) mod 4096 = 64)%Z)
              by (rewrite <- Zplus_mod_idemp_l, Hmba; reflexivity).
            rewrite HM24. replace (bv_unsigned mb + 4160 - 64)%Z with (bv_unsigned mb + 4096)%Z by lia. exact Garea.
          - exact Gsec.
          - intros i Hi. lazymatch type of HK with know_ok _ _ _ ?kn =>
              eapply (kimg_none RSEGS E _ kn ltac:(let jj := kidx kn (is_kimg_cov 0x72234 96) in exact jj) _ _ HK eq_refl) end. lia. }
        assert (GMP : gm_pure (bv_unsigned B + 112) (bv_unsigned B) (bv_unsigned mb + 4160) 0 5 6 2105312 0 0).
        { constructor.
          all: try (change (w_lastidx 2105312) with 0%Z); try (change (w_sizeclass 2105312) with 63%Z);
               try (change (w_maplen 2105312) with 513%Z).
          1: { rewrite <- Zplus_mod_idemp_l.
               replace (bv_unsigned B mod 16)%Z with 0%Z; [reflexivity|].
               symmetry. apply Znumtheory.Zdivide_mod. apply (Z.divide_trans _ 4096); [exists 256%Z; reflexivity|].
               apply Znumtheory.Zmod_divide; [lia | exact KBal]. }
          all: try lia.
          all: reflexivity. }
        clear Gb4 Gb3 Goff Gmeta Gmem GW Gav Gfr Garea Gsec Hflat2 Hflat5.
        assert (RT : Hoare.ret_ok (Z_to_bv 64 0x2b1c78)) by (apply bv_eq; vm_compute; reflexivity).
        lazymatch goal with |- GG _ _ _ _ (mkCfg (mkst ?Rc _ ?Mc _) _) =>
          assert (G10 : getr Rc 10 = Z_to_bv 64 (bv_unsigned B + 112))
            by (regv HR (10:reg); unfold bx; rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off BA LA MBA edenot ev]; subst E; cbn [ev]; rewrite P5; reflexivity);
          assert (G1 : getr Rc 1 = Z_to_bv 64 0x2b1c78) by (regv HR (1:reg); reflexivity);
          destruct (get_meta_run Rc Mc (seg_rom RSEGS) (Z_to_bv 64 0x2b1c78) _ _ _ _ _ _ _ _ _ _ GMR GMP G10 G1 RT) as (R7 & RUN & A0 & A1 & KEEP);
          clear RT G1 G10 GMR GMP end.
        replace (Z_to_bv 64 2825760) with (0x2b1e20 : word) by (apply bv_eq; vm_compute; reflexivity).
        eapply gg_msteps; [reflexivity | reflexivity | exact RUN |]. clear RUN.
        lazymatch type of HR with regs_ok _ ?sr _ =>
          pose proof (regs_after_keeps vals _ sr _ R7 gm_kept ltac:(rewrite HL; vm_compute; reflexivity) HR (gm_keeps_kept _ _ KEEP) gm_kept_no0) as HR7 end.
        rewrite HL in HR7. clear HR KEEP.
        lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
          pose proof (env_app_know RSEGS vals (junk_vals R7) _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2 end.
        clear HK. subst E.
        grow_vals HL (junk_vals R7) 139%nat.
        set (E := Env (vals_ev vals) (gblobs content)) in *. rename HK2 into HK.
        lazymatch type of HR7 with regs_ok _ ?sr _ =>
          assert (HR : regs_ok E (sr_upd (sr_upd sr (ridx 10) (mbx 4160)) (ridx 11) (ELit 6)) R7) end.
        { apply regs_ok_pin; [apply regs_ok_pin; [exact HR7|]|].
          - rewrite A0. unfold mbx. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P2. reflexivity.
          - rewrite A1. reflexivity. }
        clear HR7 A0 A1. norm_regs HR. norm_know HK.
        (* [comment removed for export] *)
        save_know HK. gg_block_keep scr0 139%nat. note_pres HKb EQM PRES.
        (* [comment removed for export] *)
        lazymatch goal with |- GG _ _ _ _ (mkCfg (mkst ?Rc _ ?Mc _) ?MD) =>
          eapply (gg_munmap RSEGS mode Q Rc (Z_to_bv 64 0x2b3f8c) Mc MD ECALLW B 2101248 K fetch_26e3a0 is_ecall_ECALLW eq_refl eq_refl) end.
        * regv HR (17:reg). reflexivity.
        * regv HR (10:reg). cbn [edenot ev]. subst E. cbn [ev]. exact P5.
        * unfold page_size. exact KBal.
        * regv HR (11:reg). reflexivity.
        * lia.
        * change (page_round_up_Z 2101248) with 2101248%Z. unfold TASK_SIZE. lia.
        * change (page_round_up_Z 2101248) with 2101248%Z. cbv [m_vmmaps mmap_model with_vmmaps HUReadStage.modelG mkModelA m_vm vmst_maps]. cbn [vm_maps]. rewrite Vmaps. apply map_has_cons. apply map_has_head.
        * change (page_round_up_Z 2101248) with 2101248%Z.
          rewrite v_addi_pc4 by lia. change (0x2b3f8c + 4)%Z with 0x2b3f90%Z.
          lazymatch type of HR with regs_ok ?E _ _ =>
            pose proof (regs_set_a0 E _ _ (Z_to_bv 64 0) (ELit 0) HR eq_refl) as HR2 end.
          clear HR. rename HR2 into HR.
          assert (AD5 : adenot E (SA (EVar 5) 0) = B).
          { unfold adenot, v_addi. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P5. apply bv_eq. rewrite u_small by lia. lia. }
          lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
            pose proof (know_ok_unfill RSEGS E Mc kn (EVar 5) 0 2101248 HK
                          ltac:(apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P5; lia) ltac:(lia)) as HK2 end.
          rewrite AD5 in HK2. clear HK AD5. rename HK2 into HK. norm_know HK.
          lazymatch goal with |- GG _ _ _ _ (mkCfg (mkst _ _ ?Mc _) _) =>
            assert (PRES2 : pres M0 Mc sp0) end.
          { eapply pres_trans; [exact PRES|]. eapply (pres_far _ _ sp0 (bv_unsigned B) 2101248); [lia | lia | lia |].
            intros x Hx. apply unfill_outside. rewrite u_small by lia. exact Hx. }
          clear PRES. rename PRES2 into PRES.
          (* [comment removed for export] *)
          save_know HK. gg_block_keep scr0 139%nat. note_pres HKb EQM PRES.
          (* [comment removed for export] *)
          rewrite munmap_model_simple by reflexivity.
          unfold mmap_model, with_vmmaps.
          cbv [m_vmmaps m_fd m_io m_fsys m_proc m_lim m_time m_vm m_vm_lazy m_vm_materialized vmst_maps vmst_lazy vmst_materialized
               HUReadStage.modelG mkModelA]. cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk vm_limit vm_mmap_base vm_init_sp].
          lazymatch goal with |- GG _ _ _ _ (mkCfg (mkst ?Rc _ ?Mc _) (mkModelOf _ (mkVmState ?V' _ _) _ _ _ _ _)) =>
            change (GG RSEGS mode Q K (mkCfg (mkst Rc (Z_to_bv 64 0xe1a68) Mc (seg_rom RSEGS)) (modelG (held_of 6) V'))) end.
          unfold half_branch in HK1. apply (HK1 _ _ _ B' (edenot E (EExt true 0 4 (EVar 6)))).
          lazymatch type of HR with regs_ok _ ?srf _ =>
          lazymatch type of HK with know_ok _ _ ?Mf ?knf =>
            set (rvl := [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 42; EExt true 0 4 (EVar 6); EVar 7; EVar 8; ELit 0] ++ srf);
            assert (XB : forall k, gblobs content k = eb E ((fun k : nat => k) k)) by (intros; reflexivity);
            split; [ exists (map (edenot E) srf); split; [rewrite length_map; reflexivity|];
                     replace (ENV_RD sp0 p1 mb bw gm L B' (edenot E (EExt true 0 4 (EVar 6))) can sec (map (edenot E) srf) content)
                        with (xenv E rvl (gblobs content));
                     [ split; [ apply (regs_ok_xfer E rvl (fun k => k) _ XB srf (sr_HALF 6) _ HR); [reflexivity | reflexivity |]
                              | apply (know_ok_xfer_entails RSEGS E rvl (fun k => k) _ Mf knf (kn_HALF 6) XB HK) ]
                     | ]
                   | split; [exact PRES |] ]
          end end.
          -- intros i Hi Hne. exfalso. apply Hne. vm_compute in Hi. cbv [In] in Hi. destruct Hi as [<-|[]]. reflexivity.
          -- match goal with |- Forall _ ?l => replace l with (@nil kentry) by (vm_compute; reflexivity) end. constructor.
          -- unfold ENV_RD, xenv, vals_RD. f_equal. subst rvl. rewrite map_app. cbn [map app].
             cbn [edenot ev]. subst E. cbn [ev]. rewrite P0, P1, P2, P3, P4, P42, P7, P8. reflexivity.
          -- (* [comment removed for export] *)
             unfold vm_stage. cbn [vm_reserved vm_limit vm_maps vm_init_sp]. split; [exact Vres|]. split; [exact Vlim|]. split; [exact Visp|].
             rewrite Vmaps.
             assert (Hbb : B' <> B) by (intros HH; rewrite HH in GB2; lia).
             exists (map_remove rest B). split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
             ++ change (nb_of 6) with 4198400%Z. rewrite map_remove_skip by exact Hbb. rewrite map_remove_head. reflexivity.
             ++ apply incl_Forall with (l1 := rest); [|exact Vsz]. unfold map_remove. apply incl_filter.
             ++ pose proof (map_remove_length rest B). lia.
             ++ pose proof (live_bytes_map_remove_le rest B). lia.
             ++ destruct Vcont as (pc & Cin & C1 & C2). exists pc. split; [|split; assumption].
                unfold map_remove. apply filter_In. split; [exact Cin|]. destruct pc as [cb cs]. cbn [fst snd] in C1, C2 |- *.
                apply Bool.negb_true_iff. unfold bv_eqb. apply Z.eqb_neq. intros HH.
                pose proof (proj1 (Forall_forall _ _) Vdisj _ Cin) as X. cbn [fst snd] in X.
                pose proof (proj1 (Forall_forall _ _) Vsz _ Cin) as Y. cbn [snd] in Y. lia.
             ++ apply Forall_forall. intros [qb qs] Hq. cbn [fst snd]. change (nb_of 6) with 4198400%Z.
                unfold map_remove in Hq. apply filter_In in Hq as [Hq _].
                pose proof (region_free_In _ _ _ qb qs GF ltac:(apply in_or_app; right; right; exact Hq)) as X.
                rewrite u_small in X by lia. lia.
             ++ unfold map_remove. apply seps_filter. exact Vseps.
             ++ split. { (* [comment removed for export] *)
                apply (HUTargetPre.vm_ledger_frame mb bw V); [exact Vlg | |].
                ** intros Hin. rewrite Vmaps in Hin. destruct Hin as [EE | Hin].
                   { exfalso. apply (f_equal snd) in EE. cbn [snd] in EE. apply (f_equal bv_unsigned) in EE. rewrite !u_small in EE by lia. lia. }
                   apply HUTargetPre.In_map_remove_keep; [right; right; exact Hin | cbn [fst]].
                   intros HH. pose proof (proj1 (Forall_forall _ _) Vdisj _ Hin) as X. cbn [fst snd] in X. rewrite HH, u_small in X by lia. lia.
                ** intros Hin Hcov. rewrite Vmaps in Hin. destruct Hin as [EE | Hin].
                   { exfalso. apply (f_equal snd) in EE. cbn [snd] in EE. apply (f_equal bv_unsigned) in EE. rewrite !u_small in EE by lia. lia. }
                   pose proof (proj1 (Forall_forall _ _) Vdisj _ Hin) as X. cbn [fst snd] in X. rewrite u_small in X by lia.
                   rewrite u_small by lia. apply HUTargetPre.maps_subtract_keep_cover; [lia | lia | lia | exact Hcov | lia]. }
                (* [comment removed for export] *)
                apply (vm_exact_grow V _ sp0 mb bw B B' _ _ Vex);
                  [vm_compute; split; reflexivity | vm_compute; split; reflexivity | cbn [vm_maps]; rewrite Vmaps; reflexivity | reflexivity
                  | reflexivity | reflexivity | exact GA | exact GP | match goal with |- (_ + ?n <= _)%Z => let n' := eval vm_compute in n in change n with n' end; lia
                  | rewrite rsegs_reserved, Vmaps; exact GF].
  Qed.
End G.
End H0ReadG5.

(* [comment removed for export] *)
Module H0ReadG6.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.PropExec OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.CatExec OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.CatSim OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.SeqExec OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.StoreOk OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.ShapeAlg OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.Nodes OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.MmapSim OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.AllocSim OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.FileSim OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.AgentLib OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.MemSplit OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.Frame OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.StreamSim OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.SymExec OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.SymExec2 OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.SymExec2Sound OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.SymRun OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.SymDrive OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.SymDriveX OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.RefMemcpyLib HUMemcpyBase HUMemcpy OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.MallocDefs HUEnframeBase HUEnframe HUGetMeta OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.RefNodes OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.LibKnowFrame OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.LibKnowXfer OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.RefReadLib HUReadBase HUReadStage HUReadChunk HUReadG0 HUTargetPre OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.ExistsRun OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.PhaseG HUReadChunk.H0ReadChunkW.
Import ConeCfg.
(* [comment removed for export] *)
(* [comment removed for export] *)

Import ListNotations.
Import ConeCfg.
Open Scope bv_scope.
Import SX2. Import SX2S.
Import ConeCfg.

#[local] Abbreviation RSEGS := Ubsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Tactic Notation "run_block" constr(scr) constr(NX) := run_block_gen RFUEL RSTOPS scr NX false.
#[local] Tactic Notation "run_block_keep" constr(scr) constr(NX) := run_block_gen RFUEL RSTOPS scr NX true.
#[local] Tactic Notation "gg_block" constr(scr) constr(NX) := gg_block_gen RFUEL RSTOPS scr NX false.
#[local] Tactic Notation "gg_block_keep" constr(scr) constr(NX) := gg_block_gen RFUEL RSTOPS scr NX true.

Section G.
  Variables (sp0 p1 mb bw gm can sec : word) (path content : list byte).
  Variables (stdin0 : AmbIn) (fs0 : Fs) (tid : word).
  Hypothesis Hfile : fs_lookup fs0 path = Some content.

  Let L : Z := Z.of_nat (length content).
  #[local] Notation modelG := (HUReadStage.modelG path stdin0 fs0 tid) (only parsing).
  #[local] Notation oom_branch := (HUReadStage.oom_branch sp0 path stdin0 fs0 tid) (only parsing).

  (* [comment removed for export] *)
  Definition half_branch (mode : bool) (Q : config -> Prop) (j' : Z) (M0 : word -> option byte) (K : TSet) : Prop :=
    forall R M V B e, half j' sp0 p1 mb bw gm L B e can sec content M0 R M V ->
      GG RSEGS mode Q K (mkCfg (mkst R (Z_to_bv 64 0xe1a68) M (seg_rom RSEGS)) (modelG (held_of j') V)).

  Ltac note_pres HKold EQM PRES :=
    lazymatch type of EQM with ?Mn = mem_denot ?E ?Mo ?log =>
      lazymatch type of PRES with pres ?Mi _ ?sp =>
        let P := fresh "PRES" in
        assert (P : pres Mi Mn sp)
          by (rewrite EQM; eapply (pres_mem_denot_trans E Mi Mo _ log sp (proj1 HKold));
              [cbn [ev]; assumption | | vm_compute; reflexivity | exact PRES]; assumption);
        clear PRES EQM HKold; try clear Mo; rename P into PRES
      end end.
  Ltac save_know HK := pose proof (conj HK I) as HKb.
  Ltac grow_vals HL extra newlen :=
    lazymatch type of HL with length ?vals = ?n =>
      let HL' := fresh "HL" in
      assert (HL' : length (vals ++ extra) = newlen)
        by (rewrite length_app, ?junk_vals_length, HL; reflexivity);
      repeat match goal with
      | P : vals_ev vals ?i = ?v |- _ =>
          let P' := fresh "P" in
          assert (P' : vals_ev (vals ++ extra) i = v) by (rewrite vals_ev_app_l by (rewrite HL; lia); exact P);
          clear P; rename P' into P
      end;
      let v' := fresh "vals" in
      set (v' := vals ++ extra) in *; clearbody v'; clear HL; try clear vals; rename v' into vals; rename HL' into HL
    end.
  Ltac norm_know HK :=
    lazymatch type of HK with know_ok ?segs ?E ?M ?kn =>
      let kn' := eval vm_compute in kn in
      let EQ := fresh "EQkn" in
      assert (EQ : kn = kn') by (vm_compute; reflexivity);
      try rewrite EQ in HK; clear EQ end.
  Ltac norm_regs HR :=
    lazymatch type of HR with regs_ok ?E ?sr ?R =>
      let sr' := eval vm_compute in sr in
      let EQ := fresh "EQsr" in
      assert (EQ : sr = sr') by (vm_compute; reflexivity);
      try rewrite EQ in HR; clear EQ end.

  Ltac hdr_byte EV42 Pf off :=
    lazymatch type of EV42 with _ = ?B =>
    eapply (kword1_of_mem RSEGS _ _ (EVar 42) _ off _ EV42); [lia | lia | lia |
      lazymatch type of Pf with _ (Z_to_bv 64 ?a) = _ => replace (bv_unsigned B + off)%Z with a by lia; exact Pf end] end.
  Ltac hdr_word EV42 Pf off w z :=
    lazymatch type of EV42 with _ = ?B =>
    eapply (kword_intro RSEGS _ _ (EVar 42) _ off w (ELit z) (Z_to_bv 64 z) EV42 eq_refl); [lia | lia | lia | lia |
      lazymatch type of Pf with rdn _ _ (Z_to_bv 64 ?a) _ = _ => replace (bv_unsigned B + off)%Z with a by lia; exact Pf end] end.

  Theorem grow6 : forall mode Q R M V B e M0 K TOOM,
    full 6 sp0 p1 mb bw gm L B e can sec content M0 R M V ->
    (4194304 <= L)%Z ->
    (0x1000 <= bv_unsigned mb)%Z -> (bv_unsigned mb + 8192 <= bv_unsigned sp0 - 8388608)%Z -> (bv_unsigned mb mod 4096 = 0)%Z ->
    (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z ->
    (mode = true -> oom_branch M0 TOOM) -> half_branch mode Q 7 M0 K ->
    GG RSEGS mode Q K (mkCfg   (* [comment removed for export] *)  (mkst R (Z_to_bv 64 0xe1a24) M (seg_rom RSEGS)) (modelG 4194304 V)).
  Proof.
    intros mode Q R M V B e M0 K TOOM ST HL64 Hmb0 Hmb1 Hmba HspR HOOM HK1.
    (* [comment removed for export] *)
    pose (Mkeep := M).
    destruct ST as ((extra & HLx & HR & HK) & PRES & VS).
    destruct VS as (Vres & Vlim & Visp & rest & Vmaps & Vsz & Vlen & Vlive & Vcont & Vdisj & Vseps & Vlg & Vex).
    change (nb_of 6) with 4198400%Z in Vmaps, Vdisj.
    unfold ENV_RD in HR, HK. set (vals := vals_RD sp0 p1 mb bw gm L B e can sec extra) in *.
    assert (HL : length vals = 42%nat) by (subst vals; unfold vals_RD; rewrite length_app, HLx; reflexivity).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P1 : vals_ev vals 1 = p1) by reflexivity.
    assert (P2 : vals_ev vals 2 = mb) by reflexivity.
    assert (P3 : vals_ev vals 3 = gm) by reflexivity.
    assert (P4 : vals_ev vals 4 = Z_to_bv 64 L) by reflexivity.
    assert (P5 : vals_ev vals 5 = B) by reflexivity.
    assert (P6 : vals_ev vals 6 = e) by reflexivity.
    assert (P7 : vals_ev vals 7 = can) by reflexivity.
    assert (P8 : vals_ev vals 8 = sec) by reflexivity.
    clearbody vals. clear HLx extra.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    norm_know HK. norm_regs HR.
    (* [comment removed for export] *)
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_krange (EVar 5)) in exact i end) _ HK eq_refl) as KB.
    cbn [kentry_ok edenot ev] in KB. subst E. cbn [ev] in KB. rewrite P5 in KB.
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_kalign (EVar 5)) in exact i end) _ HK eq_refl) as KBal.
    cbn [kentry_ok edenot ev] in KBal. cbn [ev] in KBal. rewrite P5 in KBal. destruct KBal as [_ KBal].
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_kdisj (EVar 5) (EVar 2)) in exact i end) _ HK eq_refl) as KBmb.
    cbn [kentry_ok] in KBmb. unfold estart in KBmb. cbn [a_base a_off BA LA MBA edenot ev] in KBmb. rewrite P5, P2 in KBmb.
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_kdisj (EVar 0) (EVar 5)) in exact i end) _ HK eq_refl) as KBD.
    cbn [kentry_ok] in KBD. unfold estart, HUGE in KBD. cbn [a_base a_off BA LA MBA edenot ev] in KBD. rewrite P0, P5 in KBD.
    pose proof (u64_range B) as UB.
    assert (KBD' : (bv_unsigned B + bv_unsigned (snd (B, Z_to_bv 64 0)) <= bv_unsigned B)%Z -> True) by (intros; exact I). clear KBD'.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    (* [comment removed for export] *)
    assert (RL1 : length (pref 2097152 (dropz 2097152 content)) = Z.to_nat 2097152)
      by (pose proof (pref_length 2097152 (dropz 2097152 content) ltac:(lia)); pose proof (dropz_length 2097152 content ltac:(lia)); lia).
    assert (EBc : gblobs content 11%nat = pref 2097152 (dropz 2097152 content))
      by (rewrite <- (gblobs_cb 6) by lia; reflexivity).
      (* [comment removed for export] *)
      save_know HK. gg_block_keep scr0 42%nat. note_pres HKb EQM PRES.
      lazymatch goal with |- GG _ _ _ _ (mkCfg (mkst ?Rc _ ?Mc _) ?MD) =>
        eapply (gg_mmap_anon RSEGS mode Q Rc (Z_to_bv 64 0x2b3e20) Mc MD ECALLW 8388628 TOOM K fetch_26e234 is_ecall_ECALLW eq_refl eq_refl) end.
      + regv HR (17 : reg). reflexivity.
      + regv HR (11 : reg). reflexivity.
      + lia.
      + regv HR (12 : reg). reflexivity.
      + regv HR (13 : reg). reflexivity.
      + regv HR (14 : reg). apply bv_eq. vm_compute. reflexivity.
      + regv HR (15 : reg). reflexivity.
      + (* [comment removed for export] *)
        change (page_round_up_Z 8388628) with 8392704%Z.
        apply grant_exists; [ | | | | apply grant_budget_intro; [reflexivity | reflexivity |]];
          cbv [m_vmmaps HUReadStage.modelG mkModelA m_vm vmst_maps]; rewrite ?Vres, ?Visp, ?Vmaps, ?rsegs_reserved.
        * unfold init_sp_ok. cbv [m_vmmaps HUReadStage.modelG mkModelA m_vm vmst_maps]. rewrite Visp. unfold sp_window_lo. lia.
        * lia.
        * apply Forall_app. split.
          -- repeat constructor; cbn [snd]; rewrite u_small by lia; lia.
          -- constructor; [cbn [snd]; rewrite u_small by lia; lia|]. eapply Forall_impl; [|exact Vsz]. intros [? ?]; cbn [snd]; lia.
        * rewrite length_app. cbn [length]. lia.
        * unfold vm_live_bytes. rewrite Vmaps. cbn [live_bytes]. rewrite u_small by lia. pose proof Vlim as Vlim'. unfold LIM in Vlim'. lia.   (* [comment removed for export] *)
      + (* [comment removed for export] *)
        intros Hmode err Herr. cbn [mmap_errnos In] in Herr. destruct Herr as [<-|[]]. subst E.
        rewrite v_addi_pc4 by lia. change (2833952 + 4)%Z with 0x2b3e24%Z.
        lazymatch type of HR with regs_ok ?E _ _ =>
          pose proof (regs_set_a0 E _ _ (errno_ret ENOMEM) (ELit (- 12)) HR eq_refl) as HR2 end.
        clear HR. rename HR2 into HR.
        save_know HK. run_block_keep scr0 42%nat. note_pres HKb EQM PRES.
        apply (HOOM Hmode). split; [|split; [|split; [|split]]].
        * regv HR (2 : reg). rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev]. rewrite P0. f_equal; lia.
        * regv HR (3 : reg). reflexivity.
        * regv HR (4 : reg). reflexivity.
        * exact PRES.
        * intros d m Hd Hm.
          lazymatch type of HK with know_ok _ ?E ?Mc ?kn =>
            let i := kidx kn (is_kwr_cov (EVar 0) (-8388608)%Z 1%Z) in
            pose proof (kwr_store_ok RSEGS E Mc kn i (EVar 0) (-8388608)%Z 8388608%Z (-8388608 + d)%Z m HK eq_refl ltac:(lia) ltac:(lia)) as ST end.
          unfold adenot, v_addi in ST. cbn [a_base a_off BA LA MBA edenot ev] in ST. rewrite P0 in ST.
          replace (bv_unsigned sp0 - 8388608 + d)%Z with (bv_unsigned sp0 + (-8388608 + d))%Z by lia. exact ST.
      + (* [comment removed for export] *)
        intros B' HG.
        change (page_round_up_Z 8388628) with 8392704%Z in HG |- *.
        rewrite v_addi_pc4 by lia. change (2833952 + 4)%Z with 0x2b3e24%Z.
        pose proof (grant_ok_unpack _ _ _ _ HG) as (GA & GP & GC & GF & GLv).
        unfold alloc_top in GC. cbv [m_vmmaps HUReadStage.modelG mkModelA m_vm vmst_maps] in GC. rewrite Visp in GC. unfold stack_max_size in GC.
        unfold page_size in GA.
        cbv [m_vmmaps HUReadStage.modelG mkModelA m_vm vmst_maps] in GF, GLv. rewrite Vres, Vmaps, rsegs_reserved in GF.
        assert (GB1 : (0x354000 <= bv_unsigned B')%Z).
        { pose proof (region_free_In _ _ _ (Z_to_bv 64 65536) (Z_to_bv 64 856064) GF
                        ltac:(apply in_or_app; left; cbn [In]; tauto)) as X1.
          pose proof (region_free_In _ _ _ (Z_to_bv 64 921600) (Z_to_bv 64 1966080) GF
                        ltac:(apply in_or_app; left; cbn [In]; tauto)) as X2.
          pose proof (region_free_In _ _ _ (Z_to_bv 64 2887680) (Z_to_bv 64 380928) GF
                        ltac:(apply in_or_app; left; cbn [In]; tauto)) as X3.
          pose proof (region_free_In _ _ _ (Z_to_bv 64 3268608) (Z_to_bv 64 221184) GF
                        ltac:(apply in_or_app; left; cbn [In]; tauto)) as X.
          rewrite !u_small in X1 by lia. rewrite !u_small in X2 by lia. rewrite !u_small in X3 by lia.
          rewrite !u_small in X by lia. lia. }
        assert (GB2 : (bv_unsigned B' + 8392704 <= bv_unsigned B \/ bv_unsigned B + 4198400 <= bv_unsigned B')%Z).
        { pose proof (region_free_In _ _ _ B (Z_to_bv 64 4198400) GF
                        ltac:(apply in_or_app; right; left; reflexivity)) as X.
          rewrite !u_small in X by lia. lia. }
        assert (GB3 : (bv_unsigned B' + 8392704 <= bv_unsigned mb + 4096 \/ bv_unsigned mb + 8192 <= bv_unsigned B')%Z).
        { destruct Vcont as ([cb cs] & Cin & C1 & C2). cbn [fst snd] in C1, C2.
          pose proof (region_free_In _ _ _ cb cs GF ltac:(apply in_or_app; right; right; exact Cin)) as X.
          rewrite !u_small in X by lia. lia. }
        (* [comment removed for export] *)
        lazymatch type of HR with regs_ok _ ?sr ?Rc =>
          pose proof (env_app_regs vals [B'] _ sr Rc ltac:(rewrite HL; vm_compute; reflexivity) HR) as HR2 end.
        lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
          pose proof (env_app_know RSEGS vals [B'] _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2 end.
        clear HR HK. subst E.
        assert (P42 : vals_ev (vals ++ [B']) 42 = B') by (rewrite <- HL; apply vals_ev_last).
        grow_vals HL [B'] 43%nat.
        set (E := Env (vals_ev vals) (gblobs content)) in *.
        assert (AD42 : adenot E (SA (EVar 42) 0) = B').
        { unfold adenot, v_addi. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P42. apply bv_eq. rewrite u_small by lia. lia. }
        pose proof (regs_set_a0 E _ _ B' (EVar 42) HR2 ltac:(cbn [edenot ev]; subst E; exact P42)) as HR. clear HR2.
        assert (KA42 : kentry_ok RSEGS E M1 (KAlign (EVar 42) 4096)).
        { apply kalign_intro; [lia|]. cbn [edenot ev]. subst E. cbn [ev]. rewrite P42. exact GA. }
        assert (KR42 : kentry_ok RSEGS E M1 (KRange (EVar 42) 0x354000 (CEIL - 8392704))).
        { apply krange_intro. cbn [edenot ev]. subst E. cbn [ev]. rewrite P42. unfold CEIL. lia. }
        assert (KD42a : kentry_ok RSEGS E M1 (KDisj (SA (EVar 42) 0) 8392704 (SA (EVar 5) 0) 4198400)).
        { cbn [kentry_ok]. unfold estart. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P42, P5. lia. }
        assert (KD42b : kentry_ok RSEGS E M1 (KDisj (SA (EVar 42) 0) 8392704 (SA (EVar 2) 4096) 4096)).
        { cbn [kentry_ok]. unfold estart. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P42, P2. lia. }
        assert (KD42s : kentry_ok RSEGS E M1 (KDisj (SA (EVar 0) (-8388608)) HUGE (SA (EVar 42) 0) 8392704)).
        { cbn [kentry_ok]. unfold estart, HUGE. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P42, P0. lia. }
        pose proof (know_ok_cons _ _ _ _ _ KA42 (know_ok_cons _ _ _ _ _ KR42
                     (know_ok_cons _ _ _ _ _ KD42s (know_ok_cons _ _ _ _ _ KD42a (know_ok_cons _ _ _ _ _ KD42b HK2))))) as HK2'.
        clear KA42 KR42 KD42a KD42b KD42s HK2.
        lazymatch type of HK2' with know_ok _ _ ?Mc ?kn =>
          pose proof (know_ok_zfill RSEGS E Mc kn (EVar 42) 0 8392704 HK2'
                        ltac:(apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P42; lia) ltac:(lia) ltac:(lia)) as HK3 end.
        rewrite AD42 in HK3. clear HK2'.
        assert (KW42 : kentry_ok RSEGS E (zfill B' (Z_to_bv 64 8392704) M1) (KWr (SA (EVar 42) 0) 8392704)).
        { cbn [kentry_ok]. split; [apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P42; lia|].
          intros d m Hd Hm. unfold estart. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P42.
          unfold zfill. apply store_ok_zmem; rewrite ?u_small by lia; lia. }
        pose proof (know_ok_cons _ _ _ _ _ KW42 HK3) as HK. clear KW42 HK3.
        norm_know HK.
        assert (PRES2 : pres M0 (zfill B' (Z_to_bv 64 8392704) M1) sp0).
        { eapply pres_trans; [exact PRES|]. eapply (pres_far _ _ sp0 (bv_unsigned B') 8392704); [lia | lia | lia |].
          intros x Hx. apply zfill_outside. rewrite u_small by lia. exact Hx. }
        clear PRES. rename PRES2 into PRES.
        (* [comment removed for export] *)
        save_know HK. gg_block_keep scrT 43%nat.
        { apply xor_m1_ne0. cbn [edenot ev]. subst E. cbn [ev]. rewrite P42. lia. }
        note_pres HKb EQM PRES.
        (* [comment removed for export] *)
        assert (Hflat2 : forall k n, (0 <= k)%Z -> (0 <= n)%Z -> (k + n <= 8192)%Z -> flat E (SA (EVar 2) k) n).
        { intros k n Hk Hn Hkn. apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P2; lia. }
        krdv HK 2%nat 4176%Z 8%nat RM0. { apply Hflat2; lia. }
        krdv HK 2%nat 4192%Z 8%nat RW0. { apply Hflat2; lia. }
        unfold adenot, v_addi in RM0, RW0. cbn [a_base a_off BA LA MBA edenot ev] in RM0, RW0. subst E. cbn [ev] in RM0, RW0.
        rewrite P2 in RM0, RW0. rewrite P42 in RM0.
        set (E := Env (vals_ev vals) (gblobs content)) in *.
        kzero_at HK (EVar 42) 12%Z Z12. kzero_at HK (EVar 42) 13%Z Z13.
        cbn [edenot ev] in Z12, Z13. subst E. cbn [ev] in Z12, Z13. rewrite P42 in Z12, Z13.
        set (E := Env (vals_ev vals) (gblobs content)) in *.
        lazymatch goal with |- GG _ _ _ _ (mkCfg (mkst ?Rc _ ?Mc _) _) =>
        assert (EF : efH Mc (Z_to_bv 64 8) (bv_unsigned mb + 4160) (bv_unsigned B') 8396768 0 8388608 0 0 8392688 (bv_unsigned B' + 16) 8) end.
        { constructor.
          - vm_compute. reflexivity.
          - unfold slot_start, UNIT. lia.
          - vm_compute. reflexivity.
          - lia.
          - lia.
          - lia.
          - lia.
          - lia.
          - intros HH. exfalso. destruct HH as [HH|HH]; revert HH; vm_compute; congruence.
          - lia.
          - lia.
          - lia.
          - lia.
          - lia.
          - lia.
          - replace (bv_unsigned mb + 4160 + 16)%Z with (bv_unsigned mb + 4176)%Z by lia. rewrite RM0. f_equal. f_equal. apply bv_eq. rewrite u_small by lia. reflexivity.
          - replace (bv_unsigned mb + 4160 + 32)%Z with (bv_unsigned mb + 4192)%Z by lia. exact RW0.
          - replace (bv_unsigned B' + 16 - 4)%Z with (bv_unsigned B' + 12)%Z by lia. exact Z12.
          - replace (bv_unsigned B' + 16 - 3)%Z with (bv_unsigned B' + 13)%Z by lia. exact Z13.
          - intros HH. exfalso. apply HH. reflexivity.
          - replace (Z_to_bv 64 (bv_unsigned B' + 16 - 3)) with (adenot E (SA (EVar 42) 13))
              by (unfold adenot, v_addi; cbn [a_base a_off BA LA MBA edenot ev]; subst E; cbn [ev]; rewrite P42; f_equal; lia).
            kwr_solve HK.
          - intros jj Hj. unfold SCT.
            lazymatch type of HK with know_ok _ _ _ ?kn =>
              eapply (kimg_none RSEGS E _ kn ltac:(let i := kidx kn (is_kimg_cov 0x72234 96) in exact i) _ _ HK eq_refl) end. lia. }
        assert (RT : Hoare.ret_ok (Z_to_bv 64 0xe1a3c)) by (apply bv_eq; vm_compute; reflexivity).
        lazymatch goal with |- GG _ _ _ _ (mkCfg (mkst ?Rc _ ?Mc _) _) =>
          assert (G1 : getr Rc 1 = Z_to_bv 64 0xe1a3c) by (regv HR (1:reg); reflexivity);
          assert (G10 : getr Rc 10 = Z_to_bv 64 (bv_unsigned mb + 4160))
            by (regv HR (10:reg); rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off BA LA MBA edenot ev]; subst E; cbn [ev]; rewrite P2; reflexivity);
          assert (G11 : getr Rc 11 = Z_to_bv 64 0) by (regv HR (11:reg); reflexivity);
          assert (G12 : getr Rc 12 = Z_to_bv 64 8388608) by (regv HR (12:reg); reflexivity);
          assert (G13 : getr Rc 13 = Z_to_bv 64 8) by (regv HR (13:reg); reflexivity);
          destruct (ref_enframe Rc Mc (seg_rom RSEGS) (Z_to_bv 64 0xe1a3c) (Z_to_bv 64 8) _ _ _ _ _ _ _ _ _ _ EF G1 RT G10 G11 G12 G13)
            as (R3 & M3 & RUN & KEEP & A0 & FR & POST);
          clear RT G1 G10 G11 G12 G13 EF RM0 RW0 Z12 Z13 end.
        replace (Z_to_bv 64 2830836) with (0x2b31f4 : word) by (apply bv_eq; vm_compute; reflexivity).
        eapply gg_msteps; [reflexivity | reflexivity | exact RUN |]. clear RUN.
        lazymatch type of HR with regs_ok _ ?sr _ =>
          pose proof (regs_after_keeps vals _ sr _ R3 callee_saved ltac:(rewrite HL; vm_compute; reflexivity) HR KEEP callee_saved_no0) as HR3 end.
        rewrite HL in HR3. clear HR KEEP.
        lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
          pose proof (env_app_know RSEGS vals (junk_vals R3) _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2 end.
        clear HK Hflat2 AD42. subst E.
        grow_vals HL (junk_vals R3) 75%nat.
        set (E := Env (vals_ev vals) (gblobs content)) in *.
        lazymatch type of HR3 with regs_ok _ ?sr _ =>
          assert (HR : regs_ok E (sr_upd sr (ridx 10) (EAlu ALU_ADD (EVar 42) (ELit 144))) R3) end.
        { apply regs_ok_pin; [exact HR3|]. rewrite A0, edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off BA LA MBA edenot ev].
          subst E. cbn [ev]. rewrite P42. f_equal. lia. }
        clear HR3 A0. norm_regs HR.
        destruct FR as [FRo FRg].
        assert (OUT3 : forall x : word, (bv_unsigned x < estart E (SA (EVar 42) 13) \/ estart E (SA (EVar 42) 13) + 8392687 <= bv_unsigned x)%Z -> M3 x = M2 x).
        { intros x Hx. apply FRo. cbn [outside]. split; [|exact I]. unfold in_rng. rewrite u_small by lia.
          unfold estart in Hx. cbn [a_base a_off BA LA MBA edenot ev] in Hx. subst E. cbn [ev] in Hx. rewrite P42 in Hx. lia. }
        lazymatch type of HK2 with know_ok _ _ _ ?kn =>
          pose proof (know_ok_frame RSEGS E M2 M3 kn (EVar 42) 13 8392687 HK2
                        ltac:(apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P42; lia) OUT3 FRg) as HK4 end.
        clear HK2 OUT3.
        destruct POST as [Pp Pe Pr Pq Pm4 Pm3 Pm2 Pzr Pe5 Pe4 Ps3 Ps2 Prr]. cbn zeta in *. subst Pp Pe Pr Pq.
        specialize (Pzr ltac:(lia)). specialize (Pe5 ltac:(lia)). specialize (Pe4 ltac:(lia)).
        specialize (Ps3 ltac:(lia)). specialize (Ps2 ltac:(lia)).
        replace (0 + 32 * res_code (8392688 - 4 - 8388608 - 16 * 8))%Z with 160%Z in Pm3 by (vm_compute; reflexivity).
        replace (8392688 * 0 / 16 + 8)%Z with 8%Z in Pm2 by (vm_compute; reflexivity).
        replace (8392688 - 4 - 8388608 - 16 * 8)%Z with 3948%Z in Pe4 by reflexivity.
        assert (EV42 : edenot E (EVar 42) = B') by (cbn [edenot ev]; subst E; cbn [ev]; exact P42).
        assert (K1 : kentry_ok RSEGS E M3 (KWord (SA (EVar 42) 140) 1 (ELit 0))) by (hdr_byte EV42 Pm4 140%Z).
        assert (K2 : kentry_ok RSEGS E M3 (KWord (SA (EVar 42) 141) 1 (ELit 160))) by (hdr_byte EV42 Pm3 141%Z).
        assert (K3 : kentry_ok RSEGS E M3 (KWord (SA (EVar 42) 142) 2 (ELit 8))) by (hdr_word EV42 Pm2 142%Z 2%nat 8%Z).
        assert (K4 : kentry_ok RSEGS E M3 (KWord (SA (EVar 42) 8388752) 1 (ELit 0))) by (hdr_byte EV42 Pzr 8388752%Z).
        assert (K5 : kentry_ok RSEGS E M3 (KWord (SA (EVar 42) 8392695) 1 (ELit 0))) by (hdr_byte EV42 Pe5 8392695%Z).
        assert (K6 : kentry_ok RSEGS E M3 (KWord (SA (EVar 42) 8392696) 4 (ELit 3948))) by (hdr_word EV42 Pe4 8392696%Z 4%nat 3948%Z).
        assert (K7 : kentry_ok RSEGS E M3 (KWord (SA (EVar 42) 13) 1 (ELit 224))) by (hdr_byte EV42 Ps3 13%Z).
        assert (K8 : kentry_ok RSEGS E M3 (KWord (SA (EVar 42) 14) 2 (ELit 8))) by (hdr_word EV42 Ps2 14%Z 2%nat 8%Z).
        pose proof (know_ok_cons _ _ _ _ _ K1 (know_ok_cons _ _ _ _ _ K2 (know_ok_cons _ _ _ _ _ K3 (know_ok_cons _ _ _ _ _ K4
          (know_ok_cons _ _ _ _ _ K5 (know_ok_cons _ _ _ _ _ K6 (know_ok_cons _ _ _ _ _ K7 (know_ok_cons _ _ _ _ _ K8 HK4)))))))) as HK.
        clear K1 K2 K3 K4 K5 K6 K7 K8 HK4 Pm4 Pm3 Pm2 Pzr Pe5 Pe4 Ps3 Ps2 Prr.
        norm_know HK.
        assert (PRES2 : pres M0 M3 sp0).
        { eapply pres_trans; [exact PRES|]. eapply (pres_far _ _ sp0 (bv_unsigned B' + 13) 8392687); [lia | lia | lia |].
          intros x Hx. apply FRo. cbn [outside]. split; [|exact I]. unfold in_rng. rewrite u_small by lia. lia. }
        clear PRES FRo FRg. rename PRES2 into PRES.
        (* [comment removed for export] *)
        save_know HK. gg_block_keep scr0 75%nat. note_pres HKb EQM PRES.
        (* [comment removed for export] *)
        assert (Hflat5 : forall k n, (0 <= k)%Z -> (0 <= n)%Z -> (k + n <= 4198400)%Z -> flat E (SA (EVar 5) k) n).
        { intros k n Hk Hn Hkn. apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P5; lia. }
        lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
          pose proof (kblob_rdn RSEGS E Mc kn (EVar 5) 128 (ELit 2097152) 10%nat HK ltac:(vm_compute; reflexivity)) as SRC1;
          pose proof (kblob_rdn RSEGS E Mc kn (EVar 5) 2097280 (ELit 2097152) 11%nat HK ltac:(vm_compute; reflexivity)) as SRC2 end.
        change (eb E 10%nat) with (gblobs content 10%nat) in SRC1. rewrite (gblobs_hb 6) in SRC1 by lia. change (held_of 6) with 2097152%Z in SRC1.
        change (eb E 11%nat) with (gblobs content 11%nat) in SRC2. rewrite EBc in SRC2.
        assert (RLh : length (pref 2097152 content) = Z.to_nat 2097152) by (pose proof (pref_length 2097152 content ltac:(lia)); lia).
        assert (SRC : rdn RSEGS M4 (adenot E (SA (EVar 5) 128)) (length (pref 4194304 content)) = Some (pref 4194304 content)).
        { replace (pref 4194304 content) with (pref 2097152 content ++ pref 2097152 (dropz 2097152 content))
            by (rewrite pref_app by lia; reflexivity).
          rewrite length_app, RLh, RL1. apply SeqExec.rdn_app.
          - rewrite RLh in SRC1. exact SRC1.
          - rewrite RL1 in SRC2. replace (adenot E (SA (EVar 5) 128) + nat_to_word (Z.to_nat 2097152)) with (adenot E (SA (EVar 5) 2097280)); [exact SRC2|].
            unfold adenot, v_addi, nat_to_word. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P5. apply bv_eq.
            rewrite bv_add_unsigned. rewrite Z2Nat.id by lia. rewrite !u_small by lia. rewrite bv_wrap_small; [lia|]. unfold bv_modulus. lia. }
        clear SRC1 SRC2.
        assert (RLc : length (pref 4194304 content) = Z.to_nat 4194304) by (pose proof (pref_length 4194304 content ltac:(lia)); lia).
        assert (EBf : gblobs content 12%nat = pref 4194304 content) by (rewrite <- (gblobs_fb 6) by lia; reflexivity).
        set (dst := adenot E (SA (EVar 42) 144)). set (src := adenot E (SA (EVar 5) 128)) in SRC.
        assert (Hudst : bv_unsigned dst = (bv_unsigned B' + 144)%Z).
        { subst dst. unfold adenot, v_addi. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P42, u_small by lia. lia. }
        assert (Husrc : bv_unsigned src = (bv_unsigned B + 128)%Z).
        { subst src. unfold adenot, v_addi. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P5, u_small by lia. lia. }
        lazymatch goal with |- GG _ _ _ _ (mkCfg (mkst ?Rc _ ?Mc _) _) =>
          assert (MC : mcH Mc dst src 4194304 (pref 4194304 content)) end.
        { constructor.
          - lia.
          - exact RLc.
          - exact SRC.
          - subst dst. rewrite RLc. kwr_solve HK.
          - lia.
          - lia.
          - lia. }
        assert (RT : Hoare.ret_ok (Z_to_bv 64 0xe1a5c)) by (apply bv_eq; vm_compute; reflexivity).
        lazymatch goal with |- GG _ _ _ _ (mkCfg (mkst ?Rc _ ?Mc _) _) =>
          assert (G1 : getr Rc 1 = Z_to_bv 64 0xe1a5c) by (regv HR (1:reg); reflexivity);
          assert (G10 : getr Rc 10 = dst) by (regv HR (10:reg); subst dst; apply edenot_add_lit);
          assert (G11 : getr Rc 11 = src) by (regv HR (11:reg); subst src; unfold bx; apply edenot_add_lit);
          assert (G12 : getr Rc 12 = Z_to_bv 64 4194304) by (regv HR (12:reg); reflexivity);
          destruct (ref_memcpy Mc dst src 4194304 _ (seg_rom RSEGS) MC Rc (Z_to_bv 64 0xe1a5c) RT G1 G10 G11 G12) as (R5 & RUN & KEEP);
          clear RT G1 G10 G11 G12 MC SRC end.
        replace (Z_to_bv 64 2867236) with (0x2bc024 : word) by (apply bv_eq; vm_compute; reflexivity).
        eapply gg_msteps; [reflexivity | reflexivity | exact RUN |]. clear RUN.
        lazymatch type of HR with regs_ok _ ?sr _ =>
          pose proof (regs_after_keeps vals _ sr _ R5 callee_kept ltac:(rewrite HL; vm_compute; reflexivity) HR KEEP callee_kept_no0) as HR5 end.
        rewrite HL in HR5. clear HR KEEP.
        lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
          pose proof (know_ok_wblob RSEGS E Mc kn (EVar 42) 144 12%nat (pref 4194304 content) HK
                        ltac:(apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P42, ?RLc; lia)
                        EBf ltac:(rewrite RLc; lia) ltac:(rewrite RLc; lia)) as HK2 end.
        fold dst in HK2. rewrite RLc, Z2Nat.id in HK2 by lia.
        assert (Hdst : dst = Z_to_bv 64 (bv_unsigned B' + 144)) by (apply bv_eq; rewrite Hudst, u_small by lia; reflexivity).
        rewrite Hdst in HK2 |- *.
        assert (PRES2 : pres M0 (wbytes M4 (Z_to_bv 64 (bv_unsigned B' + 144)) (pref 4194304 content)) sp0).
        { eapply pres_trans; [exact PRES|]. eapply (pres_far _ _ sp0 (bv_unsigned B' + 144) 4194304); [lia | lia | lia |].
          intros x Hx. apply MemSplit.wbytes_outside; rewrite u_small, RLc by lia; lia. }
        clear PRES HK. rename PRES2 into PRES.
        lazymatch type of HK2 with know_ok _ _ ?Mc ?kn =>
          pose proof (env_app_know RSEGS vals (junk_vals R5) _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK end.
        clear HK2. subst src E. clear dst Hdst Hudst Husrc EV42 Hflat5.
        grow_vals HL (junk_vals R5) 107%nat.
        set (E := Env (vals_ev vals) (gblobs content)) in *. rename HR5 into HR.
        norm_regs HR. norm_know HK.
        (* [comment removed for export] *)
        save_know HK. gg_block_keep scr0 107%nat. note_pres HKb EQM PRES.
        (* [comment removed for export] *)
        assert (Hflat5 : forall k n, (0 <= k)%Z -> (0 <= n)%Z -> (k + n <= 4198400)%Z -> flat E (SA (EVar 5) k) n).
        { intros k n Hk Hn Hkn. apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P5; lia. }
        assert (Hflat2 : forall k n, (0 <= k)%Z -> (0 <= n)%Z -> (k + n <= 8192)%Z -> flat E (SA (EVar 2) k) n).
        { intros k n Hk Hn Hkn. apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P2; lia. }
        krdv HK 5%nat 124%Z 1%nat Gb4. { apply Hflat5; lia. }
        krdv HK 5%nat 125%Z 1%nat Gb3. { apply Hflat5; lia. }
        krdv HK 5%nat 126%Z 2%nat Goff. { apply Hflat5; lia. }
        krdv HK 5%nat 0%Z 8%nat Gmeta. { apply Hflat5; lia. }
        krdv HK 2%nat 4136%Z 8%nat Gmem. { apply Hflat2; lia. }
        krdv HK 2%nat 4152%Z 8%nat GW. { apply Hflat2; lia. }
        krdv HK 2%nat 4144%Z 4%nat Gav. { apply Hflat2; lia. }
        krdv HK 2%nat 4148%Z 4%nat Gfr. { apply Hflat2; lia. }
        krdv HK 2%nat 4096%Z 8%nat Garea. { apply Hflat2; lia. }
        krd HK 0x351df0%Z 8%nat Gsec.
        unfold adenot, v_addi in Gb4, Gb3, Goff, Gmeta, Gmem, GW, Gav, Gfr, Garea.
        cbn [a_base a_off BA LA MBA edenot ev] in Gb4, Gb3, Goff, Gmeta, Gmem, GW, Gav, Gfr, Garea. subst E.
        cbn [ev] in Gb4, Gb3, Goff, Gmeta, Gmem, GW, Gav, Gfr, Garea.
        rewrite P5 in Gb4, Gb3, Goff, Gmeta, Gmem. rewrite P2 in Gmeta, Gmem, GW, Gav, Gfr, Garea.
        cbn [ev] in Gsec. rewrite ?P8 in Garea. rewrite ?P8 in Gsec.
        unfold mbx in Gmeta. rewrite alu_add in Gmeta. unfold v_add in Gmeta.
        set (E := Env (vals_ev vals) (gblobs content)) in *.
        lazymatch goal with |- GG _ _ _ _ (mkCfg (mkst ?Rc _ ?Mc _) _) =>
          assert (GMR : gm_reads Mc (bv_unsigned B + 128) (bv_unsigned B) (bv_unsigned mb + 4120) 0 5 7 4202464 0 0 sec) end.
        { constructor.
          - apply rdn1_mem_high; [rewrite u_small by lia; lia|]. replace (bv_unsigned B + 128 - 4)%Z with (bv_unsigned B + 124)%Z by lia. exact Gb4.
          - apply rdn1_mem_high; [rewrite u_small by lia; lia|]. replace (bv_unsigned B + 128 - 3)%Z with (bv_unsigned B + 125)%Z by lia. exact Gb3.
          - replace (bv_unsigned B + 128 - 2)%Z with (bv_unsigned B + 126)%Z by lia. exact Goff.
          - rewrite Z.add_0_r in Gmeta. change (bv_unsigned (Z_to_bv 64 4120)) with 4120%Z in Gmeta. exact Gmeta.
          - replace (bv_unsigned mb + 4120 + 16)%Z with (bv_unsigned mb + 4136)%Z by lia. rewrite Gmem. f_equal. f_equal. symmetry. apply Z_to_bv_bv_unsigned.
          - replace (bv_unsigned mb + 4120 + 32)%Z with (bv_unsigned mb + 4152)%Z by lia. exact GW.
          - replace (bv_unsigned mb + 4120 + 24)%Z with (bv_unsigned mb + 4144)%Z by lia. exact Gav.
          - replace (bv_unsigned mb + 4120 + 28)%Z with (bv_unsigned mb + 4148)%Z by lia. exact Gfr.
          - assert (HM24 : ((bv_unsigned mb + 4120) mod 4096 = 24)%Z)
              by (rewrite <- Zplus_mod_idemp_l, Hmba; reflexivity).
            rewrite HM24. replace (bv_unsigned mb + 4120 - 24)%Z with (bv_unsigned mb + 4096)%Z by lia. exact Garea.
          - exact Gsec.
          - intros i Hi. lazymatch type of HK with know_ok _ _ _ ?kn =>
              eapply (kimg_none RSEGS E _ kn ltac:(let jj := kidx kn (is_kimg_cov 0x72234 96) in exact jj) _ _ HK eq_refl) end. lia. }
        assert (GMP : gm_pure (bv_unsigned B + 128) (bv_unsigned B) (bv_unsigned mb + 4120) 0 5 7 4202464 0 0).
        { constructor.
          all: try (change (w_lastidx 4202464) with 0%Z); try (change (w_sizeclass 4202464) with 63%Z);
               try (change (w_maplen 4202464) with 1025%Z).
          1: { rewrite <- Zplus_mod_idemp_l.
               replace (bv_unsigned B mod 16)%Z with 0%Z; [reflexivity|].
               symmetry. apply Znumtheory.Zdivide_mod. apply (Z.divide_trans _ 4096); [exists 256%Z; reflexivity|].
               apply Znumtheory.Zmod_divide; [lia | exact KBal]. }
          all: try lia.
          all: reflexivity. }
        clear Gb4 Gb3 Goff Gmeta Gmem GW Gav Gfr Garea Gsec Hflat2 Hflat5.
        assert (RT : Hoare.ret_ok (Z_to_bv 64 0x2b1c78)) by (apply bv_eq; vm_compute; reflexivity).
        lazymatch goal with |- GG _ _ _ _ (mkCfg (mkst ?Rc _ ?Mc _) _) =>
          assert (G10 : getr Rc 10 = Z_to_bv 64 (bv_unsigned B + 128))
            by (regv HR (10:reg); unfold bx; rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off BA LA MBA edenot ev]; subst E; cbn [ev]; rewrite P5; reflexivity);
          assert (G1 : getr Rc 1 = Z_to_bv 64 0x2b1c78) by (regv HR (1:reg); reflexivity);
          destruct (get_meta_run Rc Mc (seg_rom RSEGS) (Z_to_bv 64 0x2b1c78) _ _ _ _ _ _ _ _ _ _ GMR GMP G10 G1 RT) as (R7 & RUN & A0 & A1 & KEEP);
          clear RT G1 G10 GMR GMP end.
        replace (Z_to_bv 64 2825760) with (0x2b1e20 : word) by (apply bv_eq; vm_compute; reflexivity).
        eapply gg_msteps; [reflexivity | reflexivity | exact RUN |]. clear RUN.
        lazymatch type of HR with regs_ok _ ?sr _ =>
          pose proof (regs_after_keeps vals _ sr _ R7 gm_kept ltac:(rewrite HL; vm_compute; reflexivity) HR (gm_keeps_kept _ _ KEEP) gm_kept_no0) as HR7 end.
        rewrite HL in HR7. clear HR KEEP.
        lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
          pose proof (env_app_know RSEGS vals (junk_vals R7) _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2 end.
        clear HK. subst E.
        grow_vals HL (junk_vals R7) 139%nat.
        set (E := Env (vals_ev vals) (gblobs content)) in *. rename HK2 into HK.
        lazymatch type of HR7 with regs_ok _ ?sr _ =>
          assert (HR : regs_ok E (sr_upd (sr_upd sr (ridx 10) (mbx 4120)) (ridx 11) (ELit 7)) R7) end.
        { apply regs_ok_pin; [apply regs_ok_pin; [exact HR7|]|].
          - rewrite A0. unfold mbx. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P2. reflexivity.
          - rewrite A1. reflexivity. }
        clear HR7 A0 A1. norm_regs HR. norm_know HK.
        (* [comment removed for export] *)
        save_know HK. gg_block_keep scr0 139%nat. note_pres HKb EQM PRES.
        (* [comment removed for export] *)
        lazymatch goal with |- GG _ _ _ _ (mkCfg (mkst ?Rc _ ?Mc _) ?MD) =>
          eapply (gg_munmap RSEGS mode Q Rc (Z_to_bv 64 0x2b3f8c) Mc MD ECALLW B 4198400 K fetch_26e3a0 is_ecall_ECALLW eq_refl eq_refl) end.
        * regv HR (17:reg). reflexivity.
        * regv HR (10:reg). cbn [edenot ev]. subst E. cbn [ev]. exact P5.
        * unfold page_size. exact KBal.
        * regv HR (11:reg). reflexivity.
        * lia.
        * change (page_round_up_Z 4198400) with 4198400%Z. unfold TASK_SIZE. lia.
        * change (page_round_up_Z 4198400) with 4198400%Z. cbv [m_vmmaps mmap_model with_vmmaps HUReadStage.modelG mkModelA m_vm vmst_maps]. cbn [vm_maps]. rewrite Vmaps. apply map_has_cons. apply map_has_head.
        * change (page_round_up_Z 4198400) with 4198400%Z.
          rewrite v_addi_pc4 by lia. change (0x2b3f8c + 4)%Z with 0x2b3f90%Z.
          lazymatch type of HR with regs_ok ?E _ _ =>
            pose proof (regs_set_a0 E _ _ (Z_to_bv 64 0) (ELit 0) HR eq_refl) as HR2 end.
          clear HR. rename HR2 into HR.
          assert (AD5 : adenot E (SA (EVar 5) 0) = B).
          { unfold adenot, v_addi. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P5. apply bv_eq. rewrite u_small by lia. lia. }
          lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
            pose proof (know_ok_unfill RSEGS E Mc kn (EVar 5) 0 4198400 HK
                          ltac:(apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P5; lia) ltac:(lia)) as HK2 end.
          rewrite AD5 in HK2. clear HK AD5. rename HK2 into HK. norm_know HK.
          lazymatch goal with |- GG _ _ _ _ (mkCfg (mkst _ _ ?Mc _) _) =>
            assert (PRES2 : pres M0 Mc sp0) end.
          { eapply pres_trans; [exact PRES|]. eapply (pres_far _ _ sp0 (bv_unsigned B) 4198400); [lia | lia | lia |].
            intros x Hx. apply unfill_outside. rewrite u_small by lia. exact Hx. }
          clear PRES. rename PRES2 into PRES.
          (* [comment removed for export] *)
          save_know HK. gg_block_keep scr0 139%nat. note_pres HKb EQM PRES.
          (* [comment removed for export] *)
          rewrite munmap_model_simple by reflexivity.
          unfold mmap_model, with_vmmaps.
          cbv [m_vmmaps m_fd m_io m_fsys m_proc m_lim m_time m_vm m_vm_lazy m_vm_materialized vmst_maps vmst_lazy vmst_materialized
               HUReadStage.modelG mkModelA]. cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk vm_limit vm_mmap_base vm_init_sp].
          lazymatch goal with |- GG _ _ _ _ (mkCfg (mkst ?Rc _ ?Mc _) (mkModelOf _ (mkVmState ?V' _ _) _ _ _ _ _)) =>
            change (GG RSEGS mode Q K (mkCfg (mkst Rc (Z_to_bv 64 0xe1a68) Mc (seg_rom RSEGS)) (modelG (held_of 7) V'))) end.
          unfold half_branch in HK1. apply (HK1 _ _ _ B' (edenot E (EExt true 0 4 (EVar 6)))).
          lazymatch type of HR with regs_ok _ ?srf _ =>
          lazymatch type of HK with know_ok _ _ ?Mf ?knf =>
            set (rvl := [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 42; EExt true 0 4 (EVar 6); EVar 7; EVar 8; ELit 0] ++ srf);
            assert (XB : forall k, gblobs content k = eb E ((fun k : nat => k) k)) by (intros; reflexivity);
            split; [ exists (map (edenot E) srf); split; [rewrite length_map; reflexivity|];
                     replace (ENV_RD sp0 p1 mb bw gm L B' (edenot E (EExt true 0 4 (EVar 6))) can sec (map (edenot E) srf) content)
                        with (xenv E rvl (gblobs content));
                     [ split; [ apply (regs_ok_xfer E rvl (fun k => k) _ XB srf (sr_HALF 7) _ HR); [reflexivity | reflexivity |]
                              | apply (know_ok_xfer_entails RSEGS E rvl (fun k => k) _ Mf knf (kn_HALF 7) XB HK) ]
                     | ]
                   | split; [exact PRES |] ]
          end end.
          -- intros i Hi Hne. exfalso. apply Hne. vm_compute in Hi. cbv [In] in Hi. destruct Hi as [<-|[]]. reflexivity.
          -- match goal with |- Forall _ ?l => replace l with (@nil kentry) by (vm_compute; reflexivity) end. constructor.
          -- unfold ENV_RD, xenv, vals_RD. f_equal. subst rvl. rewrite map_app. cbn [map app].
             cbn [edenot ev]. subst E. cbn [ev]. rewrite P0, P1, P2, P3, P4, P42, P7, P8. reflexivity.
          -- (* [comment removed for export] *)
             unfold vm_stage. cbn [vm_reserved vm_limit vm_maps vm_init_sp]. split; [exact Vres|]. split; [exact Vlim|]. split; [exact Visp|].
             rewrite Vmaps.
             assert (Hbb : B' <> B) by (intros HH; rewrite HH in GB2; lia).
             exists (map_remove rest B). split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
             ++ change (nb_of 7) with 8392704%Z. rewrite map_remove_skip by exact Hbb. rewrite map_remove_head. reflexivity.
             ++ apply incl_Forall with (l1 := rest); [|exact Vsz]. unfold map_remove. apply incl_filter.
             ++ pose proof (map_remove_length rest B). lia.
             ++ pose proof (live_bytes_map_remove_le rest B). lia.
             ++ destruct Vcont as (pc & Cin & C1 & C2). exists pc. split; [|split; assumption].
                unfold map_remove. apply filter_In. split; [exact Cin|]. destruct pc as [cb cs]. cbn [fst snd] in C1, C2 |- *.
                apply Bool.negb_true_iff. unfold bv_eqb. apply Z.eqb_neq. intros HH.
                pose proof (proj1 (Forall_forall _ _) Vdisj _ Cin) as X. cbn [fst snd] in X.
                pose proof (proj1 (Forall_forall _ _) Vsz _ Cin) as Y. cbn [snd] in Y. lia.
             ++ apply Forall_forall. intros [qb qs] Hq. cbn [fst snd]. change (nb_of 7) with 8392704%Z.
                unfold map_remove in Hq. apply filter_In in Hq as [Hq _].
                pose proof (region_free_In _ _ _ qb qs GF ltac:(apply in_or_app; right; right; exact Hq)) as X.
                rewrite u_small in X by lia. lia.
             ++ unfold map_remove. apply seps_filter. exact Vseps.
             ++ split. { (* [comment removed for export] *)
                apply (HUTargetPre.vm_ledger_frame mb bw V); [exact Vlg | |].
                ** intros Hin. rewrite Vmaps in Hin. destruct Hin as [EE | Hin].
                   { exfalso. apply (f_equal snd) in EE. cbn [snd] in EE. apply (f_equal bv_unsigned) in EE. rewrite !u_small in EE by lia. lia. }
                   apply HUTargetPre.In_map_remove_keep; [right; right; exact Hin | cbn [fst]].
                   intros HH. pose proof (proj1 (Forall_forall _ _) Vdisj _ Hin) as X. cbn [fst snd] in X. rewrite HH, u_small in X by lia. lia.
                ** intros Hin Hcov. rewrite Vmaps in Hin. destruct Hin as [EE | Hin].
                   { exfalso. apply (f_equal snd) in EE. cbn [snd] in EE. apply (f_equal bv_unsigned) in EE. rewrite !u_small in EE by lia. lia. }
                   pose proof (proj1 (Forall_forall _ _) Vdisj _ Hin) as X. cbn [fst snd] in X. rewrite u_small in X by lia.
                   rewrite u_small by lia. apply HUTargetPre.maps_subtract_keep_cover; [lia | lia | lia | exact Hcov | lia]. }
                (* [comment removed for export] *)
                apply (vm_exact_grow V _ sp0 mb bw B B' _ _ Vex);
                  [vm_compute; split; reflexivity | vm_compute; split; reflexivity | cbn [vm_maps]; rewrite Vmaps; reflexivity | reflexivity
                  | reflexivity | reflexivity | exact GA | exact GP | match goal with |- (_ + ?n <= _)%Z => let n' := eval vm_compute in n in change n with n' end; lia
                  | rewrite rsegs_reserved, Vmaps; exact GF].
  Qed.
End G.
End H0ReadG6.

(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.PropExec OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.CatExec OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.CatSim OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.SeqExec OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.StoreOk OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.ShapeAlg OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.Nodes OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.MmapSim OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.AllocSim OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.FileSim OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.AgentLib OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.MemSplit OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.Frame OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.StreamSim OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.SymExec OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.SymExec2 OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.SymExec2Sound OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.SymRun OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.SymDrive OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.SymDriveX OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.RefMemcpyLib HUMemcpyBase HUMemcpy OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.MallocDefs HUEnframeBase HUEnframe HUGetMeta OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.RefNodes OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.LibKnowFrame OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.LibKnowXfer OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.RefReadLib HUReadBase HUReadStage HUReadChunk HUReadG0 HUTargetPre OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.ExistsRun OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.PhaseG HUReadChunk.H0ReadChunkW.
Import ConeCfg.
(* [comment removed for export] *)
(* [comment removed for export] *)

Import ListNotations.
Import ConeCfg.
Open Scope bv_scope.
Import SX2. Import SX2S.
Import ConeCfg.

#[local] Abbreviation RSEGS := Ubsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Tactic Notation "run_block" constr(scr) constr(NX) := run_block_gen RFUEL RSTOPS scr NX false.
#[local] Tactic Notation "run_block_keep" constr(scr) constr(NX) := run_block_gen RFUEL RSTOPS scr NX true.
#[local] Tactic Notation "gg_block" constr(scr) constr(NX) := gg_block_gen RFUEL RSTOPS scr NX false.
#[local] Tactic Notation "gg_block_keep" constr(scr) constr(NX) := gg_block_gen RFUEL RSTOPS scr NX true.

Section G.
  Variables (sp0 p1 mb bw gm can sec : word) (path content : list byte).
  Variables (stdin0 : AmbIn) (fs0 : Fs) (tid : word).
  Hypothesis Hfile : fs_lookup fs0 path = Some content.

  Let L : Z := Z.of_nat (length content).
  #[local] Notation modelG := (HUReadStage.modelG path stdin0 fs0 tid) (only parsing).
  #[local] Notation oom_branch := (HUReadStage.oom_branch sp0 path stdin0 fs0 tid) (only parsing).

  (* [comment removed for export] *)
  Definition half_branch (mode : bool) (Q : config -> Prop) (j' : Z) (M0 : word -> option byte) (K : TSet) : Prop :=
    forall R M V B e, half j' sp0 p1 mb bw gm L B e can sec content M0 R M V ->
      GG RSEGS mode Q K (mkCfg (mkst R (Z_to_bv 64 0xe1a68) M (seg_rom RSEGS)) (modelG (held_of j') V)).

  Ltac note_pres HKold EQM PRES :=
    lazymatch type of EQM with ?Mn = mem_denot ?E ?Mo ?log =>
      lazymatch type of PRES with pres ?Mi _ ?sp =>
        let P := fresh "PRES" in
        assert (P : pres Mi Mn sp)
          by (rewrite EQM; eapply (pres_mem_denot_trans E Mi Mo _ log sp (proj1 HKold));
              [cbn [ev]; assumption | | vm_compute; reflexivity | exact PRES]; assumption);
        clear PRES EQM HKold; try clear Mo; rename P into PRES
      end end.
  Ltac save_know HK := pose proof (conj HK I) as HKb.
  Ltac grow_vals HL extra newlen :=
    lazymatch type of HL with length ?vals = ?n =>
      let HL' := fresh "HL" in
      assert (HL' : length (vals ++ extra) = newlen)
        by (rewrite length_app, ?junk_vals_length, HL; reflexivity);
      repeat match goal with
      | P : vals_ev vals ?i = ?v |- _ =>
          let P' := fresh "P" in
          assert (P' : vals_ev (vals ++ extra) i = v) by (rewrite vals_ev_app_l by (rewrite HL; lia); exact P);
          clear P; rename P' into P
      end;
      let v' := fresh "vals" in
      set (v' := vals ++ extra) in *; clearbody v'; clear HL; try clear vals; rename v' into vals; rename HL' into HL
    end.
  Ltac norm_know HK :=
    lazymatch type of HK with know_ok ?segs ?E ?M ?kn =>
      let kn' := eval vm_compute in kn in
      let EQ := fresh "EQkn" in
      assert (EQ : kn = kn') by (vm_compute; reflexivity);
      try rewrite EQ in HK; clear EQ end.
  Ltac norm_regs HR :=
    lazymatch type of HR with regs_ok ?E ?sr ?R =>
      let sr' := eval vm_compute in sr in
      let EQ := fresh "EQsr" in
      assert (EQ : sr = sr') by (vm_compute; reflexivity);
      try rewrite EQ in HR; clear EQ end.

  Ltac hdr_byte EV42 Pf off :=
    lazymatch type of EV42 with _ = ?B =>
    eapply (kword1_of_mem RSEGS _ _ (EVar 42) _ off _ EV42); [lia | lia | lia |
      lazymatch type of Pf with _ (Z_to_bv 64 ?a) = _ => replace (bv_unsigned B + off)%Z with a by lia; exact Pf end] end.
  Ltac hdr_word EV42 Pf off w z :=
    lazymatch type of EV42 with _ = ?B =>
    eapply (kword_intro RSEGS _ _ (EVar 42) _ off w (ELit z) (Z_to_bv 64 z) EV42 eq_refl); [lia | lia | lia | lia |
      lazymatch type of Pf with rdn _ _ (Z_to_bv 64 ?a) _ = _ => replace (bv_unsigned B + off)%Z with a by lia; exact Pf end] end.

  Theorem grow4 : forall mode Q R M V B e M0 K TOOM,
    full 4 sp0 p1 mb bw gm L B e can sec content M0 R M V ->
    (1048576 <= L)%Z ->
    (0x1000 <= bv_unsigned mb)%Z -> (bv_unsigned mb + 8192 <= bv_unsigned sp0 - 8388608)%Z -> (bv_unsigned mb mod 4096 = 0)%Z ->
    (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z ->
    (mode = true -> oom_branch M0 TOOM) -> half_branch mode Q 5 M0 K ->
    GG RSEGS mode Q K (mkCfg   (* [comment removed for export] *)  (mkst R (Z_to_bv 64 0xe1a24) M (seg_rom RSEGS)) (modelG 1048576 V)).
  Proof.
    intros mode Q R M V B e M0 K TOOM ST HL64 Hmb0 Hmb1 Hmba HspR HOOM HK1.
    (* [comment removed for export] *)
    pose (Mkeep := M).
    destruct ST as ((extra & HLx & HR & HK) & PRES & VS).
    destruct VS as (Vres & Vlim & Visp & rest & Vmaps & Vsz & Vlen & Vlive & Vcont & Vdisj & Vseps & Vlg & Vex).
    change (nb_of 4) with 1052672%Z in Vmaps, Vdisj.
    unfold ENV_RD in HR, HK. set (vals := vals_RD sp0 p1 mb bw gm L B e can sec extra) in *.
    assert (HL : length vals = 42%nat) by (subst vals; unfold vals_RD; rewrite length_app, HLx; reflexivity).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P1 : vals_ev vals 1 = p1) by reflexivity.
    assert (P2 : vals_ev vals 2 = mb) by reflexivity.
    assert (P3 : vals_ev vals 3 = gm) by reflexivity.
    assert (P4 : vals_ev vals 4 = Z_to_bv 64 L) by reflexivity.
    assert (P5 : vals_ev vals 5 = B) by reflexivity.
    assert (P6 : vals_ev vals 6 = e) by reflexivity.
    assert (P7 : vals_ev vals 7 = can) by reflexivity.
    assert (P8 : vals_ev vals 8 = sec) by reflexivity.
    clearbody vals. clear HLx extra.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    norm_know HK. norm_regs HR.
    (* [comment removed for export] *)
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_krange (EVar 5)) in exact i end) _ HK eq_refl) as KB.
    cbn [kentry_ok edenot ev] in KB. subst E. cbn [ev] in KB. rewrite P5 in KB.
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_kalign (EVar 5)) in exact i end) _ HK eq_refl) as KBal.
    cbn [kentry_ok edenot ev] in KBal. cbn [ev] in KBal. rewrite P5 in KBal. destruct KBal as [_ KBal].
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_kdisj (EVar 5) (EVar 2)) in exact i end) _ HK eq_refl) as KBmb.
    cbn [kentry_ok] in KBmb. unfold estart in KBmb. cbn [a_base a_off BA LA MBA edenot ev] in KBmb. rewrite P5, P2 in KBmb.
    pose proof (know_nth RSEGS _ _ _ ltac:(lazymatch type of HK with know_ok _ _ _ ?kn => let i := kidx kn (is_kdisj (EVar 0) (EVar 5)) in exact i end) _ HK eq_refl) as KBD.
    cbn [kentry_ok] in KBD. unfold estart, HUGE in KBD. cbn [a_base a_off BA LA MBA edenot ev] in KBD. rewrite P0, P5 in KBD.
    pose proof (u64_range B) as UB.
    assert (KBD' : (bv_unsigned B + bv_unsigned (snd (B, Z_to_bv 64 0)) <= bv_unsigned B)%Z -> True) by (intros; exact I). clear KBD'.
    set (E := Env (vals_ev vals) (gblobs content)) in *.
    (* [comment removed for export] *)
    assert (RL1 : length (pref 524288 (dropz 524288 content)) = Z.to_nat 524288)
      by (pose proof (pref_length 524288 (dropz 524288 content) ltac:(lia)); pose proof (dropz_length 524288 content ltac:(lia)); lia).
    assert (EBc : gblobs content 7%nat = pref 524288 (dropz 524288 content))
      by (rewrite <- (gblobs_cb 4) by lia; reflexivity).
      (* [comment removed for export] *)
      save_know HK. gg_block_keep scr0 42%nat. note_pres HKb EQM PRES.
      lazymatch goal with |- GG _ _ _ _ (mkCfg (mkst ?Rc _ ?Mc _) ?MD) =>
        eapply (gg_mmap_anon RSEGS mode Q Rc (Z_to_bv 64 0x2b3e20) Mc MD ECALLW 2097172 TOOM K fetch_26e234 is_ecall_ECALLW eq_refl eq_refl) end.
      + regv HR (17 : reg). reflexivity.
      + regv HR (11 : reg). reflexivity.
      + lia.
      + regv HR (12 : reg). reflexivity.
      + regv HR (13 : reg). reflexivity.
      + regv HR (14 : reg). apply bv_eq. vm_compute. reflexivity.
      + regv HR (15 : reg). reflexivity.
      + (* [comment removed for export] *)
        change (page_round_up_Z 2097172) with 2101248%Z.
        apply grant_exists; [ | | | | apply grant_budget_intro; [reflexivity | reflexivity |]];
          cbv [m_vmmaps HUReadStage.modelG mkModelA m_vm vmst_maps]; rewrite ?Vres, ?Visp, ?Vmaps, ?rsegs_reserved.
        * unfold init_sp_ok. cbv [m_vmmaps HUReadStage.modelG mkModelA m_vm vmst_maps]. rewrite Visp. unfold sp_window_lo. lia.
        * lia.
        * apply Forall_app. split.
          -- repeat constructor; cbn [snd]; rewrite u_small by lia; lia.
          -- constructor; [cbn [snd]; rewrite u_small by lia; lia|]. eapply Forall_impl; [|exact Vsz]. intros [? ?]; cbn [snd]; lia.
        * rewrite length_app. cbn [length]. lia.
        * unfold vm_live_bytes. rewrite Vmaps. cbn [live_bytes]. rewrite u_small by lia. pose proof Vlim as Vlim'. unfold LIM in Vlim'. lia.   (* [comment removed for export] *)
      + (* [comment removed for export] *)
        intros Hmode err Herr. cbn [mmap_errnos In] in Herr. destruct Herr as [<-|[]]. subst E.
        rewrite v_addi_pc4 by lia. change (2833952 + 4)%Z with 0x2b3e24%Z.
        lazymatch type of HR with regs_ok ?E _ _ =>
          pose proof (regs_set_a0 E _ _ (errno_ret ENOMEM) (ELit (- 12)) HR eq_refl) as HR2 end.
        clear HR. rename HR2 into HR.
        save_know HK. run_block_keep scr0 42%nat. note_pres HKb EQM PRES.
        apply (HOOM Hmode). split; [|split; [|split; [|split]]].
        * regv HR (2 : reg). rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev]. rewrite P0. f_equal; lia.
        * regv HR (3 : reg). reflexivity.
        * regv HR (4 : reg). reflexivity.
        * exact PRES.
        * intros d m Hd Hm.
          lazymatch type of HK with know_ok _ ?E ?Mc ?kn =>
            let i := kidx kn (is_kwr_cov (EVar 0) (-8388608)%Z 1%Z) in
            pose proof (kwr_store_ok RSEGS E Mc kn i (EVar 0) (-8388608)%Z 8388608%Z (-8388608 + d)%Z m HK eq_refl ltac:(lia) ltac:(lia)) as ST end.
          unfold adenot, v_addi in ST. cbn [a_base a_off BA LA MBA edenot ev] in ST. rewrite P0 in ST.
          replace (bv_unsigned sp0 - 8388608 + d)%Z with (bv_unsigned sp0 + (-8388608 + d))%Z by lia. exact ST.
      + (* [comment removed for export] *)
        intros B' HG.
        change (page_round_up_Z 2097172) with 2101248%Z in HG |- *.
        rewrite v_addi_pc4 by lia. change (2833952 + 4)%Z with 0x2b3e24%Z.
        pose proof (grant_ok_unpack _ _ _ _ HG) as (GA & GP & GC & GF & GLv).
        unfold alloc_top in GC. cbv [m_vmmaps HUReadStage.modelG mkModelA m_vm vmst_maps] in GC. rewrite Visp in GC. unfold stack_max_size in GC.
        unfold page_size in GA.
        cbv [m_vmmaps HUReadStage.modelG mkModelA m_vm vmst_maps] in GF, GLv. rewrite Vres, Vmaps, rsegs_reserved in GF.
        assert (GB1 : (0x354000 <= bv_unsigned B')%Z).
        { pose proof (region_free_In _ _ _ (Z_to_bv 64 65536) (Z_to_bv 64 856064) GF
                        ltac:(apply in_or_app; left; cbn [In]; tauto)) as X1.
          pose proof (region_free_In _ _ _ (Z_to_bv 64 921600) (Z_to_bv 64 1966080) GF
                        ltac:(apply in_or_app; left; cbn [In]; tauto)) as X2.
          pose proof (region_free_In _ _ _ (Z_to_bv 64 2887680) (Z_to_bv 64 380928) GF
                        ltac:(apply in_or_app; left; cbn [In]; tauto)) as X3.
          pose proof (region_free_In _ _ _ (Z_to_bv 64 3268608) (Z_to_bv 64 221184) GF
                        ltac:(apply in_or_app; left; cbn [In]; tauto)) as X.
          rewrite !u_small in X1 by lia. rewrite !u_small in X2 by lia. rewrite !u_small in X3 by lia.
          rewrite !u_small in X by lia. lia. }
        assert (GB2 : (bv_unsigned B' + 2101248 <= bv_unsigned B \/ bv_unsigned B + 1052672 <= bv_unsigned B')%Z).
        { pose proof (region_free_In _ _ _ B (Z_to_bv 64 1052672) GF
                        ltac:(apply in_or_app; right; left; reflexivity)) as X.
          rewrite !u_small in X by lia. lia. }
        assert (GB3 : (bv_unsigned B' + 2101248 <= bv_unsigned mb + 4096 \/ bv_unsigned mb + 8192 <= bv_unsigned B')%Z).
        { destruct Vcont as ([cb cs] & Cin & C1 & C2). cbn [fst snd] in C1, C2.
          pose proof (region_free_In _ _ _ cb cs GF ltac:(apply in_or_app; right; right; exact Cin)) as X.
          rewrite !u_small in X by lia. lia. }
        (* [comment removed for export] *)
        lazymatch type of HR with regs_ok _ ?sr ?Rc =>
          pose proof (env_app_regs vals [B'] _ sr Rc ltac:(rewrite HL; vm_compute; reflexivity) HR) as HR2 end.
        lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
          pose proof (env_app_know RSEGS vals [B'] _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2 end.
        clear HR HK. subst E.
        assert (P42 : vals_ev (vals ++ [B']) 42 = B') by (rewrite <- HL; apply vals_ev_last).
        grow_vals HL [B'] 43%nat.
        set (E := Env (vals_ev vals) (gblobs content)) in *.
        assert (AD42 : adenot E (SA (EVar 42) 0) = B').
        { unfold adenot, v_addi. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P42. apply bv_eq. rewrite u_small by lia. lia. }
        pose proof (regs_set_a0 E _ _ B' (EVar 42) HR2 ltac:(cbn [edenot ev]; subst E; exact P42)) as HR. clear HR2.
        assert (KA42 : kentry_ok RSEGS E M1 (KAlign (EVar 42) 4096)).
        { apply kalign_intro; [lia|]. cbn [edenot ev]. subst E. cbn [ev]. rewrite P42. exact GA. }
        assert (KR42 : kentry_ok RSEGS E M1 (KRange (EVar 42) 0x354000 (CEIL - 2101248))).
        { apply krange_intro. cbn [edenot ev]. subst E. cbn [ev]. rewrite P42. unfold CEIL. lia. }
        assert (KD42a : kentry_ok RSEGS E M1 (KDisj (SA (EVar 42) 0) 2101248 (SA (EVar 5) 0) 1052672)).
        { cbn [kentry_ok]. unfold estart. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P42, P5. lia. }
        assert (KD42b : kentry_ok RSEGS E M1 (KDisj (SA (EVar 42) 0) 2101248 (SA (EVar 2) 4096) 4096)).
        { cbn [kentry_ok]. unfold estart. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P42, P2. lia. }
        assert (KD42s : kentry_ok RSEGS E M1 (KDisj (SA (EVar 0) (-8388608)) HUGE (SA (EVar 42) 0) 2101248)).
        { cbn [kentry_ok]. unfold estart, HUGE. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P42, P0. lia. }
        pose proof (know_ok_cons _ _ _ _ _ KA42 (know_ok_cons _ _ _ _ _ KR42
                     (know_ok_cons _ _ _ _ _ KD42s (know_ok_cons _ _ _ _ _ KD42a (know_ok_cons _ _ _ _ _ KD42b HK2))))) as HK2'.
        clear KA42 KR42 KD42a KD42b KD42s HK2.
        lazymatch type of HK2' with know_ok _ _ ?Mc ?kn =>
          pose proof (know_ok_zfill RSEGS E Mc kn (EVar 42) 0 2101248 HK2'
                        ltac:(apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P42; lia) ltac:(lia) ltac:(lia)) as HK3 end.
        rewrite AD42 in HK3. clear HK2'.
        assert (KW42 : kentry_ok RSEGS E (zfill B' (Z_to_bv 64 2101248) M1) (KWr (SA (EVar 42) 0) 2101248)).
        { cbn [kentry_ok]. split; [apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P42; lia|].
          intros d m Hd Hm. unfold estart. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P42.
          unfold zfill. apply store_ok_zmem; rewrite ?u_small by lia; lia. }
        pose proof (know_ok_cons _ _ _ _ _ KW42 HK3) as HK. clear KW42 HK3.
        norm_know HK.
        assert (PRES2 : pres M0 (zfill B' (Z_to_bv 64 2101248) M1) sp0).
        { eapply pres_trans; [exact PRES|]. eapply (pres_far _ _ sp0 (bv_unsigned B') 2101248); [lia | lia | lia |].
          intros x Hx. apply zfill_outside. rewrite u_small by lia. exact Hx. }
        clear PRES. rename PRES2 into PRES.
        (* [comment removed for export] *)
        save_know HK. gg_block_keep scrT 43%nat.
        { apply xor_m1_ne0. cbn [edenot ev]. subst E. cbn [ev]. rewrite P42. lia. }
        note_pres HKb EQM PRES.
        (* [comment removed for export] *)
        assert (Hflat2 : forall k n, (0 <= k)%Z -> (0 <= n)%Z -> (k + n <= 8192)%Z -> flat E (SA (EVar 2) k) n).
        { intros k n Hk Hn Hkn. apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P2; lia. }
        krdv HK 2%nat 4176%Z 8%nat RM0. { apply Hflat2; lia. }
        krdv HK 2%nat 4192%Z 8%nat RW0. { apply Hflat2; lia. }
        unfold adenot, v_addi in RM0, RW0. cbn [a_base a_off BA LA MBA edenot ev] in RM0, RW0. subst E. cbn [ev] in RM0, RW0.
        rewrite P2 in RM0, RW0. rewrite P42 in RM0.
        set (E := Env (vals_ev vals) (gblobs content)) in *.
        kzero_at HK (EVar 42) 12%Z Z12. kzero_at HK (EVar 42) 13%Z Z13.
        cbn [edenot ev] in Z12, Z13. subst E. cbn [ev] in Z12, Z13. rewrite P42 in Z12, Z13.
        set (E := Env (vals_ev vals) (gblobs content)) in *.
        lazymatch goal with |- GG _ _ _ _ (mkCfg (mkst ?Rc _ ?Mc _) _) =>
        assert (EF : efH Mc (Z_to_bv 64 6) (bv_unsigned mb + 4160) (bv_unsigned B') 2105312 0 2097152 0 0 2101232 (bv_unsigned B' + 16) 6) end.
        { constructor.
          - vm_compute. reflexivity.
          - unfold slot_start, UNIT. lia.
          - vm_compute. reflexivity.
          - lia.
          - lia.
          - lia.
          - lia.
          - lia.
          - intros HH. exfalso. destruct HH as [HH|HH]; revert HH; vm_compute; congruence.
          - lia.
          - lia.
          - lia.
          - lia.
          - lia.
          - lia.
          - replace (bv_unsigned mb + 4160 + 16)%Z with (bv_unsigned mb + 4176)%Z by lia. rewrite RM0. f_equal. f_equal. apply bv_eq. rewrite u_small by lia. reflexivity.
          - replace (bv_unsigned mb + 4160 + 32)%Z with (bv_unsigned mb + 4192)%Z by lia. exact RW0.
          - replace (bv_unsigned B' + 16 - 4)%Z with (bv_unsigned B' + 12)%Z by lia. exact Z12.
          - replace (bv_unsigned B' + 16 - 3)%Z with (bv_unsigned B' + 13)%Z by lia. exact Z13.
          - intros HH. exfalso. apply HH. reflexivity.
          - replace (Z_to_bv 64 (bv_unsigned B' + 16 - 3)) with (adenot E (SA (EVar 42) 13))
              by (unfold adenot, v_addi; cbn [a_base a_off BA LA MBA edenot ev]; subst E; cbn [ev]; rewrite P42; f_equal; lia).
            kwr_solve HK.
          - intros jj Hj. unfold SCT.
            lazymatch type of HK with know_ok _ _ _ ?kn =>
              eapply (kimg_none RSEGS E _ kn ltac:(let i := kidx kn (is_kimg_cov 0x72234 96) in exact i) _ _ HK eq_refl) end. lia. }
        assert (RT : Hoare.ret_ok (Z_to_bv 64 0xe1a3c)) by (apply bv_eq; vm_compute; reflexivity).
        lazymatch goal with |- GG _ _ _ _ (mkCfg (mkst ?Rc _ ?Mc _) _) =>
          assert (G1 : getr Rc 1 = Z_to_bv 64 0xe1a3c) by (regv HR (1:reg); reflexivity);
          assert (G10 : getr Rc 10 = Z_to_bv 64 (bv_unsigned mb + 4160))
            by (regv HR (10:reg); rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off BA LA MBA edenot ev]; subst E; cbn [ev]; rewrite P2; reflexivity);
          assert (G11 : getr Rc 11 = Z_to_bv 64 0) by (regv HR (11:reg); reflexivity);
          assert (G12 : getr Rc 12 = Z_to_bv 64 2097152) by (regv HR (12:reg); reflexivity);
          assert (G13 : getr Rc 13 = Z_to_bv 64 6) by (regv HR (13:reg); reflexivity);
          destruct (ref_enframe Rc Mc (seg_rom RSEGS) (Z_to_bv 64 0xe1a3c) (Z_to_bv 64 6) _ _ _ _ _ _ _ _ _ _ EF G1 RT G10 G11 G12 G13)
            as (R3 & M3 & RUN & KEEP & A0 & FR & POST);
          clear RT G1 G10 G11 G12 G13 EF RM0 RW0 Z12 Z13 end.
        replace (Z_to_bv 64 2830836) with (0x2b31f4 : word) by (apply bv_eq; vm_compute; reflexivity).
        eapply gg_msteps; [reflexivity | reflexivity | exact RUN |]. clear RUN.
        lazymatch type of HR with regs_ok _ ?sr _ =>
          pose proof (regs_after_keeps vals _ sr _ R3 callee_saved ltac:(rewrite HL; vm_compute; reflexivity) HR KEEP callee_saved_no0) as HR3 end.
        rewrite HL in HR3. clear HR KEEP.
        lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
          pose proof (env_app_know RSEGS vals (junk_vals R3) _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2 end.
        clear HK Hflat2 AD42. subst E.
        grow_vals HL (junk_vals R3) 75%nat.
        set (E := Env (vals_ev vals) (gblobs content)) in *.
        lazymatch type of HR3 with regs_ok _ ?sr _ =>
          assert (HR : regs_ok E (sr_upd sr (ridx 10) (EAlu ALU_ADD (EVar 42) (ELit 112))) R3) end.
        { apply regs_ok_pin; [exact HR3|]. rewrite A0, edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off BA LA MBA edenot ev].
          subst E. cbn [ev]. rewrite P42. f_equal. lia. }
        clear HR3 A0. norm_regs HR.
        destruct FR as [FRo FRg].
        assert (OUT3 : forall x : word, (bv_unsigned x < estart E (SA (EVar 42) 13) \/ estart E (SA (EVar 42) 13) + 2101231 <= bv_unsigned x)%Z -> M3 x = M2 x).
        { intros x Hx. apply FRo. cbn [outside]. split; [|exact I]. unfold in_rng. rewrite u_small by lia.
          unfold estart in Hx. cbn [a_base a_off BA LA MBA edenot ev] in Hx. subst E. cbn [ev] in Hx. rewrite P42 in Hx. lia. }
        lazymatch type of HK2 with know_ok _ _ _ ?kn =>
          pose proof (know_ok_frame RSEGS E M2 M3 kn (EVar 42) 13 2101231 HK2
                        ltac:(apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P42; lia) OUT3 FRg) as HK4 end.
        clear HK2 OUT3.
        destruct POST as [Pp Pe Pr Pq Pm4 Pm3 Pm2 Pzr Pe5 Pe4 Ps3 Ps2 Prr]. cbn zeta in *. subst Pp Pe Pr Pq.
        specialize (Pzr ltac:(lia)). specialize (Pe5 ltac:(lia)). specialize (Pe4 ltac:(lia)).
        specialize (Ps3 ltac:(lia)). specialize (Ps2 ltac:(lia)).
        replace (0 + 32 * res_code (2101232 - 4 - 2097152 - 16 * 6))%Z with 160%Z in Pm3 by (vm_compute; reflexivity).
        replace (2101232 * 0 / 16 + 6)%Z with 6%Z in Pm2 by (vm_compute; reflexivity).
        replace (2101232 - 4 - 2097152 - 16 * 6)%Z with 3980%Z in Pe4 by reflexivity.
        assert (EV42 : edenot E (EVar 42) = B') by (cbn [edenot ev]; subst E; cbn [ev]; exact P42).
        assert (K1 : kentry_ok RSEGS E M3 (KWord (SA (EVar 42) 108) 1 (ELit 0))) by (hdr_byte EV42 Pm4 108%Z).
        assert (K2 : kentry_ok RSEGS E M3 (KWord (SA (EVar 42) 109) 1 (ELit 160))) by (hdr_byte EV42 Pm3 109%Z).
        assert (K3 : kentry_ok RSEGS E M3 (KWord (SA (EVar 42) 110) 2 (ELit 6))) by (hdr_word EV42 Pm2 110%Z 2%nat 6%Z).
        assert (K4 : kentry_ok RSEGS E M3 (KWord (SA (EVar 42) 2097264) 1 (ELit 0))) by (hdr_byte EV42 Pzr 2097264%Z).
        assert (K5 : kentry_ok RSEGS E M3 (KWord (SA (EVar 42) 2101239) 1 (ELit 0))) by (hdr_byte EV42 Pe5 2101239%Z).
        assert (K6 : kentry_ok RSEGS E M3 (KWord (SA (EVar 42) 2101240) 4 (ELit 3980))) by (hdr_word EV42 Pe4 2101240%Z 4%nat 3980%Z).
        assert (K7 : kentry_ok RSEGS E M3 (KWord (SA (EVar 42) 13) 1 (ELit 224))) by (hdr_byte EV42 Ps3 13%Z).
        assert (K8 : kentry_ok RSEGS E M3 (KWord (SA (EVar 42) 14) 2 (ELit 6))) by (hdr_word EV42 Ps2 14%Z 2%nat 6%Z).
        pose proof (know_ok_cons _ _ _ _ _ K1 (know_ok_cons _ _ _ _ _ K2 (know_ok_cons _ _ _ _ _ K3 (know_ok_cons _ _ _ _ _ K4
          (know_ok_cons _ _ _ _ _ K5 (know_ok_cons _ _ _ _ _ K6 (know_ok_cons _ _ _ _ _ K7 (know_ok_cons _ _ _ _ _ K8 HK4)))))))) as HK.
        clear K1 K2 K3 K4 K5 K6 K7 K8 HK4 Pm4 Pm3 Pm2 Pzr Pe5 Pe4 Ps3 Ps2 Prr.
        norm_know HK.
        assert (PRES2 : pres M0 M3 sp0).
        { eapply pres_trans; [exact PRES|]. eapply (pres_far _ _ sp0 (bv_unsigned B' + 13) 2101231); [lia | lia | lia |].
          intros x Hx. apply FRo. cbn [outside]. split; [|exact I]. unfold in_rng. rewrite u_small by lia. lia. }
        clear PRES FRo FRg. rename PRES2 into PRES.
        (* [comment removed for export] *)
        save_know HK. gg_block_keep scr0 75%nat. note_pres HKb EQM PRES.
        (* [comment removed for export] *)
        assert (Hflat5 : forall k n, (0 <= k)%Z -> (0 <= n)%Z -> (k + n <= 1052672)%Z -> flat E (SA (EVar 5) k) n).
        { intros k n Hk Hn Hkn. apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P5; lia. }
        lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
          pose proof (kblob_rdn RSEGS E Mc kn (EVar 5) 96 (ELit 524288) 6%nat HK ltac:(vm_compute; reflexivity)) as SRC1;
          pose proof (kblob_rdn RSEGS E Mc kn (EVar 5) 524384 (ELit 524288) 7%nat HK ltac:(vm_compute; reflexivity)) as SRC2 end.
        change (eb E 6%nat) with (gblobs content 6%nat) in SRC1. rewrite (gblobs_hb 4) in SRC1 by lia. change (held_of 4) with 524288%Z in SRC1.
        change (eb E 7%nat) with (gblobs content 7%nat) in SRC2. rewrite EBc in SRC2.
        assert (RLh : length (pref 524288 content) = Z.to_nat 524288) by (pose proof (pref_length 524288 content ltac:(lia)); lia).
        assert (SRC : rdn RSEGS M4 (adenot E (SA (EVar 5) 96)) (length (pref 1048576 content)) = Some (pref 1048576 content)).
        { replace (pref 1048576 content) with (pref 524288 content ++ pref 524288 (dropz 524288 content))
            by (rewrite pref_app by lia; reflexivity).
          rewrite length_app, RLh, RL1. apply SeqExec.rdn_app.
          - rewrite RLh in SRC1. exact SRC1.
          - rewrite RL1 in SRC2. replace (adenot E (SA (EVar 5) 96) + nat_to_word (Z.to_nat 524288)) with (adenot E (SA (EVar 5) 524384)); [exact SRC2|].
            unfold adenot, v_addi, nat_to_word. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P5. apply bv_eq.
            rewrite bv_add_unsigned. rewrite Z2Nat.id by lia. rewrite !u_small by lia. rewrite bv_wrap_small; [lia|]. unfold bv_modulus. lia. }
        clear SRC1 SRC2.
        assert (RLc : length (pref 1048576 content) = Z.to_nat 1048576) by (pose proof (pref_length 1048576 content ltac:(lia)); lia).
        assert (EBf : gblobs content 8%nat = pref 1048576 content) by (rewrite <- (gblobs_fb 4) by lia; reflexivity).
        set (dst := adenot E (SA (EVar 42) 112)). set (src := adenot E (SA (EVar 5) 96)) in SRC.
        assert (Hudst : bv_unsigned dst = (bv_unsigned B' + 112)%Z).
        { subst dst. unfold adenot, v_addi. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P42, u_small by lia. lia. }
        assert (Husrc : bv_unsigned src = (bv_unsigned B + 96)%Z).
        { subst src. unfold adenot, v_addi. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P5, u_small by lia. lia. }
        lazymatch goal with |- GG _ _ _ _ (mkCfg (mkst ?Rc _ ?Mc _) _) =>
          assert (MC : mcH Mc dst src 1048576 (pref 1048576 content)) end.
        { constructor.
          - lia.
          - exact RLc.
          - exact SRC.
          - subst dst. rewrite RLc. kwr_solve HK.
          - lia.
          - lia.
          - lia. }
        assert (RT : Hoare.ret_ok (Z_to_bv 64 0xe1a5c)) by (apply bv_eq; vm_compute; reflexivity).
        lazymatch goal with |- GG _ _ _ _ (mkCfg (mkst ?Rc _ ?Mc _) _) =>
          assert (G1 : getr Rc 1 = Z_to_bv 64 0xe1a5c) by (regv HR (1:reg); reflexivity);
          assert (G10 : getr Rc 10 = dst) by (regv HR (10:reg); subst dst; apply edenot_add_lit);
          assert (G11 : getr Rc 11 = src) by (regv HR (11:reg); subst src; unfold bx; apply edenot_add_lit);
          assert (G12 : getr Rc 12 = Z_to_bv 64 1048576) by (regv HR (12:reg); reflexivity);
          destruct (ref_memcpy Mc dst src 1048576 _ (seg_rom RSEGS) MC Rc (Z_to_bv 64 0xe1a5c) RT G1 G10 G11 G12) as (R5 & RUN & KEEP);
          clear RT G1 G10 G11 G12 MC SRC end.
        replace (Z_to_bv 64 2867236) with (0x2bc024 : word) by (apply bv_eq; vm_compute; reflexivity).
        eapply gg_msteps; [reflexivity | reflexivity | exact RUN |]. clear RUN.
        lazymatch type of HR with regs_ok _ ?sr _ =>
          pose proof (regs_after_keeps vals _ sr _ R5 callee_kept ltac:(rewrite HL; vm_compute; reflexivity) HR KEEP callee_kept_no0) as HR5 end.
        rewrite HL in HR5. clear HR KEEP.
        lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
          pose proof (know_ok_wblob RSEGS E Mc kn (EVar 42) 112 8%nat (pref 1048576 content) HK
                        ltac:(apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P42, ?RLc; lia)
                        EBf ltac:(rewrite RLc; lia) ltac:(rewrite RLc; lia)) as HK2 end.
        fold dst in HK2. rewrite RLc, Z2Nat.id in HK2 by lia.
        assert (Hdst : dst = Z_to_bv 64 (bv_unsigned B' + 112)) by (apply bv_eq; rewrite Hudst, u_small by lia; reflexivity).
        rewrite Hdst in HK2 |- *.
        assert (PRES2 : pres M0 (wbytes M4 (Z_to_bv 64 (bv_unsigned B' + 112)) (pref 1048576 content)) sp0).
        { eapply pres_trans; [exact PRES|]. eapply (pres_far _ _ sp0 (bv_unsigned B' + 112) 1048576); [lia | lia | lia |].
          intros x Hx. apply MemSplit.wbytes_outside; rewrite u_small, RLc by lia; lia. }
        clear PRES HK. rename PRES2 into PRES.
        lazymatch type of HK2 with know_ok _ _ ?Mc ?kn =>
          pose proof (env_app_know RSEGS vals (junk_vals R5) _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK end.
        clear HK2. subst src E. clear dst Hdst Hudst Husrc EV42 Hflat5.
        grow_vals HL (junk_vals R5) 107%nat.
        set (E := Env (vals_ev vals) (gblobs content)) in *. rename HR5 into HR.
        norm_regs HR. norm_know HK.
        (* [comment removed for export] *)
        save_know HK. gg_block_keep scr0 107%nat. note_pres HKb EQM PRES.
        (* [comment removed for export] *)
        assert (Hflat5 : forall k n, (0 <= k)%Z -> (0 <= n)%Z -> (k + n <= 1052672)%Z -> flat E (SA (EVar 5) k) n).
        { intros k n Hk Hn Hkn. apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P5; lia. }
        assert (Hflat2 : forall k n, (0 <= k)%Z -> (0 <= n)%Z -> (k + n <= 8192)%Z -> flat E (SA (EVar 2) k) n).
        { intros k n Hk Hn Hkn. apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P2; lia. }
        krdv HK 5%nat 92%Z 1%nat Gb4. { apply Hflat5; lia. }
        krdv HK 5%nat 93%Z 1%nat Gb3. { apply Hflat5; lia. }
        krdv HK 5%nat 94%Z 2%nat Goff. { apply Hflat5; lia. }
        krdv HK 5%nat 0%Z 8%nat Gmeta. { apply Hflat5; lia. }
        krdv HK 2%nat 4136%Z 8%nat Gmem. { apply Hflat2; lia. }
        krdv HK 2%nat 4152%Z 8%nat GW. { apply Hflat2; lia. }
        krdv HK 2%nat 4144%Z 4%nat Gav. { apply Hflat2; lia. }
        krdv HK 2%nat 4148%Z 4%nat Gfr. { apply Hflat2; lia. }
        krdv HK 2%nat 4096%Z 8%nat Garea. { apply Hflat2; lia. }
        krd HK 0x351df0%Z 8%nat Gsec.
        unfold adenot, v_addi in Gb4, Gb3, Goff, Gmeta, Gmem, GW, Gav, Gfr, Garea.
        cbn [a_base a_off BA LA MBA edenot ev] in Gb4, Gb3, Goff, Gmeta, Gmem, GW, Gav, Gfr, Garea. subst E.
        cbn [ev] in Gb4, Gb3, Goff, Gmeta, Gmem, GW, Gav, Gfr, Garea.
        rewrite P5 in Gb4, Gb3, Goff, Gmeta, Gmem. rewrite P2 in Gmeta, Gmem, GW, Gav, Gfr, Garea.
        cbn [ev] in Gsec. rewrite ?P8 in Garea. rewrite ?P8 in Gsec.
        unfold mbx in Gmeta. rewrite alu_add in Gmeta. unfold v_add in Gmeta.
        set (E := Env (vals_ev vals) (gblobs content)) in *.
        lazymatch goal with |- GG _ _ _ _ (mkCfg (mkst ?Rc _ ?Mc _) _) =>
          assert (GMR : gm_reads Mc (bv_unsigned B + 96) (bv_unsigned B) (bv_unsigned mb + 4120) 0 5 5 1056736 0 0 sec) end.
        { constructor.
          - apply rdn1_mem_high; [rewrite u_small by lia; lia|]. replace (bv_unsigned B + 96 - 4)%Z with (bv_unsigned B + 92)%Z by lia. exact Gb4.
          - apply rdn1_mem_high; [rewrite u_small by lia; lia|]. replace (bv_unsigned B + 96 - 3)%Z with (bv_unsigned B + 93)%Z by lia. exact Gb3.
          - replace (bv_unsigned B + 96 - 2)%Z with (bv_unsigned B + 94)%Z by lia. exact Goff.
          - rewrite Z.add_0_r in Gmeta. change (bv_unsigned (Z_to_bv 64 4120)) with 4120%Z in Gmeta. exact Gmeta.
          - replace (bv_unsigned mb + 4120 + 16)%Z with (bv_unsigned mb + 4136)%Z by lia. rewrite Gmem. f_equal. f_equal. symmetry. apply Z_to_bv_bv_unsigned.
          - replace (bv_unsigned mb + 4120 + 32)%Z with (bv_unsigned mb + 4152)%Z by lia. exact GW.
          - replace (bv_unsigned mb + 4120 + 24)%Z with (bv_unsigned mb + 4144)%Z by lia. exact Gav.
          - replace (bv_unsigned mb + 4120 + 28)%Z with (bv_unsigned mb + 4148)%Z by lia. exact Gfr.
          - assert (HM24 : ((bv_unsigned mb + 4120) mod 4096 = 24)%Z)
              by (rewrite <- Zplus_mod_idemp_l, Hmba; reflexivity).
            rewrite HM24. replace (bv_unsigned mb + 4120 - 24)%Z with (bv_unsigned mb + 4096)%Z by lia. exact Garea.
          - exact Gsec.
          - intros i Hi. lazymatch type of HK with know_ok _ _ _ ?kn =>
              eapply (kimg_none RSEGS E _ kn ltac:(let jj := kidx kn (is_kimg_cov 0x72234 96) in exact jj) _ _ HK eq_refl) end. lia. }
        assert (GMP : gm_pure (bv_unsigned B + 96) (bv_unsigned B) (bv_unsigned mb + 4120) 0 5 5 1056736 0 0).
        { constructor.
          all: try (change (w_lastidx 1056736) with 0%Z); try (change (w_sizeclass 1056736) with 63%Z);
               try (change (w_maplen 1056736) with 257%Z).
          1: { rewrite <- Zplus_mod_idemp_l.
               replace (bv_unsigned B mod 16)%Z with 0%Z; [reflexivity|].
               symmetry. apply Znumtheory.Zdivide_mod. apply (Z.divide_trans _ 4096); [exists 256%Z; reflexivity|].
               apply Znumtheory.Zmod_divide; [lia | exact KBal]. }
          all: try lia.
          all: reflexivity. }
        clear Gb4 Gb3 Goff Gmeta Gmem GW Gav Gfr Garea Gsec Hflat2 Hflat5.
        assert (RT : Hoare.ret_ok (Z_to_bv 64 0x2b1c78)) by (apply bv_eq; vm_compute; reflexivity).
        lazymatch goal with |- GG _ _ _ _ (mkCfg (mkst ?Rc _ ?Mc _) _) =>
          assert (G10 : getr Rc 10 = Z_to_bv 64 (bv_unsigned B + 96))
            by (regv HR (10:reg); unfold bx; rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off BA LA MBA edenot ev]; subst E; cbn [ev]; rewrite P5; reflexivity);
          assert (G1 : getr Rc 1 = Z_to_bv 64 0x2b1c78) by (regv HR (1:reg); reflexivity);
          destruct (get_meta_run Rc Mc (seg_rom RSEGS) (Z_to_bv 64 0x2b1c78) _ _ _ _ _ _ _ _ _ _ GMR GMP G10 G1 RT) as (R7 & RUN & A0 & A1 & KEEP);
          clear RT G1 G10 GMR GMP end.
        replace (Z_to_bv 64 2825760) with (0x2b1e20 : word) by (apply bv_eq; vm_compute; reflexivity).
        eapply gg_msteps; [reflexivity | reflexivity | exact RUN |]. clear RUN.
        lazymatch type of HR with regs_ok _ ?sr _ =>
          pose proof (regs_after_keeps vals _ sr _ R7 gm_kept ltac:(rewrite HL; vm_compute; reflexivity) HR (gm_keeps_kept _ _ KEEP) gm_kept_no0) as HR7 end.
        rewrite HL in HR7. clear HR KEEP.
        lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
          pose proof (env_app_know RSEGS vals (junk_vals R7) _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2 end.
        clear HK. subst E.
        grow_vals HL (junk_vals R7) 139%nat.
        set (E := Env (vals_ev vals) (gblobs content)) in *. rename HK2 into HK.
        lazymatch type of HR7 with regs_ok _ ?sr _ =>
          assert (HR : regs_ok E (sr_upd (sr_upd sr (ridx 10) (mbx 4120)) (ridx 11) (ELit 5)) R7) end.
        { apply regs_ok_pin; [apply regs_ok_pin; [exact HR7|]|].
          - rewrite A0. unfold mbx. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P2. reflexivity.
          - rewrite A1. reflexivity. }
        clear HR7 A0 A1. norm_regs HR. norm_know HK.
        (* [comment removed for export] *)
        save_know HK. gg_block_keep scr0 139%nat. note_pres HKb EQM PRES.
        (* [comment removed for export] *)
        lazymatch goal with |- GG _ _ _ _ (mkCfg (mkst ?Rc _ ?Mc _) ?MD) =>
          eapply (gg_munmap RSEGS mode Q Rc (Z_to_bv 64 0x2b3f8c) Mc MD ECALLW B 1052672 K fetch_26e3a0 is_ecall_ECALLW eq_refl eq_refl) end.
        * regv HR (17:reg). reflexivity.
        * regv HR (10:reg). cbn [edenot ev]. subst E. cbn [ev]. exact P5.
        * unfold page_size. exact KBal.
        * regv HR (11:reg). reflexivity.
        * lia.
        * change (page_round_up_Z 1052672) with 1052672%Z. unfold TASK_SIZE. lia.
        * change (page_round_up_Z 1052672) with 1052672%Z. cbv [m_vmmaps mmap_model with_vmmaps HUReadStage.modelG mkModelA m_vm vmst_maps]. cbn [vm_maps]. rewrite Vmaps. apply map_has_cons. apply map_has_head.
        * change (page_round_up_Z 1052672) with 1052672%Z.
          rewrite v_addi_pc4 by lia. change (0x2b3f8c + 4)%Z with 0x2b3f90%Z.
          lazymatch type of HR with regs_ok ?E _ _ =>
            pose proof (regs_set_a0 E _ _ (Z_to_bv 64 0) (ELit 0) HR eq_refl) as HR2 end.
          clear HR. rename HR2 into HR.
          assert (AD5 : adenot E (SA (EVar 5) 0) = B).
          { unfold adenot, v_addi. cbn [a_base a_off BA LA MBA edenot ev]. subst E. cbn [ev]. rewrite P5. apply bv_eq. rewrite u_small by lia. lia. }
          lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
            pose proof (know_ok_unfill RSEGS E Mc kn (EVar 5) 0 1052672 HK
                          ltac:(apply flat_intro; cbn [edenot ev]; subst E; cbn [ev]; rewrite ?P5; lia) ltac:(lia)) as HK2 end.
          rewrite AD5 in HK2. clear HK AD5. rename HK2 into HK. norm_know HK.
          lazymatch goal with |- GG _ _ _ _ (mkCfg (mkst _ _ ?Mc _) _) =>
            assert (PRES2 : pres M0 Mc sp0) end.
          { eapply pres_trans; [exact PRES|]. eapply (pres_far _ _ sp0 (bv_unsigned B) 1052672); [lia | lia | lia |].
            intros x Hx. apply unfill_outside. rewrite u_small by lia. exact Hx. }
          clear PRES. rename PRES2 into PRES.
          (* [comment removed for export] *)
          save_know HK. gg_block_keep scr0 139%nat. note_pres HKb EQM PRES.
          (* [comment removed for export] *)
          rewrite munmap_model_simple by reflexivity.
          unfold mmap_model, with_vmmaps.
          cbv [m_vmmaps m_fd m_io m_fsys m_proc m_lim m_time m_vm m_vm_lazy m_vm_materialized vmst_maps vmst_lazy vmst_materialized
               HUReadStage.modelG mkModelA]. cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk vm_limit vm_mmap_base vm_init_sp].
          lazymatch goal with |- GG _ _ _ _ (mkCfg (mkst ?Rc _ ?Mc _) (mkModelOf _ (mkVmState ?V' _ _) _ _ _ _ _)) =>
            change (GG RSEGS mode Q K (mkCfg (mkst Rc (Z_to_bv 64 0xe1a68) Mc (seg_rom RSEGS)) (modelG (held_of 5) V'))) end.
          unfold half_branch in HK1. apply (HK1 _ _ _ B' (edenot E (EExt true 0 4 (EVar 6)))).
          lazymatch type of HR with regs_ok _ ?srf _ =>
          lazymatch type of HK with know_ok _ _ ?Mf ?knf =>
            set (rvl := [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 42; EExt true 0 4 (EVar 6); EVar 7; EVar 8; ELit 0] ++ srf);
            assert (XB : forall k, gblobs content k = eb E ((fun k : nat => k) k)) by (intros; reflexivity);
            split; [ exists (map (edenot E) srf); split; [rewrite length_map; reflexivity|];
                     replace (ENV_RD sp0 p1 mb bw gm L B' (edenot E (EExt true 0 4 (EVar 6))) can sec (map (edenot E) srf) content)
                        with (xenv E rvl (gblobs content));
                     [ split; [ apply (regs_ok_xfer E rvl (fun k => k) _ XB srf (sr_HALF 5) _ HR); [reflexivity | reflexivity |]
                              | apply (know_ok_xfer_entails RSEGS E rvl (fun k => k) _ Mf knf (kn_HALF 5) XB HK) ]
                     | ]
                   | split; [exact PRES |] ]
          end end.
          -- intros i Hi Hne. exfalso. apply Hne. vm_compute in Hi. cbv [In] in Hi. destruct Hi as [<-|[]]. reflexivity.
          -- match goal with |- Forall _ ?l => replace l with (@nil kentry) by (vm_compute; reflexivity) end. constructor.
          -- unfold ENV_RD, xenv, vals_RD. f_equal. subst rvl. rewrite map_app. cbn [map app].
             cbn [edenot ev]. subst E. cbn [ev]. rewrite P0, P1, P2, P3, P4, P42, P7, P8. reflexivity.
          -- (* [comment removed for export] *)
             unfold vm_stage. cbn [vm_reserved vm_limit vm_maps vm_init_sp]. split; [exact Vres|]. split; [exact Vlim|]. split; [exact Visp|].
             rewrite Vmaps.
             assert (Hbb : B' <> B) by (intros HH; rewrite HH in GB2; lia).
             exists (map_remove rest B). split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
             ++ change (nb_of 5) with 2101248%Z. rewrite map_remove_skip by exact Hbb. rewrite map_remove_head. reflexivity.
             ++ apply incl_Forall with (l1 := rest); [|exact Vsz]. unfold map_remove. apply incl_filter.
             ++ pose proof (map_remove_length rest B). lia.
             ++ pose proof (live_bytes_map_remove_le rest B). lia.
             ++ destruct Vcont as (pc & Cin & C1 & C2). exists pc. split; [|split; assumption].
                unfold map_remove. apply filter_In. split; [exact Cin|]. destruct pc as [cb cs]. cbn [fst snd] in C1, C2 |- *.
                apply Bool.negb_true_iff. unfold bv_eqb. apply Z.eqb_neq. intros HH.
                pose proof (proj1 (Forall_forall _ _) Vdisj _ Cin) as X. cbn [fst snd] in X.
                pose proof (proj1 (Forall_forall _ _) Vsz _ Cin) as Y. cbn [snd] in Y. lia.
             ++ apply Forall_forall. intros [qb qs] Hq. cbn [fst snd]. change (nb_of 5) with 2101248%Z.
                unfold map_remove in Hq. apply filter_In in Hq as [Hq _].
                pose proof (region_free_In _ _ _ qb qs GF ltac:(apply in_or_app; right; right; exact Hq)) as X.
                rewrite u_small in X by lia. lia.
             ++ unfold map_remove. apply seps_filter. exact Vseps.
             ++ split. { (* [comment removed for export] *)
                apply (HUTargetPre.vm_ledger_frame mb bw V); [exact Vlg | |].
                ** intros Hin. rewrite Vmaps in Hin. destruct Hin as [EE | Hin].
                   { exfalso. apply (f_equal snd) in EE. cbn [snd] in EE. apply (f_equal bv_unsigned) in EE. rewrite !u_small in EE by lia. lia. }
                   apply HUTargetPre.In_map_remove_keep; [right; right; exact Hin | cbn [fst]].
                   intros HH. pose proof (proj1 (Forall_forall _ _) Vdisj _ Hin) as X. cbn [fst snd] in X. rewrite HH, u_small in X by lia. lia.
                ** intros Hin Hcov. rewrite Vmaps in Hin. destruct Hin as [EE | Hin].
                   { exfalso. apply (f_equal snd) in EE. cbn [snd] in EE. apply (f_equal bv_unsigned) in EE. rewrite !u_small in EE by lia. lia. }
                   pose proof (proj1 (Forall_forall _ _) Vdisj _ Hin) as X. cbn [fst snd] in X. rewrite u_small in X by lia.
                   rewrite u_small by lia. apply HUTargetPre.maps_subtract_keep_cover; [lia | lia | lia | exact Hcov | lia]. }
                (* [comment removed for export] *)
                apply (vm_exact_grow V _ sp0 mb bw B B' _ _ Vex);
                  [vm_compute; split; reflexivity | vm_compute; split; reflexivity | cbn [vm_maps]; rewrite Vmaps; reflexivity | reflexivity
                  | reflexivity | reflexivity | exact GA | exact GP | match goal with |- (_ + ?n <= _)%Z => let n' := eval vm_compute in n in change n with n' end; lia
                  | rewrite rsegs_reserved, Vmaps; exact GF].
  Qed.
End G.
